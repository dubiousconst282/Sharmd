namespace Sharpmd.Compiler;

using System.Diagnostics;

using DistIL.Analysis;
using DistIL.AsmIO;
using DistIL.IR;
using DistIL.IR.Utils;
using DistIL.Passes;

class VectorizingIRCloner : IRCloner {
    readonly VectorWideningPass _pass;
    readonly MethodBody _srcMethod;
    readonly UniformValueAnalysis _uniformity;
    readonly IRBuilder _builder;
    readonly Dictionary<BasicBlock, VectorIntrinsic.ExecMask> _blockMasks = new();

    Value? _currExecMask = null;

    public VectorizingIRCloner(VectorWideningPass pass, MethodTransformContext ctx, MethodBody destMethod, GenericContext genCtx) : base(destMethod, genCtx) {
        _pass = pass;
        _srcMethod = ctx.Method;
        _uniformity = ctx.GetAnalysis<UniformValueAnalysis>();

        _builder = new IRBuilder(default(BasicBlock)!, InsertionDir.After);
    }

    public void CloneWide() {
        foreach (var block in _srcMethod) {
            var destBlock = _destMethod.CreateBlock();
            AddMapping(block, destBlock);

            if (_uniformity.IsDivergent(block)) {
                _blockMasks[destBlock] = new VectorIntrinsic.ExecMask(_pass.GetVectorType(PrimType.Bool), destBlock);
            }
        }

        foreach (var block in _srcMethod) {
            var destBlock = GetMapping(block);
            _currExecMask = _blockMasks.GetValueOrDefault(destBlock);

            for (var inst = block.First; inst != block.Last; inst = inst.Next!) {
                _builder.SetPosition(destBlock, InsertionDir.After);
                var clonedInst = Clone(inst);

                if (clonedInst is Instruction { Block: null } newInst) {
                    destBlock.InsertLast(newInst);
                }
            }
            
            var clonedBranch = WidenBranch(block.Last);
            if (clonedBranch is Instruction { Block: null } newBranch) {
                destBlock.InsertLast(newBranch);
            }
        }
        // TODO: proper masking
        foreach(var (block, mask) in _blockMasks) {
            _builder.SetPosition(block.FirstNonHeader, InsertionDir.Before);
            mask.ReplaceUses(EmitSplat(PrimType.Bool, ConstInt.CreateI(1)));
        }
    }

    protected override Value CreateClone(Instruction inst) {
        Debug.Assert(!inst.IsBranch);

        if (_uniformity.IsUniform(inst)) {
            return base.CreateClone(inst);
        }

        if (inst is PhiInst phi) {
            return WidenPhi(phi);
        }

        if (inst is BinaryInst bin) {
            Debug.Assert(bin.Left.ResultType.Kind.GetStorageType() == bin.Right.ResultType.Kind.GetStorageType());
            var type = _pass.GetVectorType(bin.ResultType);
            var left = RemapCoerced(type, bin.Left);
            var right = RemapCoerced(type, bin.Right);
            return _builder.CreateBin(bin.Op, left, right);
        }
        if (inst is CompareInst cmp) {
            Debug.Assert(cmp.Left.ResultType.Kind.GetStorageType() == cmp.Right.ResultType.Kind.GetStorageType());
            var type = _pass.GetVectorType(cmp.Left.ResultType);
            var left = RemapCoerced(type, cmp.Left);
            var right = RemapCoerced(type, cmp.Right);
            return _builder.CreateCmp(cmp.Op, left, right);
        }
        if (inst is LoadInst load) {
            var vecType = _pass.GetVectorType(load.ElemType);
            // return _builder.Emit(new VectorIntrinsic.MemGather(vecType, Remap(load.Address), _currExecMask));
        }
        if (inst is StoreInst store) {
            var vecType = _pass.GetVectorType(store.ElemType);
            // return _builder.Emit(new VectorIntrinsic.MemScatter(vecType, Remap(store.Address), Remap(store.Value), _currExecMask));
        }
        if (inst is ArrayAddrInst arrd && _uniformity.IsUniform(arrd.Array) && arrd.ElemType.IsValueType) {
            return WidenUniformArrayAddr(arrd);
        }
        if (inst is ConvertInst conv && !conv.CheckOverflow) {
            return WidenConvert(conv.SrcUnsigned ? conv.SrcType.GetUnsigned() : conv.SrcType, conv.DestType, Remap(conv.Value));
        }
        if (inst is SelectInst csel) {
            return new SelectInst(Remap(csel.Cond), Remap(csel.IfTrue), Remap(csel.IfFalse), _pass.GetVectorType(csel.ResultType));
        }

        // TODO: group multiple instructions and generate scalarization loop?
        return Scalarize(inst);
    }
    protected override TypeDesc GetRemappedType(Instruction inst) {
        var type = base.GetRemappedType(inst);

        if (!_uniformity.IsUniform(inst)) {
            return _pass.GetVectorType(type);
        }
        return type;
    }

    private Value RemapCoerced(VectorType type, Value value) {
        if (value is Const cns) {
            return EmitSplat(type.ElemType, cns);
        }
        var mapping = Remap(value);
        Debug.Assert(mapping.ResultType == type);
        return mapping;
    }

    private Value WidenBranch(Instruction inst) {
        if (inst is BranchInst br) {
            if (!br.IsConditional || _uniformity.IsUniform(br.Cond)) {
                return base.CreateClone(inst);
            }

            var mask = Remap(br.Cond);
            return new BranchInst(EmitCmpMask(MaskCompareOp.AnySet, mask), GetMapping(br.Then), GetMapping(br.Else));
        }
        if (inst is ReturnInst) {
            return base.CreateClone(inst);
        }
        throw new NotImplementedException();
    }

    private Value WidenPhi(PhiInst phi) {
        var type = _pass.GetVectorType((TypeDesc)Remap(phi.ResultType));
        var args = new Value[phi.NumArgs * 2];

        for (int i = 0; i < phi.NumArgs; i++) {
            var (pred, val) = phi.GetArg(i);
            pred = GetMapping(pred);

            _builder.SetPosition(pred, InsertionDir.BeforeLast);
            args[i * 2 + 0] = pred;
            args[i * 2 + 1] = RemapCoerced(type, val);
        }
        return new PhiInst(type, args);
    }

    private Value Scalarize(Instruction inst) {
        var laneType = inst.ResultType;
        var vectorType = _pass.GetVectorType(laneType);
        var lanes = new Value[vectorType.Width];

        for (int i = 0; i < vectorType.Width; i++) {
            lanes[i] = base.CreateClone(inst);

            // TODO: masking
            if (lanes[i] is Instruction clonedInst) {
                for (int j = 0; j < clonedInst.Operands.Length; j++) {
                    var oper = clonedInst.Operands[j];

                    if (oper.ResultType is VectorType) {
                        clonedInst.ReplaceOperand(j, EmitGetLane(oper, i));
                    }
                }
                _builder.Emit(clonedInst);
            }
        }
        if (inst.HasResult) {
            return _builder.Emit(new VectorIntrinsic.Create(vectorType, lanes));
        }
        return ConstNull.Create(); // dummy
    }

    private Value WidenUniformArrayAddr(ArrayAddrInst inst) {
        var array = Remap(inst.Array);
        var index = Remap(inst.Index);
        
        if (!inst.InBounds) {
            EmitBoundsCheck(index, _builder.CreateConvert(_builder.CreateArrayLen(array), PrimType.UInt32));
        }
        var basePtr = LoopStrengthReduction.CreateGetDataPtrRange(_builder, array, getCount: false).BasePtr;
        return _builder.Emit(new VectorIntrinsic.OffsetUniformPtr(_pass.GetVectorType(inst.ResultType), basePtr, index));
    }

    private void EmitBoundsCheck(Value index, Value length) {
        var mask = _builder.CreateUlt(index, EmitSplat(PrimType.UInt32, length));
        var throwHelper = _pass._comp.Resolver.Import(typeof(SimdOps)).FindMethod("ConditionalThrow_IndexOutOfRange");
        _builder.CreateCall(throwHelper, EmitCmpMask(MaskCompareOp.AllSet, mask));
    }
    
    private Value WidenConvert(TypeKind srcType, TypeKind dstType, Value value) {
        var op = ConvertOp.BitCast;
        
        if (srcType.IsFloat() && dstType.IsFloat()) {
            op = dstType.BitSize() > srcType.BitSize() ? ConvertOp.FExt : ConvertOp.FTrunc;
        }
        else if ((srcType.IsFloat() && dstType.IsInt()) || (srcType.IsInt() && dstType.IsFloat())) {
            op = srcType.IsFloat() ? ConvertOp.F2I : ConvertOp.I2F;
        }
        else if (dstType.BitSize() > srcType.BitSize()) {
            op = dstType.IsUnsigned() ? ConvertOp.ZeroExt : ConvertOp.SignExt;
        }
        else if (dstType.BitSize() < srcType.BitSize()) {
            op = ConvertOp.Trunc;
        }
        return _builder.Emit(new VectorIntrinsic.Convert(op, dstType, value));
    }

    private Value EmitSplat(TypeDesc laneType, Value value) {
        return _builder.Emit(new VectorIntrinsic.Splat(_pass.GetVectorType(laneType), value));
    }

    private Value EmitGetLane(Value value, int laneIdx) {
        if (value is VectorIntrinsic.Splat splat) {
            return splat.Args[0];
        }
        if (value is VectorIntrinsic.Create create) {
            return create.Args[laneIdx];
        }
        if (value is VectorIntrinsic.OffsetUniformPtr lea) {
            return _builder.CreatePtrOffset(lea.Args[0], EmitGetLane(lea.Args[1], laneIdx), lea.ElemType);
        }
        return _builder.Emit(new VectorIntrinsic.GetLane(value, laneIdx));
    }

    private Value EmitCmpMask(MaskCompareOp op, Value mask) {
        if (_currExecMask != null) {
            mask = _builder.CreateAnd(mask, _currExecMask);
        }
        return _builder.Emit(new VectorIntrinsic.MaskCompare(op, mask));
    }
}