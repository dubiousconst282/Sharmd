namespace Sharpmd.Compiler;

using System.Collections.Immutable;
using System.Diagnostics;
using System.Runtime.Intrinsics;

using DistIL;
using DistIL.AsmIO;
using DistIL.IR;
using DistIL.IR.Utils;
using DistIL.Util;

using TypeAttrs = System.Reflection.TypeAttributes;
using FieldAttrs = System.Reflection.FieldAttributes;
using DistIL.Passes;

/// <summary> Lower vectorized IR to concrete <c>System.Runtime.Intrinsics</c> vector types. </summary>
public class VectorLoweringPass : IMethodPass {
    readonly Compilation _comp;

    readonly Dictionary<VectorType, VectorPack> _vectorPackCache = new();
    readonly Dictionary<Value, TypeDesc> _sourceTypes = new();
    readonly PrimType _naturalMaskType = PrimType.Int32;
    
    readonly TypeDef t_SimdOps;
    
    readonly IRBuilder _builder = new();

    public VectorLoweringPass(Compilation comp) {
        _comp = comp;

        t_SimdOps = (TypeDef)comp.Resolver.Import(typeof(SimdOps));
    }
    

    public MethodPassResult Run(MethodTransformContext ctx) {
        Process(ctx.Method);
        return MethodInvalidations.Everything;
    }

    public void Process(MethodBody method)
    {
        foreach (var inst in method.Instructions()) {
            _builder.SetPosition(inst, InsertionDir.After);
            Value? loweredPack;

            if (inst is VectorIntrinsic vinst) {
                loweredPack = LowerIntrinsic(vinst);
            } else if (inst.ResultType is VectorType vtype) {
                loweredPack = LowerWideInst(inst, vtype);
            } else {
                continue;
            }

            if (loweredPack == null) {
                inst.Remove();
            } else if (loweredPack != inst) {
                _sourceTypes.Add(loweredPack, inst.ResultType);
                inst.ReplaceWith(loweredPack);
            }
        }

        // Fix up types in method def
        foreach (var arg in method.Args) {
            if (arg.ResultType is VectorType type) {
                arg.SetResultType(GetRealType(type));
            }
        }
        if (method.ReturnType is VectorType retType) {
            method.Definition.ReturnParam.Sig = GetRealType(retType);
        }

        _sourceTypes.Clear();
    }

    protected Value? LowerWideInst(Instruction inst, VectorType type)
    {
        if (inst is BinaryInst bin) {
            return LowerBinary(bin.Op, bin.Left, bin.Right, type);
        }
        if (inst is CompareInst cmp) {
            return LowerCompare(cmp.Op, cmp.Left, cmp.Right, type);
        }
        if (inst is SelectInst csel) {
            var cond = CoerceOperand(type, csel.Cond);
            var ifTrue = CoerceOperand(type, csel.IfTrue);
            var ifFalse = CoerceOperand(type, csel.IfFalse);
            return EmitIntrinsic(type, "ConditionalSelect", [cond, ifTrue, ifFalse]);
        }
        if (inst is PhiInst phi) {
            _sourceTypes.Add(inst, type);
            phi.SetResultType(GetRealType(type));

            for (int i = 0; i < phi.NumArgs; i++) {
                var (pred, val) = phi.GetArg(i);
                _builder.SetPosition(pred, InsertionDir.BeforeLast);
                
                var coerced = CoerceOperand(type, val);
                if (coerced != val) {
                    phi.SetValue(i, coerced);
                }
            }
            return phi;
        }
        throw new NotSupportedException();
    }

    protected Value? LowerIntrinsic(VectorIntrinsic inst) {
        _builder.SetNextDebugLocation(inst.DebugLocation);

        switch (inst) {
            case VectorIntrinsic.Splat:
                return EmitSplat((VectorType)inst.ResultType, inst.Args[0]);
                
            case VectorIntrinsic.Create: {
                // JIT knows how to collapse live ranges for Vector.Create() calls, so we don't need to worry about it.
                var type = (VectorType)inst.ResultType;
                return EmitIntrinsic(type, "Create", inst.Operands.ToArray(),
                                     m => m.ParamSig.Count == inst.Operands.Length && m.ParamSig[0].Type == type.ElemType);
            }

            case VectorIntrinsic.GetMask:
                return EmitMoveMask(inst.Args[0], true);

            case VectorIntrinsic.MaskCompare cmp:
                return EmitMaskCompare(cmp.Op, inst.Args[0]);

            case VectorIntrinsic.GetLane: {
                var type = GetSourceVectorType(inst.Args[0]);
                Debug.Assert(GetVectorPack(type).VecTypes!.Length == 1); // TODO
                return EmitIntrinsic(type, "GetElement", inst.Operands.ToArray());
            }

            case VectorIntrinsic.Convert conv: {
                var srcType = GetSourceVectorType(inst.Args[0]);
                return LowerConvert(conv.Op, conv.Args[0], srcType, (VectorType)conv.ResultType);
            }
            default:
                throw new NotImplementedException();
        }
    }

    private Value LowerBinary(BinaryOp op, Value a, Value b, VectorType type) {
        string intrinsicName = op switch {
            BinaryOp.Add or BinaryOp.FAdd => "op_Addition",
            BinaryOp.Sub or BinaryOp.FSub => "op_Subtraction",
            BinaryOp.Mul or BinaryOp.FMul => "op_Multiply",
            BinaryOp.SDiv or BinaryOp.UDiv or BinaryOp.FDiv => "op_Division",
            BinaryOp.And => "op_BitwiseAnd",
            BinaryOp.Or => "op_BitwiseOr",
            BinaryOp.Xor => "op_ExclusiveOr",
            // BinaryOp.Shl => "ShiftLeft",
            // BinaryOp.Shra => "ShiftRightArithmetic",
            // BinaryOp.Shrl => "ShiftRightLogical",
        };
        TypeKind laneType = type.ElemType.Kind;

        if (op is BinaryOp.SDiv or BinaryOp.SRem) {
            laneType = laneType.GetSigned();
        }
        else if (op is BinaryOp.UDiv or BinaryOp.URem) {
            laneType = laneType.GetUnsigned();
        }
        else if (op is >= BinaryOp.FAdd and <= BinaryOp.FRem) {
            Debug.Assert(laneType.IsFloat());
        }
        else if (laneType == TypeKind.Bool) {
            Debug.Assert(op is BinaryOp.And or BinaryOp.Or or BinaryOp.Xor);
            var elemTypeA = GetLoweredElemType(a).Kind;
            var elemTypeB = GetLoweredElemType(b).Kind;

            // Pick whichever type is smaller
            laneType = elemTypeA.BitSize() < elemTypeB.BitSize() ? elemTypeA : elemTypeB;
        }

        if (type.ElemType.Kind != laneType) {
            type = VectorType.Create(PrimType.GetFromKind(laneType), type.Width);
        }

        a = CoerceOperand(type, a);
        b = CoerceOperand(type, b);
        return EmitIntrinsic(type, intrinsicName, [a, b]);
    }

    private Value LowerCompare(CompareOp op, Value a, Value b, VectorType maskType) {
        TypeKind typeA = GetSourceElemType(a).Kind;
        TypeKind typeB = GetSourceElemType(b).Kind;

        Debug.Assert(typeA.GetStorageType() == typeB.GetStorageType());
        TypeKind laneType = typeA;

        if (op.IsFloat()) {
            Debug.Assert(laneType.IsFloat());
        }
        else if (op.IsUnsigned()) {
            Debug.Assert(laneType.IsInt());
            laneType = laneType.GetUnsigned();
        }
        else if (op.IsSigned()) {
            Debug.Assert(laneType.IsInt());
            laneType = laneType.GetSigned();
        }

        Debug.Assert(maskType.ElemType.Kind == TypeKind.Bool);
        var type = VectorType.Create(PrimType.GetFromKind(laneType), maskType.Width);
        a = CoerceOperand(type, a);
        b = CoerceOperand(type, b);

        string intrinsicName = op switch {
            CompareOp.Eq or CompareOp.Ne or CompareOp.FOeq or CompareOp.FUne => "Equals",
            CompareOp.Slt or CompareOp.Ult or CompareOp.FOlt => "LessThan",
            CompareOp.Sgt or CompareOp.Ugt or CompareOp.FOgt => "GreaterThan",
            CompareOp.Sle or CompareOp.Ule or CompareOp.FOle => "LessThanOrEqual",
            CompareOp.Sge or CompareOp.Uge or CompareOp.FOge => "GreaterThanOrEqual",
        };
        var result = EmitIntrinsic(type, intrinsicName, [a, b]);

        if (op is CompareOp.Ne or CompareOp.FUne) {
            result = EmitIntrinsic(type, "op_OnesComplement", [result]);
        }
        return result;
    }

    private Value LowerConvert(ConvertOp op, Value value, VectorType srcType, VectorType destType) {
        var srcKind = srcType.ElemType.Kind;
        var destKind = destType.ElemType.Kind;

        if (srcKind == destKind) {
            return value;
        }

        if (op == ConvertOp.BitCast || (srcKind.BitSize() == destKind.BitSize() && op is not (ConvertOp.I2F or ConvertOp.F2I))) {
            Debug.Assert(srcKind.BitSize() == destKind.BitSize());
            return EmitIntrinsic(srcType, "As" + destKind, [value]);
        }

        Debug.Assert(srcType.Width == destType.Width);

        // Narrow/widen until sizes match
        while (srcKind.BitSize() != destKind.BitSize()) {
            throw new NotImplementedException();
        }

        string intrinsicName = op switch {
            ConvertOp.I2F or ConvertOp.F2I => "ConvertTo" + destKind,
        };
        return EmitIntrinsic(destType, intrinsicName, [value]);
    }

    private Value CoerceOperand(VectorType destType, Value oper) {
        var type = _sourceTypes.GetValueOrDefault(oper, oper.ResultType);
        Debug.Assert(type is VectorType);

        if (type is VectorType vtype && vtype != destType) {
            if (vtype.ElemType == PrimType.Bool) {
                var loweredType = GetLoweredElemType(oper);
                int srcSize = loweredType.Kind.BitSize();
                var destSize = destType.ElemType.Kind.BitSize();
                var op = srcSize > destSize ? ConvertOp.SignExt : ConvertOp.Trunc;
                return LowerConvert(op, oper, VectorType.Create(loweredType, vtype.Width), destType);
            }
            return LowerConvert(ConvertOp.BitCast, oper, vtype, destType);
        }
        return oper;
    }

    private Value EmitSplat(VectorType type, Value value) {
        var elemType = type.ElemType;

        if (elemType == PrimType.Bool) {
            elemType = _naturalMaskType;
            value = _builder.CreateSelect(_builder.CreateNe(value, ConstInt.CreateI(0)), ConstInt.CreateI(-1), ConstInt.CreateI(0));
        }
        return EmitIntrinsic(type, "Create", [value], m => m.ParamSig.Count == 1 && m.ParamSig[0].Type == elemType);
    }
    private Value EmitMoveMask(Value vector, bool normalizeToU64) {
        var mask = EmitIntrinsic(GetLoweredVectorType(vector), "ExtractMostSignificantBits", [vector]);

        if (normalizeToU64 && mask.ResultType != PrimType.UInt64) {
            mask = _builder.CreateConvert(mask, PrimType.UInt64);
        }
        return mask;
    }

    private Value EmitMaskCompare(MaskCompareOp op, Value vector) {
        int width = GetSourceVectorType(vector).Width;
        var mask = EmitMoveMask(vector, false);

        var (targetOp, targetValue) = op switch {
            MaskCompareOp.AnyZero => (CompareOp.Ne, 1L),
            MaskCompareOp.AnySet  => (CompareOp.Ne, 0L),
            MaskCompareOp.AllZero => (CompareOp.Eq, 0L),
            MaskCompareOp.AllSet  => (CompareOp.Eq, 1L),
        };
        return _builder.CreateCmp(targetOp, mask, ConstInt.Create(mask.ResultType, -targetValue >>> (64 - width)));
    }
    
    private Value EmitIntrinsic(VectorType type, string name, Value[] args, Predicate<MethodDesc>? filter = null) {
        var pack = GetVectorPack(type);
        
        var method = FindIntrinsic(pack.VecTypes![0], name, filter);

        if (pack.VecTypes.Length == 1) {
            return _builder.CreateCall(method, args);
        }
        var result = new Undef(pack.WrapperType!) as Value;

        for (int i = 0; i < pack.VecTypes.Length; i++) {
            if (i > 0 && pack.VecTypes[i - 1] != pack.VecTypes[i]) {
                method = FindIntrinsic(pack.VecTypes[i], name, filter);
            }

            var packArgs = new Value[args.Length];
            for (int j = 0; j < args.Length; j++) {
                if (args[j].ResultType == pack.WrapperType) {
                    packArgs[j] = _builder.CreateFieldLoad(args[j].ResultType.Fields[i], args[j]);
                } else {
                    packArgs[j] = args[j];
                }
            }

            var vector = _builder.CreateCall(method, packArgs);
            result = _builder.CreateFieldInsert(pack.WrapperType!.Fields[i], result, vector);
        }
        return result;
    }

    private MethodDesc FindIntrinsic(TypeDesc realType, string name, Predicate<MethodDesc>? filter) {
        var extClass = name.StartsWith("op_") ? realType : GetVectorExtClass(realType);

        foreach (var method in extClass.Methods) {
            if (method.Name == name && method.IsStatic && (filter == null || filter.Invoke(method))) {
                return method.IsGeneric ? method.GetSpec([realType.GenericParams[0]]) : method;
            }
        }
        throw new InvalidOperationException();
    }

    // Vector128`1  ->  Vector128
    private TypeDef GetVectorExtClass(TypeDesc realType) {
        return _comp.Resolver.CoreLib.FindType(
            "System.Runtime.Intrinsics", realType.Name[0..^2],
            throwIfNotFound: true)!;
    }

    
    private VectorPack GetVectorPack(VectorType type) {
        if (type.ElemType == PrimType.Bool) {
            type = VectorType.Create(_naturalMaskType, type.Width);
        }
        return _vectorPackCache.GetOrAddRef(type) ??= new(_comp, type);
    }
    private VectorType GetSourceVectorType(Value value) {
        return (VectorType)_sourceTypes.GetValueOrDefault(value, value.ResultType);
    }
    private TypeDesc GetSourceElemType(Value value) {
        var type = _sourceTypes.GetValueOrDefault(value, value.ResultType);
        return (type as VectorType)?.ElemType ?? type;
    }
    private TypeDesc GetLoweredElemType(Value value) {
        var type = value.ResultType;
        Debug.Assert(type.Name.StartsWith("Vector"));
        return type.IsCorelibType() ? type.GenericParams[0] : throw new NotImplementedException();
    }
    private VectorType GetLoweredVectorType(Value value) {
        var type = GetSourceVectorType(value);
        return VectorType.Create(GetLoweredElemType(value), type.Width);
    }
    
    private TypeDesc GetRealType(VectorType type) {
        var pack = GetVectorPack(type);
        return pack.VecTypes!.Length >= 2 ? pack.WrapperType! : pack.VecTypes[0]!;
    }
}

class VectorPack {
    public readonly TypeSpec[]? VecTypes;
    public readonly TypeDef? WrapperType;
    public readonly Dictionary<string, MethodDesc> FnCache = new();

    public VectorPack(Compilation comp, VectorType type) {
        var laneType = type.ElemType;

        if (laneType.IsInt() || laneType.IsFloat()) {
            int laneBits = laneType.Kind.BitSize();

            var packs = new List<TypeSpec>();

            for (int width = type.Width; width > 0; ) {
                var (genType, vecBits) = (width * laneBits) switch {
                    >= 512 => (typeof(Vector512<>), 512),    
                    >= 256 => (typeof(Vector256<>), 256),
                    _ => (typeof(Vector128<>), 128),
                };
                packs.Add(comp.Resolver.Import(genType).GetSpec([laneType]));
                width -= vecBits / laneBits;
            }
            VecTypes = packs.ToArray();

            if (VecTypes.Length >= 2) {
                WrapperType = comp.GetAuxType().CreateNestedType(
                    $"Vector_{laneType.Name}_x{type.Width}", 
                    TypeAttrs.Sealed | TypeAttrs.SequentialLayout | TypeAttrs.BeforeFieldInit,
                    baseType: comp.Resolver.SysTypes.ValueType);

                for (int i = 0; i < VecTypes.Length; i++) {
                    WrapperType.CreateField("_" + i, VecTypes[i], FieldAttrs.Public);
                }
            }
        } else {
            // TODO: generate InlineArray for scalarized vectors
            WrapperType = comp.GetAuxType().CreateNestedType(
                $"Vector_{laneType.Name}_x{type.Width}", 
                TypeAttrs.Public | TypeAttrs.Sealed | TypeAttrs.SequentialLayout | TypeAttrs.BeforeFieldInit,
                baseType: comp.Resolver.SysTypes.ValueType);

            for (int i = 0; i < type.Width; i++) {
                WrapperType.CreateField("_" + i, type.ElemType, FieldAttrs.Public);
            }
        }
    }
}