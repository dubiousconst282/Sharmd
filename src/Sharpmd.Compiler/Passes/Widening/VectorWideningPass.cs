namespace Sharpmd.Compiler;

using System.Collections.Immutable;

using DistIL;
using DistIL.AsmIO;
using DistIL.IR;
using DistIL.Passes;
using DistIL.Util;

using MethodAttrs = System.Reflection.MethodAttributes;

public class VectorWideningPass {
    internal Compilation _comp;
    internal TypeDef _containerType;
    internal int _targetWidth;

    private Dictionary<TypeDesc, VectorType> _vectorTypeCache = new();
    public Dictionary<MethodBody, MethodBody> VectorizedMethods = new();
    private ArrayStack<MethodBody> _worklist = new();
    
    public VectorWideningPass(Compilation comp, int targetWidth) {
        _comp = comp;
        _containerType = comp.Module.CreateType(null, $"SpmdGenerated__{comp.Module.TypeDefs.Count}_{targetWidth}");
        _targetWidth = targetWidth;
    }

    public void AddEntryPoint(MethodBody method) {
        _worklist.Push(method);
    }
    public void Process() {
        while (!_worklist.IsEmpty) {
            ProcessMethod(_worklist.Pop());
        }
    }

    private void ProcessMethod(MethodBody srcMethod) {
        var destMethod = GetVectorizedMethod(srcMethod)!;
        var ctx = new MethodTransformContext(_comp, srcMethod);
        var cloner = new VectorizingIRCloner(this, ctx, destMethod, default);

        for (int i = 0; i < srcMethod.Args.Length; i++) {
            cloner.AddMapping(srcMethod.Args[i], destMethod.Args[i]);
        }

        cloner.CloneWide();
    }

    internal MethodBody? GetVectorizedMethod(MethodBody srcMethod) {
        var srcDef = srcMethod.Definition;

        if (srcDef.Module != _comp.Module) {
            return null;
        }
        if (VectorizedMethods.TryGetValue(srcMethod, out var vectorBody)) {
            return vectorBody;
        }

        var newParams = ImmutableArray.CreateBuilder<ParamDef>();

        foreach (var arg in srcMethod.Args) {
            var type = arg.Param.Sig;

            if (!UniformValueAnalysis.IsUniform(srcDef, arg.Param)) {
                type = GetVectorType(arg.ResultType);
            }
            newParams.Add(new ParamDef(type, arg.Param.Name, arg.Param.Attribs));
        }
        var retType = srcDef.ReturnType;
    
        if (retType != PrimType.Void && !UniformValueAnalysis.IsUniform(srcDef, srcDef.ReturnParam)) {
            retType = GetVectorType(retType);
        }

        var vectorDef = _containerType.CreateMethod(srcDef.Name, retType, newParams.ToImmutable(), MethodAttrs.Public | MethodAttrs.Static | MethodAttrs.HideBySig);

        vectorDef.Body = new MethodBody(vectorDef);
        VectorizedMethods[srcMethod] = vectorDef.Body;

        return vectorDef.Body;
    }

    internal VectorType GetVectorType(TypeDesc laneType) {
        return _vectorTypeCache.GetOrAddRef(laneType) ??= VectorType.Create(laneType, _targetWidth);
    }
}
