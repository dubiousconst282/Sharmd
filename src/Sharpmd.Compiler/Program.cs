using DistIL;
using DistIL.AsmIO;
using DistIL.CodeGen.Cil;
using DistIL.IR.Utils;
using DistIL.Passes;

using Sharpmd.Compiler;

var resolver = new ModuleResolver();
resolver.AddTrustedSearchPaths();

var module = resolver.Load(args[0]);

var pm = new PassManager() {
    Compilation = new Compilation(module, new ConsoleLogger(), new CompilationSettings()),
    Inspectors = { new PassTimingInspector(), new PassDiffCollector("logs/pass_diff.json", null) }
};

pm.AddPasses()
    .Apply<SimplifyCFG>()
    .Apply<ExtrinsifierPass>()
    .Apply<AggressiveSROA>()
    .Apply<SsaPromotion>()
    .Apply<ExpandLinq>()
    .Apply<SimplifyInsts>(); // lambdas and devirtualization

pm.AddPasses(applyIndependently: true) // this is so that e.g. all callees are in SSA before inlining.
    .Apply<InlineMethods>();

pm.AddPasses()
    .Apply<SimplifyCFG>()
    .Apply<ExtrinsifierPass>()
    .Apply<ScalarReplacement>()
    .Apply<AggressiveSROA>()
    .IfChanged(c => c.Apply<SsaPromotion>()
                     .Apply<InlineMethods>()) // SROA+SSA uncovers new devirtualization oportunities
    .RepeatUntilFixedPoint(maxIters: 3);

var simplifySeg = pm.AddPasses()
    .Apply<SimplifyInsts>()
    .Apply<SimplifyCFG>()
    .Apply<DeadCodeElim>()
    .RepeatUntilFixedPoint(maxIters: 2);

pm.AddPasses()
    .Apply<ValueNumbering>()
    .Apply<LoopStrengthReduction>()
    .IfChanged(simplifySeg);

var candidateMethods = PassManager.GetCandidateMethodsFromIL(module, filter: (caller, method) => {
    if (method.Module != module) return false;
    
    return true;
});

pm.Run(candidateMethods);

var meth = candidateMethods.First(m => m.Name == "<<Main>$>b__0").Body;

IRPrinter.ExportForest(meth, "logs/dump.txt");
//IRPrinter.ExportDot(meth, "logs/dump.dot", [new UniformValueAnalysis(meth, pm.Compilation.GetAnalysis<GlobalFunctionEffects>())]);
IRPrinter.ExportDot(meth, "logs/dump.dot", [new PostDominatorTree(meth)]);


var widenPass = new VectorWideningPass(pm.Compilation, 4);
widenPass.AddEntryPoint(meth);
widenPass.Process();

var vectorMeth = widenPass.GetVectorizedMethod(meth)!;

new ReconvergeCFG().Run(new MethodTransformContext(pm.Compilation, vectorMeth));

new DeadCodeElim().Run(new MethodTransformContext(pm.Compilation, vectorMeth));

IRPrinter.ExportPlain(vectorMeth, "logs/dump_A.txt");
IRPrinter.ExportDot(vectorMeth, "logs/dump_A.dot", [new PostDominatorTree(vectorMeth)]);

new VectorLoweringPass(pm.Compilation).Process(vectorMeth);
IRPrinter.ExportPlain(vectorMeth, "logs/dump_B.txt");

vectorMeth.Definition.ILBody = ILGenerator.GenerateCode(vectorMeth);

module.Save(args[1], true);