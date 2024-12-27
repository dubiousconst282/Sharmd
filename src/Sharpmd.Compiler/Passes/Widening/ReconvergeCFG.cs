namespace Sharpmd.Compiler;

using System.Diagnostics;

using DistIL.Analysis;
using DistIL.IR;
using DistIL.Passes;
using DistIL.Util;

// In essence, this pass converts If-Else blocks into If-If sequences,
// as required to fixup divergent branches after the vector widening pass.
//
//  if (any(x)) A;       if (any(x))  A;
//  else        B;  -->  if (any(~x)) B;
//              C;                    C;
//
// The technique is based on "Vectorising Divergent Control-Flow for SIMD Applications" by Fabian Wahlster
// - https://github.com/rAzoR8/EuroLLVM19
// - https://llvm.org/devmtg/2019-04/slides/Poster-Wahlster-Implementing_SPMD_control_flow_in_LLVM_using_reconverging_CFG.pdf
class ReconvergeCFG : IMethodPass {
    RefSet<BasicBlock> _createdBlocks = new();
    DominatorTree _domTree = null!;
    PostDominatorTree _postDomTree = null!;

    public MethodPassResult Run(MethodTransformContext ctx) {
        bool changed = false;
        _domTree = ctx.GetAnalysis<DominatorTree>();
        _postDomTree = ctx.GetAnalysis<PostDominatorTree>();

        var blocks = new BasicBlock[ctx.Method.NumBlocks];
        int index = 0;
        ctx.Method.TraverseDepthFirst(postVisit: b => blocks[index++] = b);

        foreach (var block in blocks) {
            switch (block.Last) {
                case BranchInst { Cond: VectorIntrinsic.MaskCompare cond } br:
                    changed |= TransformBlock(block, cond);
                    break;
                case BranchInst or ReturnInst or ThrowInst: break;
                default: throw new NotSupportedException();
            }
        }

        _domTree = null!;
        _postDomTree = null!;
        _createdBlocks.Clear();
        
        return changed ? MethodInvalidations.ControlFlow : MethodInvalidations.None;
    }

    private bool TransformBlock(BasicBlock block, VectorIntrinsic.MaskCompare cond) {
        var br = (BranchInst)block.Last;

        Debug.Assert(cond.Op == MaskCompareOp.AnySet);
        Debug.Assert(br.Then.NumPreds == 1);

        var exitBlock = _postDomTree.IDom(block);

        // Don't need to transform single `If` regions.
        if (br.Else == exitBlock) return true;

        //Debug.Assert(!exitBlock.HasPhis); // can't handle phis yet

        var flowBlock = block.Method.CreateBlock(insertAfter: block);
        _createdBlocks.Add(flowBlock);

        // Identify if-else region exits for the `Then` branch,
        // and redirect to new continuation block
        foreach (var pred in exitBlock.Preds) {
            // Skip new blocks because we cannot query dom info for them
            if (_createdBlocks.Contains(pred)) continue;

            if (_domTree.Dominates(br.Then, pred)) {
                pred.RedirectSucc(exitBlock, flowBlock);
            }
        }

        if (ShouldFlatten(br, cond)) {
            br.Cond = ConstInt.CreateI(1);
            flowBlock.InsertLast(new BranchInst(br.Else!));
        } else {
            // Create flow block (for negated condition)
            var invCond = new VectorIntrinsic.MaskCompare(cond.Op.GetInvese(), cond.Args[0]);
            flowBlock.InsertLast(invCond);
            flowBlock.InsertLast(new BranchInst(invCond, br.Else!, exitBlock));
        }
        br.Else = flowBlock;

        return true;
    }

    private bool ShouldFlatten(BranchInst br, VectorIntrinsic.MaskCompare cond) {
        return false;
    }
}