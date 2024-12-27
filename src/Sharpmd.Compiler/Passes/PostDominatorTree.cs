namespace Sharpmd.Compiler;

using System.Diagnostics;

using DistIL.Analysis;
using DistIL.IR;
using DistIL.IR.Utils;
using DistIL.Util;

// TODO: Merge this with DomTree
public class PostDominatorTree : IMethodAnalysis, IPrintDecorator
{
    readonly Dictionary<BasicBlock, Node> _block2node = new();
    readonly Node _root;
    bool _hasDfsIndices = false; // whether Node.{PreIndex, PostIndex} have been calculated

    public PostDominatorTree(MethodBody method)
    {
        var nodes = CreateNodes(method);
        _root = nodes[0];
        ComputeDom(nodes);
        ComputeChildren(nodes);
    }

    static IMethodAnalysis IMethodAnalysis.Create(IMethodAnalysisManager mgr)
        => new PostDominatorTree(mgr.Method);

    /// <summary> Returns the immediate post dominator of <paramref name="block"/>, or itself if it's an exiting block. </summary>
    public BasicBlock IDom(BasicBlock block)
    {
        return GetNode(block).IDom.Block;
    }

    /// <summary> Checks if all successor paths from <paramref name="parent"/> must exit through <paramref name="child"/>. </summary>
    public bool Dominates(BasicBlock parent, BasicBlock child)
    {
        if (parent == child) {
            return true;
        }

        var parentNode = GetNode(parent);
        var childNode = GetNode(child);

        if (childNode.IDom == parentNode) {
            return true;
        }

        if (!_hasDfsIndices) {
            ComputeDfsIndices();
        }
        return childNode.PreIndex >= parentNode.PreIndex &&
               childNode.PostIndex <= parentNode.PostIndex;
    }

    /// <summary> Same as <see cref="Dominates(BasicBlock, BasicBlock)"/>, but returns false if <paramref name="parent"/> and <paramref name="child"/> are the same block. </summary>
    public bool StrictlyDominates(BasicBlock parent, BasicBlock child)
    {
        return parent != child && Dominates(parent, child);
    }

    /// <summary> Performs a depth first traversal over this post dominator tree. </summary>
    public void Traverse(Action<BasicBlock>? preVisit = null, Action<BasicBlock>? postVisit = null)
    {
        TraverseNodes(
            preVisit: node => preVisit?.Invoke(node.Block),
            postVisit: node => postVisit?.Invoke(node.Block)
        );
    }

    // NOTE: Querying nodes from unreachable blocks lead to KeyNotFoundException.
    //       Unsure how to best handle them, but ideally passes would not even consider unreachable blocks in the first place.
    private Node GetNode(BasicBlock block)
    {
        return _block2node[block];
    }

    /// <summary> Creates the tree nodes and returns an array with them in DFS post order. </summary>
    private Span<Node> CreateNodes(MethodBody method)
    {
        Debug.Assert(method.EntryBlock.NumPreds == 0);

        var nodes = new Node[method.NumBlocks];
        int index = nodes.Length;
        
        var worklist = new ArrayStack<(BasicBlock Block, BasicBlock.PredIterator Itr)>();

        var (exitBlock, isFakeExit) = GetUnifiedExitBlock(method);
        Push(exitBlock);

        Debug.Assert(!isFakeExit); // FIXME: delete fake block at end

        while (!worklist.IsEmpty) {
            ref var top = ref worklist.Top;

            if (top.Itr.MoveNext()) {
                // Pre
                var child = top.Itr.Current;
                Push(child);
            } else {
                // Post
                var node = _block2node[top.Block];
                node.PostIndex = nodes.Length - index;
                nodes[--index] = node;

                worklist.Pop();
            }
        }
        void Push(BasicBlock block)
        {
            if (!_block2node.ContainsKey(block)) {
                _block2node.Add(block, new Node() { Block = block });
                worklist.Push((block, block.Preds));
            }
        }

        // index will only be >0 if there are unreachable blocks.
        return nodes.AsSpan(index);
    }

    private (BasicBlock Block, bool IsFake) GetUnifiedExitBlock(MethodBody method)
    {
        var exitBlocks = new List<BasicBlock>();

        foreach (var block in method) {
            if (IsExitBlock(block)) {
                exitBlocks.Add(block);
            }
        }
        // No need to create a fake block if there's only one exit
        if (exitBlocks.Count == 1) {
            return (exitBlocks[0], false);
        }

        var unifiedExit = method.CreateBlock();
        unifiedExit.InsertLast(new SwitchInst([ConstInt.CreateI(0), ..exitBlocks], Enumerable.Range(0, exitBlocks.Count).ToArray()));
        return (unifiedExit, true);
    }

    private static bool IsExitBlock(BasicBlock block)
    {
        return block.Last is ReturnInst or ThrowInst;
    }

    // Algorithm from the paper "A Simple, Fast Dominance Algorithm"
    // https://www.cs.rice.edu/~keith/EMBED/dom.pdf
    private void ComputeDom(Span<Node> nodesRPO)
    {
        var entry = nodesRPO[0];
        entry.IDom = entry; // entry block dominates itself

        bool changed = true;
        while (changed) {
            changed = false;
            // foreach block in reverse post order, except entry (at index 0)
            foreach (var node in nodesRPO[1..]) {
                var newDom = default(Node);

                if (IsExitBlock(node.Block)) {
                    // Blocks are not connected to our fake exit block
                    // post_idom(n) of a exit block is itself
                    Debug.Assert(node.Block.NumSuccs == 0);
                    newDom = entry;
                } else {
                    foreach (var succBlock in node.Block.Succs) {
                        var succ = _block2node.GetValueOrDefault(succBlock);

                        if (succ?.IDom != null) {
                            newDom = newDom == null ? succ : Intersect(succ, newDom);
                        }
                    }
                }
                if (newDom != node.IDom) {
                    node.IDom = newDom!;
                    changed = true;
                }
            }
        }

        // Find common ancestor
        static Node Intersect(Node b1, Node b2)
        {
            while (b1 != b2) {
                while (b1.PostIndex < b2.PostIndex) {
                    b1 = b1.IDom;
                }
                while (b2.PostIndex < b1.PostIndex) {
                    b2 = b2.IDom;
                }
            }
            return b1;
        }
    }

    private static void ComputeChildren(Span<Node> nodes)
    {
        // Ignore entry node (index 0) to avoid cycles in the children list
        foreach (var node in nodes[1..]) {
            var parent = node.IDom;
            if (parent.FirstChild == null) {
                parent.FirstChild = node;
            } else {
                Debug.Assert(node.NextChild == null);
                node.NextChild = parent.FirstChild.NextChild;
                parent.FirstChild.NextChild = node;
            }
        }
    }

    private void ComputeDfsIndices()
    {
        int index = 0;
        TraverseNodes(
            preVisit: node => node.PreIndex = ++index,
            postVisit: node => node.PostIndex = index
        );
        _hasDfsIndices = true;
    }

    private void TraverseNodes(Action<Node>? preVisit, Action<Node>? postVisit)
    {
        preVisit?.Invoke(_root);

        var worklist = new ArrayStack<(Node Node, Node? NextChild)>();
        worklist.Push((_root, _root.FirstChild));

        while (!worklist.IsEmpty) {
            ref var curr = ref worklist.Top;
            var child = curr.NextChild;

            if (child != null) {
                curr.NextChild = child.NextChild;
                worklist.Push((child, child.FirstChild));
                preVisit?.Invoke(child);
            } else {
                postVisit?.Invoke(curr.Node);
                worklist.Pop();
            }
        }
    }

    void IPrintDecorator.DecorateLabel(PrintContext ctx, BasicBlock block)
    {
        ctx.Print($"{PrintToner.Comment} postdom={IDom(block)}");
    }

    class Node
    {
        public Node IDom = null!;
        public Node? FirstChild, NextChild; // Links for the children list
        public BasicBlock Block = null!;
        // ComputeDom() assumes that PostIndex holds the post DFS index of each block.
        // Once dominance is computed and when _hasDfsIndices is true, these contain
        // the DFS indices of the actual dominance tree, used for O(1) dominance checks.
        public int PreIndex, PostIndex;

        public override string ToString() => $"{Block} <- {IDom?.Block.ToString() ?? "?"}";
    }
}