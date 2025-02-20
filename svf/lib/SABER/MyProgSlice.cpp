#include "SABER/MyProgSlice.h"

using namespace SVF;
using namespace SVFUtil;

/*!
 * Compute path conditions for nodes on the backward slice
 * path condition of each node is calculated starting from root node (source)
 * Given a SVFGNode n, its path condition C is allocated (path_i stands for one of m program paths reaches n)
 *
 * C = \bigvee Guard(path_i),  0 < i < m
 * Guard(path_i) = \bigwedge VFGGuard(x,y),  suppose (x,y) are two SVFGNode nodes on path_i
 */
bool MyProgSlice::AllPathReachableSolve()
{
    const SVFGNode* source = getSource(); // root node of SVFG
    VFWorkList worklist;
    worklist.push(source);
    /// mark source node conditions to be true
    setVFCond(source,getTrueCond());

    while(!worklist.empty())
    {
        const SVFGNode* node = worklist.pop();
        setCurSVFGNode(node);

        Condition invalidCond = computeInvalidCondFromRemovedSUVFEdge(node);
        Condition cond = getVFCond(node);
        for(SVFGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it!=eit; ++it)
        {
            const SVFGEdge* edge = (*it);
            const SVFGNode* succ = edge->getDstNode();
            if(inBackwardSlice(succ))
            {
                Condition vfCond;
                const SVFBasicBlock* nodeBB = getSVFGNodeBB(node);
                const SVFBasicBlock* succBB = getSVFGNodeBB(succ);
                /// clean up the control flow conditions for next round guard computation
                clearCFCond();

                if(edge->isCallVFGEdge())
                {
                    vfCond = ComputeInterCallVFGGuard(nodeBB,succBB, getCallSite(edge)->getParent());
                }
                else if(edge->isRetVFGEdge())
                {
                    vfCond = ComputeInterRetVFGGuard(nodeBB,succBB, getRetSite(edge)->getParent());
                }
                else
                    vfCond = ComputeIntraVFGGuard(nodeBB,succBB);
                vfCond = condAnd(vfCond, condNeg(invalidCond));
                Condition succPathCond = condAnd(cond, vfCond);
                if(setVFCond(succ,  condOr(getVFCond(succ), succPathCond) ))
                    worklist.push(succ);
            }

            DBOUT(DSaber, outs() << " node (" << node->getId()  <<
                  ") --> " << "succ (" << succ->getId() << ") condition: " << getVFCond(succ) << "\n");
        }
    }

    return isSatisfiableForAll();
}

/*!
 * Compute invalid branch condition stemming from removed strong update value-flow edges
 *
 * Fix issue: https://github.com/SVF-tools/SVF/issues/1306
 * Line 11->13 is removed due to a strong update at Line 13, which means Line 11 is unreachable to Line 13 on the value flow graph.
 * However on the control flow graph they are still considered as reachable,
 * making the vf guard on Line 11 -> Line 15 a true condition (should consider the infeasible branch Line 11 -> Line 13)
 * Therefore, we collect this infeasible branch condition (condition on Line 11 -> Line 13, `a == b`) as an invalid condition (invalidCond),
 * and add the negation of invalidCond when computing value flow guard starting from the source of the SU.
 * In this example, we add `a != b` on Line 11 -> Line 15.
 *
 * @param cur current SVFG node
 * @return invalid branch condition
 */
MyProgSlice::Condition MyProgSlice::computeInvalidCondFromRemovedSUVFEdge(const SVFGNode * cur)
{
    Set<const SVFBasicBlock*> validOutBBs; // the BBs of valid successors
    for(SVFGNode::const_iterator it = cur->OutEdgeBegin(), eit = cur->OutEdgeEnd(); it!=eit; ++it)
    {
        const SVFGEdge* edge = (*it);
        const SVFGNode* succ = edge->getDstNode();
        if(inBackwardSlice(succ))
        {
            validOutBBs.insert(getSVFGNodeBB(succ));
        }
    }
    Condition invalidCond = getFalseCond();
    auto suVFEdgesIt = getRemovedSUVFEdges().find(cur);
    if (suVFEdgesIt != getRemovedSUVFEdges().end())
    {
        for (const auto &succ: suVFEdgesIt->second)
        {
            if (!validOutBBs.count(getSVFGNodeBB(succ)))
            {
                // removed vfg node does not reside in the BBs of valid successors
                const SVFBasicBlock *nodeBB = getSVFGNodeBB(cur);
                const SVFBasicBlock *succBB = getSVFGNodeBB(succ);
                clearCFCond();
                invalidCond = condOr(invalidCond, ComputeIntraVFGGuard(nodeBB, succBB));
            }
        }
    }
    return invalidCond;
}

/*!
 * Solve by computing disjunction of conditions from all sinks (e.g., memory leak)
 */
bool MyProgSlice::isSatisfiableForAll()
{

    Condition guard = getFalseCond();
    for(SVFGNodeSetIter it = sinksBegin(), eit = sinksEnd(); it!=eit; ++it)
    {
        guard = condOr(guard,getVFCond(*it));
    }
    setFinalCond(guard);

    return pathAllocator->isAllPathReachable(guard);
}

/*!
 * Solve by analysing each pair of sinks (e.g., double free)
 */
bool MyProgSlice::isSatisfiableForPairs()
{

    for(SVFGNodeSetIter it = sinksBegin(), eit = sinksEnd(); it!=eit; ++it)
    {
        for(SVFGNodeSetIter sit = it, esit = sinksEnd(); sit!=esit; ++sit)
        {
            if(*it == *sit)
                continue;
            Condition guard = condAnd(getVFCond(*sit),getVFCond(*it));
            if(!isEquivalentBranchCond(guard, getFalseCond()))
            {
                setFinalCond(guard);
                return false;
            }
        }
    }

    return true;
}

const CallICFGNode* MyProgSlice::getCallSite(const SVFGEdge* edge) const
{
    assert(edge->isCallVFGEdge() && "not a call svfg edge?");
    if(const CallDirSVFGEdge* callEdge = SVFUtil::dyn_cast<CallDirSVFGEdge>(edge))
        return getSVFG()->getCallSite(callEdge->getCallSiteId());
    else
        return getSVFG()->getCallSite(SVFUtil::cast<CallIndSVFGEdge>(edge)->getCallSiteId());
}
const CallICFGNode* MyProgSlice::getRetSite(const SVFGEdge* edge) const
{
    assert(edge->isRetVFGEdge() && "not a return svfg edge?");
    if(const RetDirSVFGEdge* callEdge = SVFUtil::dyn_cast<RetDirSVFGEdge>(edge))
        return getSVFG()->getCallSite(callEdge->getCallSiteId());
    else
        return getSVFG()->getCallSite(SVFUtil::cast<RetIndSVFGEdge>(edge)->getCallSiteId());
}

void MyProgSlice::evalFinalCond2Event(GenericBug::EventStack &eventStack) const
{
    NodeBS elems = pathAllocator->exactCondElem(finalCond);
    for(NodeBS::iterator it = elems.begin(), eit = elems.end(); it!=eit; ++it)
    {
        const SVFInstruction* tinst = pathAllocator->getCondInst(*it);
        if(pathAllocator->isNegCond(*it))
            eventStack.push_back(SVFBugEvent(
                                     SVFBugEvent::Branch|((((u32_t)false) << 4) & BRANCHFLAGMASK), tinst));
        else
            eventStack.push_back(SVFBugEvent(
                                     SVFBugEvent::Branch|((((u32_t)true) << 4) & BRANCHFLAGMASK), tinst));
    }
}

/*!
 * Evaluate Atoms of a condition
 * TODO: for now we only evaluate one path, evaluate every single path
 *
 * Atom -- a propositional variable: a, b, c
 * Literal -- an atom or its negation: a, ~a
 * Clause  -- A disjunction of some literals: a \vee b
 * CNF formula -- a conjunction of some clauses:  (a \vee b ) \wedge (c \vee d)
 */
std::string MyProgSlice::evalFinalCond() const
{
    std::string str;
    std::stringstream rawstr(str);
    Set<std::string> locations;
    NodeBS elems = pathAllocator->exactCondElem(finalCond);

    for(NodeBS::iterator it = elems.begin(), eit = elems.end(); it!=eit; ++it)
    {
        const SVFInstruction* tinst = pathAllocator->getCondInst(*it);
        if(pathAllocator->isNegCond(*it))
            locations.insert(tinst->getSourceLoc()+"|False");
        else
            locations.insert(tinst->getSourceLoc()+"|True");
    }

    /// print leak path after eliminating duplicated element
    for(Set<std::string>::iterator iter = locations.begin(), eiter = locations.end();
            iter!=eiter; ++iter)
    {
        rawstr << "\t\t  --> (" << *iter << ") \n";
    }

    return rawstr.str();
}

void MyProgSlice::destroy()
{
}
