#ifndef PROGSLICE_H_
#define PROGSLICE_H_

#include "SABER/SaberCondAllocator.h"
#include "Util/WorkList.h"
#include "Graphs/SVFG.h"
#include "Util/DPItem.h"
#include "Util/SVFBugReport.h"

namespace SVF
{

class MyProgSlice
{

public:
    typedef Set<const SVFGNode*> SVFGNodeSet;
    typedef SVFGNodeSet::const_iterator SVFGNodeSetIter;
    typedef SaberCondAllocator::Condition Condition;
    typedef Map<const SVFGNode*, Condition> SVFGNodeToCondMap; 	///< map a SVFGNode to its condition during value-flow guard computation

    typedef FIFOWorkList<const SVFGNode*> VFWorkList;		    ///< worklist for value-flow guard computation
    typedef FIFOWorkList<const SVFBasicBlock*> CFWorkList;	///< worklist for control-flow guard computation

    typedef SaberCondAllocator::SVFGNodeToSVFGNodeSetMap SVFGNodeToSVFGNodeSetMap;


    /// Constructor
    MyProgSlice(const SVFGNode* src, SaberCondAllocator* pa, const SVFG* graph):
        root(src), partialReachable(false), fullReachable(false), reachGlob(false),
        pathAllocator(pa), _curSVFGNode(nullptr), finalCond(pa->getFalseCond()), svfg(graph)
    {
    }

    /// Destructor
    virtual ~MyProgSlice()
    {
        destroy();
    }

    inline u32_t getForwardSliceSize() const
    {
        return forwardslice.size();
    }
    inline u32_t getBackwardSliceSize() const
    {
        return backwardslice.size();
    }
    /// Forward and backward slice operations
    //@{
    inline void addToForwardSlice(const SVFGNode* node)
    {
        forwardslice.insert(node);
    }
    inline void addToBackwardSlice(const SVFGNode* node)
    {
        backwardslice.insert(node);
    }
    inline bool inForwardSlice(const SVFGNode* node)
    {
        return forwardslice.find(node)!=forwardslice.end();
    }
    inline bool inBackwardSlice(const SVFGNode* node)
    {
        return backwardslice.find(node)!=backwardslice.end();
    }
    inline SVFGNodeSetIter forwardSliceBegin() const
    {
        return forwardslice.begin();
    }
    inline SVFGNodeSetIter forwardSliceEnd() const
    {
        return forwardslice.end();
    }
    inline SVFGNodeSetIter backwardSliceBegin() const
    {
        return backwardslice.begin();
    }
    inline SVFGNodeSetIter backwardSliceEnd() const
    {
        return backwardslice.end();
    }
    //@}

    /// root and sink operations
    //@{
    void setCustomSource(const SVFGNode* source) {
        customSource = source;
    }
    inline const SVFGNode* getSource() const
    {
        if (customSource) {
            return customSource;
        }
        return root;
    }
    inline void addToSinks(const SVFGNode* node)
    {
        sinks.insert(node);
    }
    inline const SVFGNodeSet& getSinks() const
    {
        return sinks;
    }
    inline SVFGNodeSetIter sinksBegin() const
    {
        return sinks.begin();
    }
    inline SVFGNodeSetIter sinksEnd() const
    {
        return sinks.end();
    }
    inline void setPartialReachable()
    {
        partialReachable = true;
    }
    inline void setAllReachable()
    {
        fullReachable = true;
    }
    inline bool setReachGlobal()
    {
        return reachGlob = true;
    }
    inline bool isPartialReachable() const
    {
        return partialReachable || reachGlob;
    }
    inline bool isAllReachable() const
    {
        return fullReachable || reachGlob;
    }
    inline bool isReachGlobal() const
    {
        return reachGlob;
    }
    //@}

    /// Guarded reachability solve
    bool AllPathReachableSolve();
    bool isSatisfiableForAll();
    bool isSatisfiableForPairs();

    /// Get callsite ID and get returnsiteID from SVFGEdge
    //@{
    const CallICFGNode* getCallSite(const SVFGEdge* edge) const;
    const CallICFGNode* getRetSite(const SVFGEdge* edge) const;
    //@}

    /// Condition operations
    //@{
    inline Condition condAnd(const Condition &lhs, const Condition &rhs)
    {
        return pathAllocator->condAnd(lhs,rhs);
    }
    inline Condition condOr(const Condition &lhs, const Condition &rhs)
    {
        return pathAllocator->condOr(lhs,rhs);
    }
    inline Condition condNeg(const Condition &cond)
    {
        return pathAllocator->condNeg(cond);
    }
    inline Condition getTrueCond() const
    {
        return pathAllocator->getTrueCond();
    }
    inline Condition getFalseCond() const
    {
        return pathAllocator->getFalseCond();
    }
    inline std::string dumpCond(const Condition& cond) const
    {
        return pathAllocator->dumpCond(cond);
    }
    /// Evaluate final condition
    std::string evalFinalCond() const;
    /// Add final condition to eventStack
    void evalFinalCond2Event(GenericBug::EventStack &eventStack) const;
    //@}

protected:
    inline const SVFG* getSVFG() const
    {
        return svfg;
    }

    /// Release memory
    void destroy();
    /// Clear Control flow conditions before each VF computation
    inline void clearCFCond()
    {
        /// TODO: how to clean z3 memory
        pathAllocator->clearCFCond();
    }

    /// Get/set VF (value-flow) and CF (control-flow) conditions
    //@{
    inline Condition getVFCond(const SVFGNode* node) const
    {
        SVFGNodeToCondMap::const_iterator it = svfgNodeToCondMap.find(node);
        if(it==svfgNodeToCondMap.end())
        {
            return getFalseCond();
        }
        return it->second;
    }
    inline bool setVFCond(const SVFGNode* node, const Condition &cond)
    {
        SVFGNodeToCondMap::iterator it = svfgNodeToCondMap.find(node);
        // until a fixed-point is reached (condition is not changed)
        if(it!=svfgNodeToCondMap.end() && isEquivalentBranchCond(it->second, cond))
            return false;

        svfgNodeToCondMap[node] = cond;
        return true;
    }
    //@}

    /// Compute guards for value-flows
    //@{
    inline Condition ComputeIntraVFGGuard(const SVFBasicBlock* src, const SVFBasicBlock* dst)
    {
        return pathAllocator->ComputeIntraVFGGuard(src,dst);
    }
    inline Condition ComputeInterCallVFGGuard(const SVFBasicBlock* src, const SVFBasicBlock* dst, const SVFBasicBlock* callBB)
    {
        return pathAllocator->ComputeInterCallVFGGuard(src,dst,callBB);
    }
    inline Condition ComputeInterRetVFGGuard(const SVFBasicBlock* src, const SVFBasicBlock* dst, const SVFBasicBlock* retBB)
    {
        return pathAllocator->ComputeInterRetVFGGuard(src,dst,retBB);
    }
    //@}

    inline bool isEquivalentBranchCond(const Condition &lhs, const Condition &rhs) const
    {
        return pathAllocator->isEquivalentBranchCond(lhs, rhs);
    };

    /// Return the basic block where a SVFGNode resides in
    /// a SVFGNode may not in a basic block if it is not a program statement
    /// (e.g. PAGEdge is an global assignment or NullPtrSVFGNode)
    inline const SVFBasicBlock* getSVFGNodeBB(const SVFGNode* node) const
    {
        const ICFGNode* icfgNode = node->getICFGNode();
        if(SVFUtil::isa<NullPtrSVFGNode>(node) == false)
        {
            return icfgNode->getBB();
        }
        return nullptr;
    }

    /// Get/set current SVFG node
    //@{
    inline const SVFGNode* getCurSVFGNode() const
    {
        return _curSVFGNode;
    }
    inline void setCurSVFGNode(const SVFGNode* node)
    {
        _curSVFGNode = node;
        pathAllocator->setCurEvalSVFGNode(node);
    }
    //@}
    /// Set final condition after all path reachability analysis
    inline void setFinalCond(const Condition &cond)
    {
        finalCond = cond;
    }

    /// Compute invalid branch condition stemming from removed strong update value-flow edges
    Condition computeInvalidCondFromRemovedSUVFEdge(const SVFGNode * cur);

    const SVFGNodeToSVFGNodeSetMap& getRemovedSUVFEdges() const
    {
        return pathAllocator->getRemovedSUVFEdges();
    }

private:
    SVFGNodeSet forwardslice;				///<  the forward slice
    SVFGNodeSet backwardslice;				///<  the backward slice
    SVFGNodeSet sinks;						///<  a set of sink nodes
    const SVFGNode* root;					///<  root node on the slice
    const SVFGNode* customSource = nullptr;    ///<  custom source node
    SVFGNodeToCondMap svfgNodeToCondMap;	///<  map a SVFGNode to its path condition starting from root
    bool partialReachable;					///<  reachable from some paths
    bool fullReachable;						///<  reachable from all paths
    bool reachGlob;							///<  Whether slice reach a global
    SaberCondAllocator* pathAllocator;		///<  path condition allocator
    const SVFGNode* _curSVFGNode;			///<  current svfg node during guard computation
    Condition finalCond;					///<  final condition
    const SVFG* svfg;						///<  SVFG
};

} // End namespace SVF

#endif /* PROGSLICE_H_ */
