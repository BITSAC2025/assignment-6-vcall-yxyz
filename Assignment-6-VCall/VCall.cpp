/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A6Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);
    auto cg = pag->getCallGraph();

    // TODO: complete the following two methods
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    
    WorkList<unsigned> wl;
    auto pag = SVF::PAG::getPAG();
    
    // Initialize worklist with Addr edges: p = &o -> o ∈ pts(p)
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        auto node = it->second;
        for (auto edgeIt = node->getOutEdges().begin(); 
             edgeIt != node->getOutEdges().end(); ++edgeIt)
        {
            auto edge = *edgeIt;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Addr)
            {
                unsigned src = edge->getSrcID();  // o (the object)
                unsigned dst = edge->getDstID();  // p (the pointer)
                // p = &o -> o ∈ pts(p), so dst points to src
                pts[dst].insert(src);
                wl.push(dst);
            }
        }
    }
    
    // Process worklist
    while (!wl.empty())
    {
        unsigned src = wl.pop();
        
        // Process Copy edges: q = p -> pts(p) ⊆ pts(q)
        auto node = consg->getCGNode(src);
        if (node)
        {
            for (auto edgeIt = node->getOutEdges().begin(); 
                 edgeIt != node->getOutEdges().end(); ++edgeIt)
            {
                auto edge = *edgeIt;
                unsigned dst = edge->getDstID();
                
                if (edge->getEdgeKind() == SVF::ConstraintEdge::Copy)
                {
                    // pts(src) ⊆ pts(dst)
                    bool changed = false;
                    for (auto pointee : pts[src])
                    {
                        if (pts[dst].insert(pointee).second)
                            changed = true;
                    }
                    if (changed)
                        wl.push(dst);
                }
                else if (edge->getEdgeKind() == SVF::ConstraintEdge::Load)
                {
                    // q = *p -> ∀o ∈ pts(p): pts(o) ⊆ pts(q)
                    bool changed = false;
                    for (auto pointee : pts[src])
                    {
                        // pts(pointee) ⊆ pts(dst)
                        for (auto pointee2 : pts[pointee])
                        {
                            if (pts[dst].insert(pointee2).second)
                                changed = true;
                        }
                    }
                    if (changed)
                        wl.push(dst);
                }
            }
            
            // Process Store edges: *p = q -> ∀o ∈ pts(p): pts(q) ⊆ pts(o)
            for (auto edgeIt = node->getInEdges().begin(); 
                 edgeIt != node->getInEdges().end(); ++edgeIt)
            {
                auto edge = *edgeIt;
                if (edge->getEdgeKind() == SVF::ConstraintEdge::Store)
                {
                    unsigned storeSrc = edge->getSrcID();
                    // ∀o ∈ pts(src): pts(storeSrc) ⊆ pts(o)
                    bool changed = false;
                    for (auto pointee : pts[src])
                    {
                        for (auto pointee2 : pts[storeSrc])
                        {
                            if (pts[pointee].insert(pointee2).second)
                            {
                                changed = true;
                            }
                        }
                    }
                    if (changed)
                    {
                        for (auto pointee : pts[src])
                            wl.push(pointee);
                    }
                }
            }
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library
    
    auto pag = SVF::PAG::getPAG();
    auto icfg = pag->getICFG();
    
    // Iterate through all ICFG nodes to find indirect call sites
    for (auto it = icfg->begin(); it != icfg->end(); ++it)
    {
        SVF::ICFGNode* node = it->second;
        
        // Check if this is an indirect call site
        if (auto* callNode = SVF::SVFUtil::dyn_cast<SVF::CallICFGNode>(node))
        {
            if (callNode->isIndirectCall())
            {
                // Get the function pointer ID from the call site
                // According to Lec06.md: "ConstraintGraph :: Corresponding ICFG Node  The ID of the function pointer"
                SVF::CallBlockNode* callBlock = callNode->getCallBlockNode();
                if (callBlock)
                {
                    // Get the call instruction from call block
                    const llvm::Instruction* callInst = callBlock->getCallSite();
                    if (callInst)
                    {
                        // Get the function pointer PAG node
                        SVF::PAGNode* funPtrNode = pag->getCallSiteFunPtr(callInst);
                        if (funPtrNode)
                        {
                            unsigned funPtrID = funPtrNode->getId();
                            
                            // Get the caller function
                            const SVF::Function* caller = callNode->getFun();
                            
                            // Find all functions that the function pointer may point to
                            if (pts.find(funPtrID) != pts.end())
                            {
                                for (auto funObjID : pts[funPtrID])
                                {
                                    // Get the PAG node for the function object
                                    SVF::PAGNode* funObjNode = pag->getGNode(funObjID);
                                    if (funObjNode)
                                    {
                                        // Get the function from the node's value
                                        const SVF::Function* callee = nullptr;
                                        if (funObjNode->hasValue())
                                        {
                                            callee = pag->getFunction(funObjNode->getValue());
                                        }
                                        
                                        if (callee)
                                        {
                                            // Add edge to call graph
                                            SVF::PTACallGraphNode* callerNode = cg->getCallGraphNode(caller);
                                            SVF::PTACallGraphNode* calleeNode = cg->getCallGraphNode(callee);
                                            
                                            if (callerNode && calleeNode)
                                            {
                                                cg->addIndirectCallGraphEdge(callerNode, calleeNode, callNode);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}