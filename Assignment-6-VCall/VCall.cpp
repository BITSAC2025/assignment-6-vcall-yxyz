/**
 * VCall.cpp
 * @author kisslune
 */

#include "A6Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char **argv)
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

    // TODO: 完成以下两个方法
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: 完成此方法。点集和工作列表定义在A6Header.h中
    //  约束图的实现在SVF库中提供
    WorkList<unsigned> wl;

    // 辅助函数：检查从src到dst的Copy边是否存在
    auto hasCopyEdge = [this](unsigned srcId, unsigned dstId) -> bool {
        SVF::ConstraintNode *srcNode = consg->getConstraintNode(srcId);
        if (!srcNode) return false;
        
        for (auto copyEdge : srcNode->getCopyOutEdges())
        {
            if (copyEdge->getDstID() == dstId)
                return true;
        }
        return false;
    };

    // 辅助函数：检查从src到dst的Copy边是否存在（通过入边检查）
    auto hasCopyEdgeIn = [this](unsigned srcId, unsigned dstId) -> bool {
        SVF::ConstraintNode *dstNode = consg->getConstraintNode(dstId);
        if (!dstNode) return false;
        
        for (auto copyEdge : dstNode->getCopyInEdges())
        {
            if (copyEdge->getSrcID() == srcId)
                return true;
        }
        return false;
    };

    // 初始化：处理所有Addr边，建立初始点集
    for (auto iter = consg->begin(); iter != consg->end(); ++iter)
    {
        SVF::ConstraintNode *constraintNode = iter->second;
        
        for (auto addrEdge : constraintNode->getAddrInEdges())
        {
            SVF::AddrCGEdge *edge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(addrEdge);
            if (!edge) continue;
            
            unsigned objId = edge->getSrcID();
            unsigned ptrId = edge->getDstID();
            
            pts[ptrId].insert(objId);
            wl.push(ptrId);
        }
    }

    // 迭代处理工作列表
    while (!wl.empty())
    {
        unsigned ptrId = wl.pop();
        SVF::ConstraintNode *ptrNode = consg->getConstraintNode(ptrId);
        if (!ptrNode) continue;

        // 处理Store边：*ptr = src，需要添加 src --Copy--> obj 边
        for (auto storeEdge : ptrNode->getStoreInEdges())
        {
            SVF::StoreCGEdge *edge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(storeEdge);
            if (!edge) continue;
            
            unsigned srcId = edge->getSrcID();
            
            // 对于ptr点集中的每个对象，检查并添加Copy边
            for (auto objId : pts[ptrId])
            {
                if (hasCopyEdge(srcId, objId))
                    continue;
                
                consg->addCopyCGEdge(srcId, objId);
                wl.push(srcId);
            }
        }

        // 处理Load边：dst = *ptr，需要添加 obj --Copy--> dst 边
        for (auto loadEdge : ptrNode->getLoadOutEdges())
        {
            SVF::LoadCGEdge *edge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(loadEdge);
            if (!edge) continue;
            
            unsigned dstId = edge->getDstID();
            
            // 对于ptr点集中的每个对象，检查并添加Copy边
            for (auto objId : pts[ptrId])
            {
                if (hasCopyEdgeIn(objId, dstId))
                    continue;
                
                consg->addCopyCGEdge(objId, dstId);
                wl.push(objId);
            }
        }

        // 处理Copy边：target = ptr，传播点集
        for (auto copyEdge : ptrNode->getCopyOutEdges())
        {
            SVF::CopyCGEdge *edge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(copyEdge);
            if (!edge) continue;
            
            unsigned targetId = edge->getDstID();
            size_t prevSize = pts[targetId].size();
            
            pts[targetId].insert(pts[ptrId].begin(), pts[ptrId].end());
            
            if (pts[targetId].size() > prevSize)
                wl.push(targetId);
        }

        // 处理Gep边：target = ptr->field，处理字段访问
        for (auto gepEdge : ptrNode->getGepOutEdges())
        {
            SVF::GepCGEdge *edge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(gepEdge);
            if (!edge) continue;
            
            unsigned targetId = edge->getDstID();
            size_t prevSize = pts[targetId].size();
            
            for (auto objId : pts[ptrId])
            {
                unsigned fieldObjId = consg->getGepObjVar(objId, edge);
                pts[targetId].insert(fieldObjId);
            }
            
            if (pts[targetId].size() > prevSize)
                wl.push(targetId);
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph *cg)
{
    // TODO: 完成此方法
    //  调用图的实现在SVF库中提供
    const auto &allIndirectCalls = consg->getIndirectCallsites();

    for (const auto &callsiteInfo : allIndirectCalls)
    {
        SVF::CallBlockNode *callsite = callsiteInfo.first;
        unsigned funcPtrId = callsiteInfo.second;

        // 检查函数指针的点集是否存在
        auto it = pts.find(funcPtrId);
        if (it == pts.end())
            continue;

        const SVF::Function *caller = callsite->getCaller();
        const auto &funcPtrPointsTo = it->second;

        // 遍历函数指针可能指向的所有对象
        for (unsigned potentialFuncId : funcPtrPointsTo)
        {
            // 跳过非函数对象
            if (!consg->isFunction(potentialFuncId))
                continue;
            
            const SVF::Function *callee = consg->getFunction(potentialFuncId);
            cg->addIndirectCallGraphEdge(callsite, caller, callee);
        }
    }
}