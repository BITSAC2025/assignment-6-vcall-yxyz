/**
 * Andersen.cpp
 * @author kisslune
 */

 #include "A5Header.h"

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
     consg->dump("ConstraintGraph");
 
     Andersen andersen(consg);
 
     // TODO: complete the following method
     andersen.runPointerAnalysis();
 
     andersen.dumpResult();
     SVF::LLVMModuleSet::releaseLLVMModuleSet();
     return 0;
 }
 
 
 void Andersen::runPointerAnalysis()
 {
     // TODO: 完成此方法。点集合和工作列表定义在 A5Header.h 中
     //  约束图的实现在 SVF 库中提供
     WorkList<unsigned> worklist;
 
     // 初始化阶段：处理所有地址约束 (ptr = &obj)
     // 地址约束表示对象直接赋值给指针，需要初始化点集合
     for (auto nodeIter = consg->begin(); nodeIter != consg->end(); ++nodeIter)
     {
         unsigned nodeId = nodeIter->first;
         SVF::ConstraintNode *currentNode = nodeIter->second;
 
         // 遍历该节点的所有地址入边，处理地址约束
         const auto &addrEdges = currentNode->getAddrInEdges();
         for (auto *edge : addrEdges)
         {
             SVF::AddrCGEdge *addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge);
             unsigned objId = addrEdge->getSrcID();   // 源对象
             unsigned ptrId = addrEdge->getDstID();   // 目标指针
 
             // 将对象添加到指针的点集合：obj ∈ pts(ptr)
             pts[ptrId].insert(objId);
             worklist.push(ptrId);
         }
     }
 
     // 主循环：迭代处理约束直到工作列表为空
     while (!worklist.empty())
     {
         unsigned ptr = worklist.pop();
         SVF::ConstraintNode *ptrNode = consg->getConstraintNode(ptr);
 
         // 处理 Store 和 Load 约束：需要为点集合中的每个对象添加 Copy 边
         for (unsigned obj : pts[ptr])
         {
             // 处理 Store 约束：*ptr = srcPtr
             // 对于每个 srcPtr --Store--> ptr，需要添加 srcPtr --Copy--> obj
             const auto &storeInEdges = ptrNode->getStoreInEdges();
             for (auto *edge : storeInEdges)
             {
                 SVF::StoreCGEdge *storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge);
                 unsigned srcPtr = storeEdge->getSrcID();
 
                 // 检查是否已存在 srcPtr --Copy--> obj 边
                 SVF::ConstraintNode *srcNode = consg->getConstraintNode(srcPtr);
                 bool hasCopyEdge = false;
                 for (auto *copyEdge : srcNode->getCopyOutEdges())
                 {
                     if (copyEdge->getDstID() == obj)
                     {
                         hasCopyEdge = true;
                         break;
                     }
                 }
 
                 // 若不存在则添加 Copy 边，并将源指针加入工作列表
                 if (!hasCopyEdge)
                 {
                     consg->addCopyCGEdge(srcPtr, obj);
                     worklist.push(srcPtr);
                 }
             }
 
             // 处理 Load 约束：dstPtr = *ptr
             // 对于每个 ptr --Load--> dstPtr，需要添加 obj --Copy--> dstPtr
             const auto &loadOutEdges = ptrNode->getLoadOutEdges();
             for (auto *edge : loadOutEdges)
             {
                 SVF::LoadCGEdge *loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge);
                 unsigned dstPtr = loadEdge->getDstID();
 
                 // 检查是否已存在 obj --Copy--> dstPtr 边
                 SVF::ConstraintNode *dstNode = consg->getConstraintNode(dstPtr);
                 bool hasCopyEdge = false;
                 for (auto *copyEdge : dstNode->getCopyInEdges())
                 {
                     if (copyEdge->getSrcID() == obj)
                     {
                         hasCopyEdge = true;
                         break;
                     }
                 }
 
                 // 若不存在则添加 Copy 边，并将对象加入工作列表
                 if (!hasCopyEdge)
                 {
                     consg->addCopyCGEdge(obj, dstPtr);
                     worklist.push(obj);
                 }
             }
         }
 
         // 处理 Copy 约束：target = ptr
         // 将 ptr 的点集合传播到 target 的点集合
         const auto &copyOutEdges = ptrNode->getCopyOutEdges();
         for (auto *edge : copyOutEdges)
         {
             SVF::CopyCGEdge *copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge);
             unsigned target = copyEdge->getDstID();
 
             // 记录传播前的点集合大小
             size_t prevSize = pts[target].size();
             // 将 ptr 的点集合合并到 target 的点集合
             pts[target].insert(pts[ptr].begin(), pts[ptr].end());
 
             // 如果点集合发生变化，将 target 加入工作列表
             if (pts[target].size() > prevSize)
             {
                 worklist.push(target);
             }
         }
 
         // 处理 Gep 约束：target = ptr.fld
         // 处理字段访问，为点集合中的每个对象获取对应的字段对象
         const auto &gepOutEdges = ptrNode->getGepOutEdges();
         for (auto *edge : gepOutEdges)
         {
             SVF::GepCGEdge *gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge);
             unsigned target = gepEdge->getDstID();
 
             // 记录传播前的点集合大小
             size_t prevSize = pts[target].size();
             // 为 ptr 点集合中的每个对象获取字段对象
             for (unsigned obj : pts[ptr])
             {
                 unsigned fieldObj = consg->getGepObjVar(obj, gepEdge);
                 pts[target].insert(fieldObj);
             }
 
             // 如果点集合发生变化，将 target 加入工作列表
             if (pts[target].size() > prevSize)
             {
                 worklist.push(target);
             }
         }
     }
 }