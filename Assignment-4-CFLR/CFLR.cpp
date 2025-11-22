/**
 * CFLR.cpp
 * @author kisslune 
 */

 #include "A4Header.h"

 using namespace SVF;
 using namespace llvm;
 using namespace std;
 
 int main(int argc, char **argv)
 {
     auto moduleNameVec =
             OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                      "[options] <input-bitcode...>");
 
     LLVMModuleSet::buildSVFModule(moduleNameVec);
 
     SVFIRBuilder builder;
     auto pag = builder.build();
     
     std::string pagDotFile = pag->getModuleIdentifier() + ".dot";
     pag->dump(pagDotFile);
 
     CFLR solver;
     solver.buildGraph(pag);
     // TODO: 完成此方法
     solver.solve();
     solver.dumpResult();
 
     LLVMModuleSet::releaseLLVMModuleSet();
     return 0;
 }
 
 
 void CFLR::solve()
 {
     // 收集所有节点并用现有边初始化工作列表
     std::unordered_set<unsigned> nodeSet;
 
     for (auto &nodeItr : graph->getSuccessorMap())
     {
         unsigned sourceNode = nodeItr.first;
         nodeSet.insert(sourceNode);
 
         for (auto &lblItr : nodeItr.second)
         {
             EdgeLabel edgeType = lblItr.first;
             for (auto targetNode : lblItr.second)
             {
                 nodeSet.insert(targetNode);
                 workList.push(CFLREdge(sourceNode, targetNode, edgeType));
             }
         }
     }
 
     // 辅助lambda函数：如果边不存在则添加新边
     auto insertNewEdge = [this](unsigned from, unsigned to, EdgeLabel lbl) {
         if (!graph->hasEdge(from, to, lbl))
         {
             graph->addEdge(from, to, lbl);
             workList.push(CFLREdge(from, to, lbl));
         }
     };
 
     // 初始化VF、VFBar和VA的自反边
     for (auto nodeId : nodeSet)
     {
         insertNewEdge(nodeId, nodeId, VF);
         insertNewEdge(nodeId, nodeId, VFBar);
         insertNewEdge(nodeId, nodeId, VA);
     }
 
     // 辅助函数：应用前向规则 A -> B C（如果src->dst有标签A且dst->next有标签B，则添加src->next标签C）
     auto applyForwardRule = [&](unsigned src, unsigned dst, EdgeLabel srcLabel, EdgeLabel followLabel, EdgeLabel resultLabel) {
         auto &succMap = graph->getSuccessorMap();
         if (succMap.count(dst) && succMap[dst].count(followLabel))
         {
             for (auto nextNode : succMap[dst][followLabel])
                 insertNewEdge(src, nextNode, resultLabel);
         }
     };
 
     // 辅助函数：应用后向规则 A -> B C（如果prev->src有标签B且src->dst有标签A，则添加prev->dst标签C）
     auto applyBackwardRule = [&](unsigned src, unsigned dst, EdgeLabel srcLabel, EdgeLabel prevLabel, EdgeLabel resultLabel) {
         auto &predMap = graph->getPredecessorMap();
         if (predMap.count(src) && predMap[src].count(prevLabel))
         {
             for (auto prevNode : predMap[src][prevLabel])
                 insertNewEdge(prevNode, dst, resultLabel);
         }
     };
 
     // 主工作列表算法
     while (!workList.empty())
     {
         CFLREdge currentEdge = workList.pop();
         unsigned src = currentEdge.src;
         unsigned dst = currentEdge.dst;
         EdgeLabel edgeLabel = currentEdge.label;
 
         auto &successorMap = graph->getSuccessorMap();
         auto &predecessorMap = graph->getPredecessorMap();
 
         // 根据边标签使用switch语句应用语法规则
         switch (edgeLabel)
         {
             case VFBar:
                 applyForwardRule(src, dst, VFBar, AddrBar, PT);
                 // VFBar的传递闭包：VFBar ∷= VFBar VFBar
                 applyForwardRule(src, dst, VFBar, VFBar, VFBar);
                 applyBackwardRule(src, dst, VFBar, VFBar, VFBar);
                 applyForwardRule(src, dst, VFBar, VA, VA);
                 break;
 
             case AddrBar:
                 applyBackwardRule(src, dst, AddrBar, VFBar, PT);
                 break;
 
             case Addr:
                 applyForwardRule(src, dst, Addr, VF, PTBar);
                 break;
 
             case VF:
                 applyForwardRule(src, dst, VF, VF, VF);
                 applyBackwardRule(src, dst, VF, VF, VF);
                 applyBackwardRule(src, dst, VF, Addr, PTBar);
                 applyBackwardRule(src, dst, VF, VA, VA);
                 break;
 
             case Copy:
                 insertNewEdge(src, dst, VF);
                 break;
 
             case SV:
                 applyForwardRule(src, dst, SV, Load, VF);
                 break;
 
             case Load:
                 applyBackwardRule(src, dst, Load, SV, VF);
                 applyBackwardRule(src, dst, Load, PV, VF);
                 applyBackwardRule(src, dst, Load, LV, VA);
                 break;
 
             case PV:
                 applyForwardRule(src, dst, PV, Load, VF);
                 applyForwardRule(src, dst, PV, StoreBar, VFBar);
                 break;
 
             case Store:
                 applyForwardRule(src, dst, Store, VP, VF);
                 applyForwardRule(src, dst, Store, VA, SV);
                 break;
 
             case VP:
                 applyBackwardRule(src, dst, VP, Store, VF);
                 applyBackwardRule(src, dst, VP, LoadBar, VFBar);
                 break;
 
             case CopyBar:
                 insertNewEdge(src, dst, VFBar);
                 break;
 
             case LoadBar:
                 applyForwardRule(src, dst, LoadBar, SVBar, VFBar);
                 applyForwardRule(src, dst, LoadBar, VP, VFBar);
                 applyForwardRule(src, dst, LoadBar, VA, LV);
                 break;
 
             case SVBar:
                 applyBackwardRule(src, dst, SVBar, LoadBar, VFBar);
                 break;
 
             case StoreBar:
                 applyBackwardRule(src, dst, StoreBar, VA, SVBar);
                 break;
 
             case LV:
                 applyForwardRule(src, dst, LV, Load, VA);
                 break;
 
             case VA:
                 applyBackwardRule(src, dst, VA, VFBar, VA);
                 applyForwardRule(src, dst, VA, VF, VA);
                 applyBackwardRule(src, dst, VA, Store, SV);
                 applyForwardRule(src, dst, VA, StoreBar, SVBar);
                 applyBackwardRule(src, dst, VA, PTBar, PV);
                 applyForwardRule(src, dst, VA, PT, VP);
                 applyBackwardRule(src, dst, VA, LoadBar, LV);
                 break;
 
             case PTBar:
                 applyForwardRule(src, dst, PTBar, VA, PV);
                 break;
 
             case PT:
                 applyBackwardRule(src, dst, PT, VA, VP);
                 break;
 
             default:
                 break;
         }
     }
 }
 