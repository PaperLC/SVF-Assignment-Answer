#include "Assignment-1.h"
 #include "WPA/Andersen.h"
 #include <sys/stat.h>
 #include <filesystem>
 #include <fstream>
 #include <sstream>
 #include <string>
 
 using namespace SVF;
 using namespace llvm;
 using namespace std;
 
 /// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path
 /// by matching calls and returns while maintaining a `callstack`.
 /// Sources and sinks are identified by implementing and calling `readSrcSnkFromFile`
 /// Each path including loops, qualified by a `callstack`, should only be traversed once using a `visited` set.
 /// You will need to collect each path from src to snk and then add the path to the `paths` set.
 /// Add each path (a sequence of node IDs) as a string into std::set<std::string> paths
 /// in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs
 void ICFGTraversal::reachability(const ICFGNode* curNode, const ICFGNode* snk) {
	 /// TODO: your code starts from here
	 ICFGNodeCallStackPair curPair(curNode, callstack);
	 if(visited.find(curPair)==visited.end())
	 {
		 visited.insert(curPair);
		 path.push_back(curNode->getId());
		 if(curNode->getId()==snk->getId())
		 {
			 string mypath="START->";
			 for(auto st:path)
			 {
				 mypath+=to_string(st)+"->";
			 }
			 mypath+="END";
			 paths.insert(mypath);
		 }
		 for(auto edge : curNode->getOutEdges())
		 {
			 if(edge->isIntraCFGEdge())
			 {
				 reachability(edge->getDstNode(),snk);
			 }
			 else if(edge->isCallCFGEdge())
			 {
				 CallCFGEdge* callEdge=SVFUtil::dyn_cast<CallCFGEdge>(edge);
				 callstack.push_back(callEdge->getCallSite());
				 reachability(edge->getDstNode(),snk);
				 callstack.pop_back();
			 }
			 else if(edge->isRetCFGEdge())
			 {
				 RetCFGEdge* retEdge=SVFUtil::dyn_cast<RetCFGEdge>(edge);
				 if(!callstack.empty() && callstack.back()->getId()==retEdge->getCallSite()->getId())
				 {
					 callstack.pop_back();
					 reachability(edge->getDstNode(),snk);
					 callstack.push_back(retEdge->getCallSite());
				 }
				 else if(callstack.empty())
				 {
					 reachability(edge->getDstNode(),snk);
				 }
			 }
		 }
	 }
	 visited.erase(curPair);
	 path.pop_back();
 }
 
 /// TODO: Implement your code to parse the two lines to identify sources and sinks from `SrcSnk.txt` for your
 /// reachability analysis The format in SrcSnk.txt is in the form of 
 /// line 1 for sources  "{ api1 api2 api3 }" 
 /// line 2 for sinks    "{ api1 api2 api3 }"
 void ICFGTraversal::readSrcSnkFromFile(const string& filename) {
	 /// TODO: your code starts from here
	 ifstream infile(filename);
	 string line;
	 if(getline(infile,line))
	 {
		 size_t theBegin=line.find("{");
		 size_t theEnd=line.find("}");
		 string sources=line.substr(theBegin+1,theEnd-theBegin-1);
		 stringstream ss(sources);
		 string api;
		 while(ss >> api)
		 {
			 checker_source_api.insert(api);
		 }
	 }
	 if(getline(infile,line))
	 {
		 size_t theBegin=line.find("{");
		 size_t theEnd=line.find("}");
		 string sources=line.substr(theBegin+1,theEnd-theBegin-1);
		 stringstream ss(sources);
		 string api;
		 while(ss >> api)
		 {
			 checker_sink_api.insert(api);
		 }
	 }
 
 }
 
 // TODO: Implement your Andersen's Algorithm here
 /// The solving rules are as follows:
 /// p <--Addr-- o        =>  pts(p) = pts(p) ∪ {o}
 /// q <--COPY-- p        =>  pts(q) = pts(q) ∪ pts(p)
 /// q <--LOAD-- p        =>  for each o ∈ pts(p) : q <--COPY-- o
 /// q <--STORE-- p       =>  for each o ∈ pts(q) : o <--COPY-- p
 /// q <--GEP, fld-- p    =>  for each o ∈ pts(p) : pts(q) = pts(q) ∪ {o.fld}
 /// pts(q) denotes the points-to set of q
 void AndersenPTA::solveWorklist() {
	 /// TODO: your code starts from here
	 for (ConstraintGraph::const_iterator nodeIt = consCG->begin(), nodeEit = consCG->end();nodeIt != nodeEit; nodeIt++) {
		 ConstraintNode *cgNode = nodeIt->second;
		 ConstraintEdge::ConstraintEdgeSetTy addrInedges=cgNode->getAddrInEdges();
		 NodeID debugid=cgNode->getId();//debug
		 for(auto edge:addrInedges)
		 {
			 NodeID dstID=edge->getDstID();
			 NodeID srcID=edge->getSrcID();
			 bool addsuc=addPts(dstID, srcID);
			 PointsTo setsuc=getPts(dstID);//debug
			 pushIntoWorklist(dstID);
		 }
	 }
	 
	 while(!isWorklistEmpty())
	 {
		 NodeID pID=popFromWorklist();
		 ConstraintNode *p=consCG->getConstraintNode(pID);
		 for(auto obj:getPts(pID))
		 {
			 for(auto storeEdge:p->getStoreInEdges())
			 {
				 //if(StoreCGEdge* storeEdge = SVFUtil::cast<StoreCGEdge>(edge))
				 //{
					 NodeID dstID=storeEdge->getDstID();
					 NodeID srcID=storeEdge->getSrcID();
					 if(!(consCG->hasEdge(consCG->getConstraintNode(srcID),consCG->getConstraintNode(obj), ConstraintEdge::ConstraintEdgeK::Copy)))
					 {
						 addCopyEdge(srcID, obj);
						 pushIntoWorklist(srcID);
					 }
					//}
				 
			 }
			 for(auto loadEdge:p->getLoadOutEdges())
			 {
				 //if(LoadCGEdge* loadEdge = SVFUtil::cast<LoadCGEdge>(edge))
				 //{
					 NodeID dstID=loadEdge->getDstID();
					 NodeID srcID=loadEdge->getSrcID();
					 if(!(consCG->hasEdge(consCG->getConstraintNode(obj), consCG->getConstraintNode(dstID), ConstraintEdge::ConstraintEdgeK::Copy)))
					 {
						 addCopyEdge(obj, dstID);
						 pushIntoWorklist(obj);
					 }
				 //}
				 
			 }
		 }
		 for(auto copyEdge:p->getCopyOutEdges())
			 {
				 //if(CopyCGEdge* copyEdge = SVFUtil::cast<CopyCGEdge>(edge))
				 //{
					 NodeID dstID=copyEdge->getDstID();
					 NodeID srcID=copyEdge->getSrcID();
					 if(unionPts(dstID, srcID))
					 {
						 pushIntoWorklist(dstID);
					 }
				 //}
				 
			 }
			 for(auto edge:p->getGepOutEdges())
			 {
				 if(NormalGepCGEdge* gepEdge = SVFUtil::cast<NormalGepCGEdge>(edge))
				 {
					 NodeID dstID=gepEdge->getDstID();
					 NodeID srcID=gepEdge->getSrcID();
					 for(auto obj:getPts(srcID))
					 {
						 NodeID fldObj=consCG->getGepObjVar(obj,gepEdge->getConstantFieldIdx());
						 if(addPts(dstID, fldObj))
						 {
							 pushIntoWorklist(dstID);
						 }
					 }
				 }
				 
			 }
	 }
	 
 }
 
 /// TODO: Checking aliases of the two variables at source and sink. For example:
 /// src instruction:  actualRet = source();
 /// snk instruction:  sink(actualParm,...);
 /// return true if actualRet is aliased with any parameter at the snk node (e.g., via ander->alias(..,..))
 bool ICFGTraversal::aliasCheck(const CallICFGNode* src, const CallICFGNode* snk) {
	 /// TODO: your code starts from here
	 //ICFGNode *inode = ...;  // subclass object CallICFGNode : %call = call i32 (...) @source(),
	 for(auto snkParm:snk->getActualParms())
	 {
		auto srcParm=src->getRetICFGNode()->getActualRet();
			 if(ander->alias(srcParm->getId(), snkParm->getId()))
			 {
				 return true;
			 }
	 }
	 return false;
 }
 
 // Start taint checking.
 // There is a tainted flow from p@source to q@sink
 // if (1) alias(p,q)==true and (2) source reaches sink on ICFG.
 void ICFGTraversal::taintChecking() {
	 const fs::path& config = CUR_DIR() / "SrcSnk.txt";
	 // configure sources and sinks for taint analysis
	 readSrcSnkFromFile(config);
 
	 // Set file permissions to read-only for user, group and others
	 if (chmod(config.string().c_str(), S_IRUSR | S_IRGRP | S_IROTH) == -1) {
		 std::cerr << "Error setting file permissions for " << config << ": " << std::strerror(errno) << std::endl;
		 abort();
	 }
	 ander = new AndersenPTA(pag);
	 ander->analyze();
	 for (const CallICFGNode* src : identifySources()) {
		 for (const CallICFGNode* snk : identifySinks()) {
			 if (aliasCheck(src, snk))
				 reachability(src, snk);
		 }
	 }
 }
 
 /*!
  * Andersen analysis
  */
 void AndersenPTA::analyze() {
	 initialize();
	 initWorklist();
	 /*bool test=this->isWorklistEmpty();
	 if (test) {
		 std::cerr << "Worklist is empty" << std::endl;
	 }
	 else {
		 std::cerr << "Worklist is not empty" << std::endl;
	 }*/
	 do {
		 reanalyze = false;
		 solveWorklist();
		 if (updateCallGraph(getIndirectCallsites()))
			 reanalyze = true;
	 } while (reanalyze);
	 finalize();
 }
 
