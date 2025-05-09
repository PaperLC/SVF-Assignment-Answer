#include "GraphAlgorithm.h"
#include <string>
#include <algorithm>

using namespace std;

/// TODO: Implement your depth-first search here to traverse each program path from src to dst (each node appears at most once in each path).
/// Add each path as a string into std::set<std::string> paths.
/// Each path should have a format like this: "START->1->2->4->5->END", where -> indicates an edge connecting two node IDs.
void Graph::reachability(Node* src, Node* dst) {
	//cout<<"Start our work!"<<endl;
	if(src->getNodeID() == dst->getNodeID()) {
		//cout<<"We reach the destination!"<<endl;
		string mypath="START->";
		for(auto it=path.begin();it!=path.end();++it)
		{
			mypath=mypath+to_string(*it)+"->";
		}
		mypath=mypath+to_string(dst->getNodeID())+"->END";
		paths.insert(mypath);
		return;
	}
	if(find(path.begin(),path.end(),src->getNodeID())==path.end())
	{
		//src is not visited yet
		path.push_back(src->getNodeID());
		set<const Edge*> myedges=src->getOutEdges();
		for(auto it = myedges.begin(); it != myedges.end(); ++it)
		{
			Node* nextNode=(*it)->getDst();
			reachability(nextNode,dst);
		}
	}
	path.pop_back();
}

/// TODO: Implement constraint solving by iteratively (1) propagating points-to sets among nodes on CGraph, and (2)
/// adding new copy edges until a fixed point is reached (i.e., no new copy edges are added). 
/// The solving rules are as follows: 
/// p <--ADDR-- o   =>  pts(p) = pts(p) ∪ {o}
/// q <--COPY-- p   =>  pts(q) = pts(q) ∪ pts(p) 
/// q <--LOAD-- p   =>  for each o ∈ pts(p) : q <--COPY-- o 
/// q <--STORE-- p  =>  for each o ∈ pts(q) : o <--COPY-- p 
/// pts(q) denotes the points-to set of node q. 
/// Refer to the APIs in CGraph, including `addPts`, `getPts`, `unionPts` and `addEdge` for your implementation.
void CGraph::solveWorklist() {
	//initialize the worklist with all edges in the graph
	for(auto pair :IDToNodeMap)
	{
		pushIntoWorklist(pair.first);
	}
	while(!worklist.empty())
	{
		unsigned myNodeID=popFromWorklist();
		CGNode* myNode=getNode(myNodeID);
		for(auto myEdge :myNode->getOutEdges())
		{
			CGEdge::EdgeType myType=myEdge->getType();
			CGNode* src=myEdge->getSrc();
			CGNode* dst=myEdge->getDst();
			switch(myType)
			{
			case CGEdge::ADDR:
				if(addPts(dst,src))
				{
					pushIntoWorklist(dst->getID());
				}
				break;
			case CGEdge::COPY:
				if(unionPts(dst,src))
				{
					pushIntoWorklist(dst->getID());
				}
				break;
			case CGEdge::LOAD:
				for(auto myobj :src->getPts())
				{
					if(addEdge(getNode(myobj), dst, CGEdge::COPY))
					{
						pushIntoWorklist(dst->getID());
					}
				}
				break;
			case CGEdge::STORE:
				for(auto myobj:dst->getPts())
				{
					if(addEdge(src, getNode(myobj), CGEdge::COPY))
					{
						pushIntoWorklist(src->getID());
					}
				}
				break;
			}
		}
	}
}
