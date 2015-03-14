/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifdef PRODUCE_PROOF

#include "ProofGraph.h"

void ProofGraph::checkClauseSorting(clauseid_t nid)
{
	ProofNode* n=graph[nid];
	assert(n!=NULL);
	assert(n->id==nid);

	if(n->clause.size()==0)return;

	for(size_t i=0;i<n->clause.size()-1;i++)
	{
		if(var(n->clause[i])>
		var(n->clause[i+1]))
		{
			cerr << "Bad clause sorting for clause " << n->id << " of type " << n->type << endl;
			printClause(n);
			assert(false);
		}
		if(var(n->clause[i])==var(n->clause[i+1]) && sign(n->clause[i])==sign(n->clause[i+1]))
		{
			cerr << "Repetition of var " << var(n->clause[i]) << " in clause " << n->id << " of type " << n->type << endl;
			printClause(n);
			assert(false);
		}
		if(var(n->clause[i])==var(n->clause[i+1]) && sign(n->clause[i])!=sign(n->clause[i+1]))
		{
			cerr << "Inconsistency on var " << var(n->clause[i]) << " in clause " << n->id << " of type " << n->type << endl;
			printClause(n);
			assert(false);
		}
	}
}

//Checks for various issues
//return false if issues present
void ProofGraph::checkClause(clauseid_t nid)
{
	ProofNode* n=graph[nid];
	assert(n!=NULL);
	assert(n->id==nid);

	//Check if empty clause
	if(n->id==root)
	{
		if(n->clause.size()!=0)
		{
			cerr << n->id << " is the sink but not an empty clause" << endl;
			printClause(n);
			assert(false);
		}
	}
	if(n->clause.size()==0)
	{
		if(n->id!=root)
		{
			cerr << n->id << " is an empty clause not sink" << endl;
			printClause(n);
			assert(false);
		}
	}
	else
	{
		checkClauseSorting(nid);
	}

	if(n->ant1==NULL && n->ant2!=NULL)
	{
		cerr << "Antecedent 1 null" << endl;
		assert(false);
	}
	if(n->ant1!=NULL && n->ant2==NULL)
	{
		cerr << "Antecedent 2 null" << endl;
		assert(false);
	}

	if(n->ant1!=NULL && n->ant2!=NULL)
	{
		assert(n->id != n->ant1->id && n->id !=n->ant2->id);

		vector<Lit> v;
		mergeClauses(n->ant1->clause,n->ant2->clause,v,n->pivot);
		if(v.size()!=n->clause.size())
		{
			cerr << "Clause : "; printClause(graph[nid]); cout << " does not correctly derive from antecedents " << endl;
			printClause(graph[n->ant1->id]);
			printClause(graph[n->ant2->id]);
			assert(false);
		}
		for(size_t i=0;i<n->clause.size();i++)
			if(!litEq(n->clause[i],v[i]))
			{
				cerr << "Clause : "; printClause(graph[nid]); cout << " does not correctly derive from antecedents " << endl;
				printClause(graph[n->ant1->id]);
				printClause(graph[n->ant2->id]);
				assert(false);
			}
		assert(graph[n->ant1->id]!=NULL);
		assert(graph[n->ant2->id]!=NULL);
	}

	set<ProofNode*>::iterator it;
	ProofNode* r;
	for(it=n->res.begin();it!=n->res.end();it++)
	{
		r=(*it);
		if(graph[r->id]==NULL)
		{
			cerr << "Clause " << nid << " resolvent " << r->id << " does not exist anymore " << endl;
			assert(false);
		}
		assert(r->ant1==n || r->ant2==n);
	}
}

//Checks that the proof graph has no issues
void ProofGraph::checkProof()
{
	//Visit graph from sink keeping track of edges and nodes
	std::deque<ProofNode*> q;
	ProofNode* n;

	q.push_back(graph[root]);
	do
	{
		n=q.front();
		q.pop_front();
		//End current level, change level and set new end
		if(!visited[n->id])
		{
			checkClause(n->id);
			if(n->ant1!=NULL || n->ant2!=NULL)
			{
				if(n->ant1!=NULL)
					q.push_back(n->ant1);
				if(n->ant2!=NULL)
					q.push_back(n->ant2);
			}
			visited[n->id]=true;
		}
	}
	while(!q.empty());
	visited.reset();
}

//Checks if during transformations we come up with nodes with equal clauses
void ProofGraph::checkClauseDuplicates()
{
	int count=0;
	bool succ;

	cout << "# Checking for duplicates and subsumptions" << endl;

	for(size_t i=0;i<graph.size();i++)
		for(size_t j=i+1;j<graph.size();j++)
			if(graph[i]!=NULL && graph[j]!=NULL)
			{
				if(graph[i]->clause.size()==graph[j]->clause.size())
				{
					succ=true;
					for(size_t k=0;k<graph[i]->clause.size();k++)
						if(!litEq(graph[i]->clause[k],graph[j]->clause[k]))
						{ succ=false; break;}
					if(succ)
					{
						cerr << "Clause " << i << " of type " << graph[i]->type << " is equal to clause "
								<< j << " of type " << graph[j]->type << endl;
						printClause(graph[i]);
						printClause(graph[j]);
						count++;
					}
				}
			}
}

//Check if at each resolution step ant 1 has the positive occurrence of the pivot and ant2 the negative
void ProofGraph::checkNormality()
{
	bool signPivAnt1=false;
	bool signPivAnt2=true;
	Var pivot;

	for(size_t i=0; i<graph.size(); i++)
		if(graph[i]!=NULL && (graph[i]->ant1!=NULL || graph[i]->ant2!=NULL))
		{
			pivot=graph[i]->pivot;
			//Look for sign of pivots in antecedents
			if(graph[i]->ant1!=NULL)
			{
				for(size_t j=0; j< graph[i]->ant1->clause.size(); j++)
					if(var(graph[i]->ant1->clause[j])==pivot)
					{
						signPivAnt1=sign(graph[i]->ant1->clause[j]);
						//Ant 1, negative sign
						if(signPivAnt1) assert(false);
						break;
					}
			}
			if(graph[i]->ant2!=NULL)
			{
				for(size_t j=0; j< graph[i]->ant2->clause.size(); j++)
					if(var(graph[i]->ant2->clause[j])==pivot)
					{
						signPivAnt2=sign(graph[i]->ant2->clause[j]);
						//Ant 2, positive sign
						if(!signPivAnt2) assert(false);
						break;
					}
			}
		}
}

//Checks that the pivots are ordered in the right way along each path according to a pairwise ordering criterion
void ProofGraph::checkPivotOrdering(bool(ProofGraph::*ordered)(RuleContext& ra))
{
	//Visit graph from sink keeping track of edges and nodes
	std::deque<ProofNode*> q;
	ProofNode* n;
	set< pair<clauseid_t,clauseid_t> >::iterator it;
	RuleContext ra;

	q.push_back(graph[root]);
	do
	{
		n=q.front();
		q.pop_front();
		//End current level, change level and set new end
		if(!visited[n->id])
		{
			if(n->ant1!=NULL || n->ant2!=NULL)
			{
				//Look for edges in sets
				//Remember that v1 and v2 must be present for a rule to be applied
				if(getApplContext(n->ant1->id,n->id,ra))
				{
					if(!(*this.*ordered)(ra))
					{
						assert(graph[ra.cw]==graph[ra.cv]->ant1 || graph[ra.cw]==graph[ra.cv]->ant2);
						cerr << "Wrong ordering pivots: bottom clause " << ra.cv <<"(" << graph[ra.cv]->pivot
								<< ") \ttop clause " << ra.cw << "(" <<graph[ra.cw]->pivot << ")"<<endl;
					}
				}

				//Remember that v1 and v2 must be present for a rule to be applied
				if(getApplContext(n->ant2->id,n->id,ra))
				{
					if(!(*this.*ordered)(ra))
					{
						assert(graph[ra.cw]==graph[ra.cv]->ant1 || graph[ra.cw]==graph[ra.cv]->ant2);
						cerr << "Wrong ordering pivots: bottom clause " << ra.cv <<"(" << graph[ra.cv]->pivot
								<< ") \ttop clause " << ra.cw << "(" <<graph[ra.cw]->pivot << ")"<<endl;
					}
				}

				if(n->ant1!=NULL)
					q.push_back(n->ant1);
				if(n->ant2!=NULL)
					q.push_back(n->ant2);
			}
			visited[n->id]=true;
		}
	}
	while(!q.empty());
	visited.reset();
}

//Returns true if pivots in context are ordered according to the given criterion
bool ProofGraph::pushUpLightVarCriterionWeakOrdered(RuleContext& ra)
{
	Var t0=graph[ra.cw]->pivot;
	Var t1=graph[ra.cv]->pivot;
	bool t0Light=(light_vars.find(t0)!=light_vars.end());
	bool t1Light=(light_vars.find(t1)!=light_vars.end());

	if(!t0Light && t1Light) return false;
	else return true;
}

//Checks soundness of magentification
void ProofGraph::checkMagentification()
{
/*	cerr << "Set of light variables: ";
	for(set<Var>::iterator it=light_vars.begin();it!=light_vars.end(); it++)
		cerr << (*it) << " ";*/
	cerr << endl;
	for(size_t i=0;i<graph.size();i++)
		if(graph[i]!=NULL)
		{
			if(graph[i]->isLeaf())
			{
				if(graph[i]->type!=CLAMAGENTA && graph[i]->type!=CLAORIG)
				{
					cerr << "Leaf " << i << " should be magenta or original" << endl;
					assert(false);
				}
				if(graph[i]->type==CLAORIG)
				{
					for(size_t j=0; j<graph[i]->clause.size(); j++)
					{
						if(light_vars.find(var(graph[i]->clause[j]))!=light_vars.end())
						{
							cerr << "Blue clause " << i << " contains light var " << var(graph[i]->clause[j]) << endl;
							assert(false);
						}
					}
				}
			}
			else if(graph[i]->type!=CLALEARNT && graph[i]->type!=CLADERIVED)
			{
				cerr << "Internal node " << i << " should be learnt or derived" << endl;
				assert(false);
			}
		}
}

void ProofGraph::checkTreefication()
{
	vector<clauseid_t>q;
	ProofNode* n;
	clauseid_t c;

	q.push_back(root);
	do
	{
		c=q.back();
		n=graph[c];
		assert(n!=NULL);
		//Node not visited yet
		if(!visited[c])
		{
			//Mark node as visited
			visited[c]=true;
			q.pop_back();

			//Check if non leaves node have only one resolvent
			if(n->res.size()>1 && n->ant1!=NULL && n->ant2!=NULL)
			{
				cout << "Clause " << n->id << " has " << n->res.size() << " resolvents" << endl;
				assert(false);
			}

			//Enqueue antecedents not visited
			if(n->ant1!=NULL && !visited[n->ant1->id])q.push_back(n->ant1->id);
			if(n->ant2!=NULL && !visited[n->ant2->id])q.push_back(n->ant2->id);
		}
		else
			q.pop_back();
	}
	while(!q.empty());

	visited.reset();
}

#endif
