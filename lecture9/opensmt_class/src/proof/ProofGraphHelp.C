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

// Linear merge for resolution
bool ProofGraph::mergeClauses(vector<Lit>& A, vector<Lit>& B, vector<Lit>& res, Var pivot)
{
	res.clear();
	size_t i, j;
	i = 0;
	j = 0;
	bool rep;
	size_t Asize= A.size();
	size_t Bsize= B.size();
	size_t ressize=0;

	//Insert first element
	if(var(A[i])==pivot) i++;
	if(var(B[j])==pivot) j++;
	if(i < Asize && j < Bsize) {
		if (litLess(A[i],B[j])) {
			if(var(A[i])!=pivot){ res.push_back(A[i]); ressize++; }
			i++;
		}
		else {
			if(var(B[j])!=pivot){ res.push_back(B[j]); ressize++; }
			j++;
		}
	}
	else if (i < Asize) {
		if(var(A[i])!=pivot){ res.push_back(A[i]); ressize++; }
		i++;
	}
	else if (j< Bsize) {
		if(var(B[j])!=pivot){ res.push_back(B[j]); ressize++; }
		j++;
	}

	//Insert further elements avoiding repetitions
	while (i < Asize && j < Bsize) {
		if (litLess(A[i],B[j])) {
			rep=(var(A[i])==var(res[ressize-1]) && sign(A[i])==sign(res[ressize-1]));
			if(var(A[i])!=pivot && !rep){ res.push_back(A[i]); ressize++; }
			i++;
		} else {
			rep=(var(B[j])==var(res[ressize-1]) && sign(B[j])==sign(res[ressize-1]));
			if(var(B[j])!=pivot && !rep){ res.push_back(B[j]); ressize++; }
			j++;
		}
	}
	if (i < Asize)
		for (size_t p = i; p < Asize; p++)
		{
			rep=(var(A[p])==var(res[ressize-1]) && sign(A[p])==sign(res[ressize-1]));
			if(var(A[p])!=pivot && !rep){ res.push_back(A[p]); ressize++; }
		}
	else if(j < Bsize)
		for (size_t p = j; p < Bsize; p++)
		{
			rep=(var(B[p])==var(res[ressize-1]) && sign(B[p])==sign(res[ressize-1]));
			if(var(B[p])!=pivot && !rep){ res.push_back(B[p]); ressize++; }
		}
#ifdef CHECK
	assert(ressize==res.size());
#endif
	return true;
}


//Transform proof so to have at each resolution step the positive occurrence of the pivot
//in ant1 and the negative in ant2
void ProofGraph::normalizeProof()
{
	ProofNode* aux;
	bool signPivAnt1=false;
	bool signPivAnt2=false;
	Var pivot;

	for(size_t i=0; i<graph.size(); i++)
		if(graph[i]!=NULL && (graph[i]->ant1!=NULL || graph[i]->ant2!=NULL))
		{
			pivot=graph[i]->getPivot();
			//Look for sign of pivots in antecedents
			if(graph[i]->getAnt1()!=NULL)
			{
				for(size_t j=0; j< graph[i]->getAnt1()->getClauseSize(); j++)
					if(var(graph[i]->getAnt1()->getClause()[j])==pivot)
					{
						signPivAnt1=sign(graph[i]->getAnt1()->getClause()[j]);
						break;
					}
			}
			if(graph[i]->getAnt2()!=NULL)
			{
				for(size_t j=0; j< graph[i]->getAnt2()->getClauseSize(); j++)
					if(var(graph[i]->ant2->getClause()[j])==pivot)
					{
						signPivAnt2=sign(graph[i]->getAnt2()->getClause()[j]);
						break;
					}
			}
			//Ant 1 negative while ant 2 positive
			if(signPivAnt1 && !signPivAnt2)
			{
				aux=graph[i]->getAnt1();
				graph[i]->setAnt1(graph[i]->getAnt2());
				graph[i]->setAnt2(aux);
			}
		}
}

//
// Prints resolution proof graph to a dot file,
// with proper colors
// If skeleton is true then prints propositional variables, otherwise full SMT formulae
void ProofGraph::printProofAsDotty( ostream & out, bool skeleton )
{
	// Visited nodes vector
	vector< bool > visited_dotty( graph.size( ), false );
	// Visit proof graph from sink via DFS
	vector< ProofNode * > q;
	q.push_back(graph[root]);

	out << "digraph proof {" << endl;

	while( !q.empty( ) )
	{
		ProofNode * node = q.back( );
		// Remove node
		q.pop_back( );
		// Node not yet visited
		if( !visited_dotty.at( node->getId() ) )
		{
			//Clean
			//clauseSort(node->clause);
			// Print node
			//0 if original, 1 if lemma, 2 if axiom inst, 3 if deduced, 4 if magenta
			string typ;
			string color="";
			switch( node->getType() )
			{
			case 0:
			{
				typ = "cls_";
				out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
				//solver.printSMTClause( out, node->getClause(), true );
				if(skeleton) printClause(node, out); else printSMTClause(node, out);
				if( node->getPartialInterpolant( ) )
					out << "\\\\n" << node->getPartialInterpolant( );
				out << "\", color=\"blue\", fontcolor=\"white\", style=\"filled\"]" << endl;
			}
			break;
			case 1:
			{
				typ = "lem_";
				out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
				if(skeleton) printClause(node, out); else printSMTClause(node, out);
				if( node->getPartialInterpolant( ) )
					out << "\\\\n" << node->getPartialInterpolant( );
				out << "\", color=\"green\"";
				out << ", style=\"filled\"]" << endl;
			}
			break;
			case 2:
			{
				typ = "axi_";
				out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
				if(skeleton) printClause(node, out); else printSMTClause(node, out);
				if( node->getPartialInterpolant( ) )
					out << "\\\\n" << node->getPartialInterpolant( );
				out << "\", color=\"red\"";
				out << ", style=\"filled\"]" << endl;
			}
			break;
			case 3:
			{
				typ = "ded_";
				out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
				if( !node->getClause().empty( ) )
				{ if(skeleton) printClause(node, out); else printSMTClause(node, out); }
				else out << "+"; // learnt clause
				//out << "\", color=\"grey\"";
				if( node->getPartialInterpolant( ) )
					out << "\\\\n" << node->getPartialInterpolant( );
				out << "\", color=\"grey\"";
				out << ", style=\"filled\"]" << endl;
			}
			break;
			case 4:
			{
				typ = "mag_";
				out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
				if( !node->getClause().empty( ) )
				{ if(skeleton) printClause(node, out); else printSMTClause(node, out); }
				else out << "+"; // magenta clause
				if( node->getPartialInterpolant( ) )
					out << "\\\\n" << node->getPartialInterpolant( );
				out << "\", color=\"purple\"";
				out << ", style=\"filled\"]" << endl;
			}
			break;
			case 5:
			{
				typ = "der_";
				out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
				if( !node->getClause().empty( ) )
				{ if(skeleton) printClause(node, out); else printSMTClause(node, out); }
				else out << "+"; // internal ded clause clause
				if( node->getPartialInterpolant( ) )
					out << "\\\\n" << node->getPartialInterpolant( );
				out << "\", color=\"orange\"";
				out << ", style=\"filled\"]" << endl;
			}
			break;
			default: typ=""; break;
			}

			// Print edges from parents (if existing)
			string t1,t2;
			ProofNode * r1 = node->getAnt1();
			ProofNode * r2 = node->getAnt2();
			if( r1 != NULL && r2 != NULL)
			{
				switch( r1->getType() )
				{
				case 0: t1 = "cls_"; break;
				case 1: t1 = "lem_"; break;
				case 2: t1 = "axi_"; break;
				case 3: t1 = "ded_"; break;
				case 4: t1 = "mag_"; break;
				case 5: t1 = "der_"; break;
				default: t1 = ""; break;
				}
				switch( r2->getType() )
				{
				case 0: t2 = "cls_"; break;
				case 1: t2 = "lem_"; break;
				case 2: t2 = "axi_"; break;
				case 3: t2 = "ded_"; break;
				case 4: t2 = "mag_"; break;
				case 5: t2 = "der_"; break;
				default: t2 = ""; break;
				}

				out << t1 << r1->getId() << " -> " << typ << node->getId();
				out << " [label=\"(" << node->pivot << ")\", fontsize=10]" << endl;
				out << t2 << r2->getId() << " -> " << typ << node->getId();
				out << " [label=\"(" << node->pivot << ")\", fontsize=10]" << endl;

				// Enqueue parents
				q.push_back( r1 );
				q.push_back( r2 );
			}
			//Mark node as visited
			visited_dotty[ node->getId() ] = true;
		}
	}
	out << "}" << endl;
}

void ProofGraph::printClause(ProofNode* n)
{
	assert(n!=NULL);
	vector<Lit>& cl=n->clause;
	cout << n->id << ": ";
	for(size_t k=0;k<cl.size();k++)
	{
		if(sign(cl[k])) cout << "-";
		cout << var(cl[k]) << " ";
	}
	cout << endl;
}

void ProofGraph::printClause(ProofNode* n, ostream & os)
{
	assert(n!=NULL);
	vector<Lit>& cl=n->clause;
	for(size_t k=0;k<cl.size();k++)
	{
		if(sign(cl[k])) os << "-";
		os << var(cl[k]) << " ";
	}
}

void ProofGraph::printSMTClause( ProofNode * n, ostream & os )
{
	assert( n );
	vector< Lit > & c = n->clause;

	if ( c.size( ) == 0 ) os << "-";
	if ( c.size( ) > 1 ) os << "(or ";
	for ( size_t i = 0 ; i < c.size( ) ; i++ )
	{
		Var v = var(c[i]);
		if ( v <= 1 ) continue;
		Enode * e = thandler->varToEnode( v );
		os << ( sign(c[i]) ? "(not " : "" ) << e << ( sign( c[i] ) ? ") " : " " );
	}
	if ( c.size( ) > 1 ) os << ")";
}

#if 0
void ProofGraph::printSMTClause( ProofNode * n )
{
	assert( n );
	vector< Lit > & c = n->clause;
	cout << n->id << ": ";

	if ( c.size( ) == 0 ) cout << "-";
	if ( c.size( ) > 1 ) cout << "(or ";
	for (int i = 0; i < c.size(); i++)
	{
		Var v = var(c[i]);
		if ( v <= 1 ) continue;
		Enode * e = thandler->varToEnode( v );
		cout << (sign(c[i])?"(not ":"") << e << (sign(c[i])?") ":" ");
	}
	if ( c.size( ) > 1 ) cout << ")";
	cout << endl;
}
#endif

//Look for a variable in a clause
//If found, return true and sign of variable
//clause is assumed to be consistent
bool ProofGraph::binSearch(vector<Lit>& clause, Var piv, bool& sig)
{
	int mid,low,high;
	low=0; high=clause.size()-1;
	Lit l; Var v;

	while(low<=high)
	{
		mid=(low+high)/2;
		l=clause[mid];
		v=var(l);

		if( v == piv ){
			sig=sign(l);
			return true;
		}
		else if ( v > piv )
			high=mid-1;
		else
			low=mid+1;
	}
	return false;
}


//Calculate graph info
void ProofGraph::getGraphInfo()
{
	//Visit graph from sink keeping track of edges and nodes
	std::deque<ProofNode*> q;
	ProofNode* n;

	av_cla_size=0;
	max_cla_size=0;
	var_cla_size=0;
	avg_num_res=0;
	var_num_res=0;
	max_num_res=0;
	dim_unsat_core=0;
	num_nodes=0;
	num_edges=0;
	diameter=0;
	num_unary=0;
	avg_num_res_unary=0;
	num_leaves=0;


	q.push_back(graph[root]);
	graph[root]->min_dist_sink=0;
	do
	{
		n=q.front();
		q.pop_front();

		//Update info on parents, given info on node
		if(n->ant1!=NULL || n->ant2!=NULL)
		{
			if(n->ant1!=NULL)
			{
				if(n->ant1->min_dist_sink > n->min_dist_sink + 1)
					n->ant1->min_dist_sink = n->min_dist_sink + 1;
				if(n->ant1->max_dist_sink < n->max_dist_sink + 1)
					n->ant1->max_dist_sink = n->max_dist_sink + 1;
			}
			if(n->ant2!=NULL)
			{
				if(n->ant2->min_dist_sink > n->min_dist_sink + 1)
					n->ant2->min_dist_sink = n->min_dist_sink + 1;
				if(n->ant2->max_dist_sink < n->max_dist_sink + 1)
					n->ant2->max_dist_sink = n->max_dist_sink + 1;
			}
		}
		//Leaf reached; update global info
		else
		{
			if (diameter < n->min_dist_sink)
				diameter=n->min_dist_sink;
		}

		//Node not visited yet
		if(!visited[n->id])
		{
			if(n->ant1!=NULL || n->ant2!=NULL)
			{
				if(n->ant1!=NULL)
				{
					q.push_back(n->ant1);
					num_edges++;
				}
				if(n->ant2!=NULL)
				{
					q.push_back(n->ant2);
					num_edges++;
				}
			}
			else
				num_leaves++;

			//Mark node as visited
			visited[n->id]=true;
			num_nodes++;
			av_cla_size+=n->clause.size();
			avg_num_res+=n->res.size();
			if(n->clause.size() > (size_t)max_cla_size) max_cla_size=n->clause.size();
			if(n->res.size() > (size_t)max_num_res) max_num_res=n->res.size();
			if(n->type==CLAORIG) dim_unsat_core++;
			if(n->clause.size()==1) {
				num_unary++;
				avg_num_res_unary+=n->res.size();
			}

		}
	}
	while(!q.empty());

	if(num_unary>0)avg_num_res_unary/=num_unary;
	avg_num_res/=num_nodes;
	av_cla_size/=num_nodes;
	//Calculate sample variance for num resolvents and clause size
	for(size_t i=0;i<graph.size();i++)
		if(graph[i]!=NULL)
		{
			var_num_res+=pow(graph[i]->res.size()-avg_num_res,2);
			var_cla_size+=pow(graph[i]->clause.size()-av_cla_size,2);
		}
	var_num_res/=(num_nodes-1);
	var_cla_size/=(num_nodes-1);
	//Calculate sample variance for clause size
	visited.reset();

	// Determine actual set of variables
	set<Var> ps;
	for(size_t i=0;i<graph.size();i++)
		if(graph[i]!=NULL && graph[i]->ant1!=NULL && graph[i]->ant2!=NULL)
			ps.insert(graph[i]->pivot);
	num_vars_actual=ps.size();

}

//Input: a vector which will contain the topological sorting of nodes
//Output: a topological sorting antecedents-resolvents
void ProofGraph::topolSortingVec(vector<clauseid_t>& DFS)
{
	vector<clauseid_t>q;
	ProofNode* n;
	DFS.clear();
	clauseid_t c;
	bool push_ant1, push_ant2;

	q.push_back(root);
	do
	{
		c=q.back();
		n=graph[c];
		assert(n!=NULL);
		//Node not visited yet
		if(!visited2[c])
		{
			if(!additionalRandomization())
			{
				//Enqueue antecedents
				if(n->getAnt1()!=NULL && !visited2[n->getAnt1()->getId()]) q.push_back(n->getAnt1()->getId());
				else if(n->getAnt2()!=NULL && !visited2[n->getAnt2()->getId()]) q.push_back(n->getAnt2()->getId());
				//Mark node as visited if both antecedents visited
				else
				{
					visited2[c]=true;
					q.pop_back();
					DFS.push_back(c);
				}
			}
			// Introduce randomization in enqueuing antecedents
			else
			{
				push_ant1 = (n->ant1!=NULL && !visited2[n->ant1->id]);
				push_ant2 = (n->ant2!=NULL && !visited2[n->ant2->id]);
				if(push_ant1 && !push_ant2) q.push_back(n->ant1->id);
				else if(!push_ant1 && push_ant2) q.push_back(n->ant2->id);
				else if(push_ant1 && push_ant2)
				{
					if(rand() %2 ==0)
					{
						q.push_back(n->ant1->id);
						q.push_back(n->ant2->id);
					}
					else
					{
						q.push_back(n->ant2->id);
						q.push_back(n->ant1->id);
					}
				}
				//Mark node as visited if both antecedents visited
				else
				{
					visited2[c]=true;
					q.pop_back();
					DFS.push_back(c);
				}
			}
		}
		else
			q.pop_back();
	}
	while(!q.empty());

	visited2.reset();
}

//TODO GO ON HERE
//Input: a vector which will contain the topological sorting of nodes
//Output: a topological sorting antecedents-resolvents
void ProofGraph::invTopolSortingVec(vector<clauseid_t>& DFS)
{
	vector<clauseid_t> q;
	ProofNode* n;
	DFS.clear();
	clauseid_t c;
	bool resolvents_visited;

	// Start from leaves
	for( size_t i = 0; i < graph.size( ) ; i ++ )
	  if ( graph[ i ] != NULL 
	    && graph[ i ]->isLeaf( ) ) 
	    q.push_back( graph[ i ]->getId( ) );

	do
	{
		c=q.back();
		n=graph[c];
		assert(n!=NULL);
		//Node not visited yet
		if(!visited2[c])
		{
			// Check if all resolvents have been visited, in case enqueue them
			resolvents_visited = true;
			for( set<ProofNode*>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it ++ )
				if( !visited2[(*it)->getId()] ) { q.push_back( (*it)->getId() ); resolvents_visited = false; }
			if( resolvents_visited )
			{
				visited2[c]=true;
				q.pop_back();
				DFS.push_back(c);
			}
		}
		else
			q.pop_back();
	}
	while(!q.empty());

	visited2.reset();
}

void ProofGraph::topolSortingList(list<clauseid_t>& DFS)
{
	vector<clauseid_t>q;
	ProofNode* n;
	DFS.clear();
	clauseid_t c;

	q.push_back(root);
	do
	{
		c=q.back();
		n=graph[c];
		assert(n!=NULL);
		//Node not visited yet
		if(!visited2[c])
		{
			//Enqueue antecedents
			if(n->getAnt1()!=NULL && !visited2[n->getAnt1()->getId()]) q.push_back(n->getAnt1()->getId());
			else if(n->getAnt2()!=NULL && !visited2[n->getAnt2()->getId()]) q.push_back(n->getAnt2()->getId());
			//Mark node as visited if both antecedents visited
			else
			{
				visited2[c]=true;
				q.pop_back();
				DFS.push_back(c);
			}
		}
		else
			q.pop_back();
	}
	while(!q.empty());

	visited2.reset();
}

void ProofGraph::visitProofChains()
{
	//Queue for visit and propagation
	std::deque<clauseid_t> q;
	ProofNode* n;
	//Vector for topological ordering
	vector<clauseid_t> DFSv;
	RuleContext ra;

	//Compute topological sorting of graph
	topolSortingVec(DFSv);

	//Visit in topological order
	for(size_t i=0;i<DFSv.size();i++)
	{
		n=graph[DFSv[i]];
		bool in_proof_chain;

		//Non leaf node
		if(n->ant1!=NULL && n->ant2!=NULL)
		{
			assert( n->type==CLALEARNT || n->type==CLADERIVED );

			if(n->type==CLALEARNT || n->type==CLADERIVED)
			{
				ProofNode* v1=NULL;
				ProofNode* v2=NULL;
				ProofNode* w=NULL;
				ProofNode* v3=NULL;
				ProofNode* v=NULL;

				//Look for rules applicability in first node context
				getApplContext(n->ant1->id,n->id,ra);

				//Check if first context fully belongs to a single proof chain
				if( ra.type!=rNO )
				{
					v1=graph[ra.cv1];
					v2=graph[ra.cv2];
					w=graph[ra.cw];
					v3=graph[ra.cv3];
					v=graph[ra.cv];

					assert(v->id == n->id);

					in_proof_chain=true;

					//v3 should not be internally derived
					if( v3->type==CLADERIVED ) in_proof_chain=false;
					//w should be internally derived
					if( w->type!=CLADERIVED ) in_proof_chain=false;
					//v1 and v2 should not be both internally derived
					if( (v1->type==CLADERIVED) && (v2->type==CLADERIVED) ) in_proof_chain=false;

					if(in_proof_chain)
					{ cout << v->id << " - " << printClauseType(v->type) << " - left context " << " IN  chain - rule "; cout << printRuleType(ra.type) << endl; }
					else
					{ cout << v->id << " - " << printClauseType(v->type) << " - left context " << " OUT chain - rule "; cout << printRuleType(ra.type) << endl; }
				}

				//Look for rules applicability in second node context
				getApplContext(n->ant2->id,n->id,ra);

				//Check if second context fully belongs to a single proof chain
				if( ra.type!=rNO )
				{
					v1=graph[ra.cv1];
					v2=graph[ra.cv2];
					w=graph[ra.cw];
					v3=graph[ra.cv3];
					v=graph[ra.cv];

					in_proof_chain=true;

					assert(v->id == n->id);

					//v3 should not be internally derived
					if( v3->type==CLADERIVED ) in_proof_chain=false;
					//w should be internally derived
					if( w->type!=CLADERIVED ) in_proof_chain=false;
					//v1 and v2 should not be both internally derived
					if( (v1->type==CLADERIVED) && (v2->type==CLADERIVED) ) in_proof_chain=false;

					if(in_proof_chain)
					{ cout << v->id << " - " << printClauseType(v->type) << " - right context " << " IN  chain - rule "; cout << printRuleType(ra.type) << endl; }
					else
					{ cout << v->id << " - " << printClauseType(v->type) << " - right context " << " OUT chain - rule "; cout << printRuleType(ra.type) << endl; }

					printClause(v);
				}
			}
		}
		//Leaf node
		else
		{
			assert( n->type==CLAORIG || n->type==CLALEMMA );
		}
	}
}

string ProofGraph::printRuleType(rul_type rt)
{
	string s;
	switch ((int)rt) {
	case 0:
		s = "A1";
		break;
	case 1:
		s = "A2";
		break;
	case 2:
		s = "A2unary";
		break;
	case 3:
		s = "B2killer";
		break;
	case 4:
		s = "B3";
		break;
	case 5:
		s = "B1";
		break;
	case 6:
		s = "B2";
	case 7:
		s = "A1toB";
		break;
	case 8:
		s = "A2toB";
		break;
	case 9:
		s = "A1undo";
		break;
	default:
		s = "badvalue";
		break;
	}
	return s;
}

string ProofGraph::printClauseType(clause_type ct)
{
	string s;
	switch ((int)ct) {
	case 0:
		s = "original";
		break;
	case 1:
		s = "lemma";
		break;
	case 3:
		s = "learnt";
		break;
	case 4:
		s = "magenta";
		break;
	case 5:
		s = "derived";
		break;
	default:
		s = "badvalue";
		break;
	}
	return s;
}

void ProofGraph::printProofNode(clauseid_t vid)
{
	ProofNode* v=graph[vid];
	if(v==NULL)
	{
		cerr << vid << " removed"<< endl<<endl;
		return;
	}
	cerr << "Node id: " << v->id << "   Type: " << v->type;
	if(v->ant1!=NULL && v->ant2!=NULL)
	{
		cerr << "   Parents: " << v->ant1->id << " " << v->ant2->id << "   Pivot: " << v->pivot;
	}
	cerr << "   Clause: ";
	for(size_t i=0;i<v->clause.size();i++)
	{
		if(sign(v->clause[i])) cerr << "~";
		cerr << var(v->clause[i]) << " ";
	}
	cerr << endl;
	cerr << "Sons: ";
	if(v->res.size()!=0)
	{
		for(set<ProofNode*>::iterator it=v->res.begin();it!=v->res.end();it++)
			cerr << (*it)->id << " ";
		cerr << endl;
	}
	cerr << endl;
}

//Prints info to check rule application effects
void ProofGraph::printContext(RuleContext& ra)
{
	cerr << "Context: " << endl ;
	cerr << "v "<< ra.cv;
	cerr << " - w "<< ra.cw;
	cerr << " - v3 "<< ra.cv3;
	cerr << " - v1 " << ra.cv1;
	cerr << " - v2 " << ra.cv2;
	cerr << " - type " ;
	//rA1,rA2,rA2u,rB2k,rB3,rB1,rB2,rA1B,rA2B,rA1undo,rB,rNO,ru,ru2,rb,rp,rANY
	switch(ra.type)
	{
	case 0:cout << "A1"; break;
	case 1:cout << "A2"; break;
	case 2:cout << "A2u"; break;
	case 3:cout << "B2k"; break;
	case 4:cout << "B3"; break;
	case 5:cout << "B1"; break;
	case 6:cout << "B2"; break;
	case 7:cout << "A1B"; break;
	case 8:cout << "A2B"; break;
	case 9:cout << "A1undo"; break;
	case 10:cout << "B"; break;
	case 11:cout << "NO"; break;
	default: break;
	}
	cout << endl ;
}

//TODO update
//Prints global info
void ProofGraph::printStatus()
{
	cerr 	<< "Rules applications - A1: "
			<< A1 << "  A2: "
			<< A2 << "  A2unary: "
			<< A2U << "  B1: "
			<< B1 << "  B2: "
			<< B2 << "  B2killer: "
			<< B2K << "  B3: "
			<< B3
			<< endl ;
	cerr 	<< "Duplications: "<< num_dup
			<< "   Vector dimension: " << graph.size()
			<< endl << endl;
}

//Input: pivot, clause id
//Output: true if pivot is contained in subtree rooted in input clause
bool ProofGraph::findPivotInSubproof(Var pivot, clauseid_t cl)
{
	//Visit graph from sink keeping track of edges and nodes
	std::deque<ProofNode*> q;
	ProofNode* n;

	n=graph[cl];
	assert(n!=NULL);
	q.push_back(n);

	do
	{
		n=q.front();
		q.pop_front();

		//Non leaf node
		if(n->ant1!=NULL && n->ant2!=NULL)
		{
			if(n->pivot==pivot)
			{
				//cout << "Found pivot " << pivot << " in subtree rooted in clause " << cl << endl;
				return true;
			}
			q.push_back(n->getAnt1());
			q.push_back(n->getAnt2());
		}

	}
	while(!q.empty());

	return false;
}

#if ENABLE_SAFE_VARIABLES
//Output: associate to each node the set of all the variables resolved upon along
//the path node -> root
void ProofGraph::calcSafeVarsSets()
{
	vector<clauseid_t> invDFS;
	// Calculate inverse topological sorting
	invTopolSortingVec( invDFS );

	ProofNode* n;
	// Visit in topological order
	for( size_t i=0; i < invDFS.size(); i++ )
	{
		n=graph[ invDFS[i] ];
		assert(n!=NULL);
		// Root
		if ( n->getNumResolvents() == 0 ) continue;

		// Compute set of safe variables for n as intersection of its resolvents sets, adding
		// respective pivots
		// Start with resolvent 1 and its pivot
		set<Var>& init_set = (*(n->getResolvents().begin()))->getSafeVars();
		Var init_pivot = (*(n->getResolvents().begin()))->getPivot();
		bool found = true;
		// Scan for pivot
		for( set<ProofNode*>::iterator n_res = ++(n->getResolvents().begin()); n_res != n->getResolvents().end() && found; n_res ++ )
		{
			set<Var>& next_set = (*(n_res))->getSafeVars();
			if( next_set.find( init_pivot ) == next_set.end() && (* n_res)->getPivot() != init_pivot ) found = false;

		}
		if( found ) n->getSafeVars().insert( init_pivot );
		// Scan for safe vars
		for( set<Var>::iterator s_var = init_set.begin(); s_var != init_set.end(); s_var ++)
		{
			found = true;
			for( set<ProofNode*>::iterator n_res = ++(n->getResolvents().begin()); n_res != n->getResolvents().end() && found; n_res ++ )
			{
				set<Var>& next_set = (* n_res)->getSafeVars();
				if( next_set.find((*s_var)) == next_set.end() && (* s_var) != (* n_res)->getPivot() ) found = false;
			}
			if( found ) n->getSafeVars().insert( (* s_var) );
		}
/*		cout << "Examining Node " << n->getId() << " Vars : ";
		for( set<Var>::iterator it = n->getSafeVars().begin(); it != n->getSafeVars().end(); it ++) cout << (*it) << " ";
		cout << endl;*/
	}
}
#endif

#endif
