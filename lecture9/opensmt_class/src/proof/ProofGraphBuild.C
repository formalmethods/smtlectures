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

// Resolution proof builder
void
ProofGraph::buildProofGraph( Proof & proof
                           , set< int >& axioms_ids
                           , int final_root_id
                           , clauseid_t goal
                           , int nVars )
{
  // FIXME: remove these !
  (void)axioms_ids;
  (void)final_root_id;
  (void)goal;
  /*
  if ( verbose() )
  {
    cout << "# Building proof graph" << endl;
  }
  */
  const double initTime=cpuTime();

  A1=0;A2=0;A2U=0;B1=0;B2=0;B2K=0;B3=0;A1B=0;A2B=0;A1Undo=0;
  av_cla_size=0; max_cla_size=0;
  dim_unsat_core=0;
  num_edges=0;
  num_nodes=0;
  diameter=0;
  num_dup=0;
  num_leaves=0;
  num_node_add_A1=0;
  building_time=0;

  // Resolution tree for clause id; pairs <clause,pivot>
  // Structure:
  // a -
  // b c
  // ...
  // a,b resolved over c...
  map< Clause *, ProofDer * > & clause_to_proof_der = proof.getProof( );
  map< Clause *, ProofDer * >::iterator it;

  //To map clauses to graph id
  //An id is associated when the node is created
  map< Clause *, int > clauseToIDMap;

  //To keep track of visited nodes
  set< Clause * > visitedSet;

  //Queue to build proof graph from sink
  std::deque< Clause * > q;

  int currId         = 0
    , lastInternalId = 0
    , id             = 0
    , id1            = 0
    , id2            = 0;

  ProofNode * n = NULL;

  //Start from empty clause
  q.push_back(NULL);
  do
  {
    //Get current clause
    Clause* currClause=q.back();
    q.pop_back();

    //Clause not visited yet
    if(visitedSet.find(currClause)==visitedSet.end())
    {
      //Get clause derivation tree
      ProofDer &           proofder = *(clause_to_proof_der[currClause]);
      vector< Clause * > & chaincla = (*(proofder.chain_cla));            // Clauses chain
      vector< Var > &      chainvar = (*(proofder.chain_var));            // Pivot chain
      clause_type_t        ctype    = proofder.type;

      // No derivation tree: theory lemma or original clause
      // Non empty clause
      if ( ctype==CLA_ORIG || ctype==CLA_THEORY )
      {
	assert(chaincla.size()==0 || chaincla.size()==1);
	assert(currClause!=NULL);

	//Strange case clause with link
	if(chaincla.size()>0)
	{
	  if(produceInterpolants()>0)
	    solver.setInterpolant( currClause, solver.getInterpolants( chaincla[0] ) );
	  // cout << "Clause with link, type " << proofder.type << endl;
	  // solver.printSMTClause(cout,*currClause);
	  // cout << endl;
	  // cout << "Link, type " << (*(clause_to_proof_der[chaincla[0]])).type << endl;
	  // solver.printSMTClause(cout,*(chaincla[0]));
	  // cout << chaincla[0] << endl;
	  // cout << endl;
	  //q.push_back(chaincla[0]);
	  //continue;
	}
	//Clause not processed yet
	if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
	{
	  n=new ProofNode();
	  for(int k=0;k<(*currClause).size();k++)
	    n->getClause().push_back((*currClause)[k]);
	  //Add node to graph vector
	  currId=(int)graph.size();
	  n->setId(currId);
	  graph.push_back(n);
	  assert(graph[currId]==n);
	  //Update map clause->id
	  clauseToIDMap[currClause]=currId;
	  //Sort clause literals
	  std::sort(n->getClause().begin(),n->getClause().end());
#ifdef CHECK
	  checkClauseSorting(n->getId());
#endif
	}
	// NB: internal derived clauses not considered here
	//Original clause
	if(ctype==CLA_ORIG)
	{
	  graph[clauseToIDMap[currClause]]->setType(CLAORIG);
	  //Determine partition mask in case of interpolation
	  if(produceInterpolants()>0)
	  {
	    graph[clauseToIDMap[currClause]]->setInterpPartitionMask( solver.getIPartitions( currClause ) );
	    // cout << "Associating mask " << graph[clauseToIDMap[currClause]]->partition_mask << " to clause "; printClause(graph[clauseToIDMap[currClause]]);
	  }
	}
	// Theory clause
	else if (ctype==CLA_THEORY)
	{
	  graph[clauseToIDMap[currClause]]->setType(CLALEMMA);
	  //Determine list of partial interpolants in case of theory lemma
	  if( produceInterpolants( ) > 0 )
	  {
	    Enode * partial_interp_list = solver.getInterpolants( currClause );
	    assert( partial_interp_list );
	    graph[ clauseToIDMap[ currClause ] ]->setPartialInterpolant( partial_interp_list );
	  }
	}
	//TODO: how to distinguish between green and red???
      }
      // Learnt clause
      // Resolution tree present
      else if(ctype==CLA_LEARNT)
      {
	assert(chaincla.size() >= 2);
	// No internal deduced nodes
	if ( chaincla.size( ) == 2 )
	{
	  assert(chainvar.size()==1);
	  // First clause not yet processed
	  if(clauseToIDMap.find(chaincla[0])==clauseToIDMap.end())
	  {
	    n=new ProofNode();
	    for(int k=0;k<(*chaincla[0]).size();k++)
	      n->getClause().push_back((*chaincla[0])[k]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->setId(currId);
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[chaincla[0]]=currId;
	    //Add clause to queue
	    q.push_back(chaincla[0]);
	    //Sort clause literals
	    std::sort(n->getClause().begin(),n->getClause().end());

#ifdef CHECK
	    checkClauseSorting(n->getId());
#endif
	  }
	  if(clauseToIDMap.find(chaincla[1])==clauseToIDMap.end())
	  {
	    ProofNode* n=new ProofNode();
	    for(int k=0;k<(*chaincla[1]).size();k++)
	      n->getClause().push_back((*chaincla[1])[k]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->setId(currId);
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[chaincla[1]]=currId;
	    //Add clause to queue
	    q.push_back(chaincla[1]);
	    //Sort clause literals
	    std::sort(n->getClause().begin(),n->getClause().end());

#ifdef CHECK
	    checkClauseSorting(n->getId());
#endif
	  }

	  id1=clauseToIDMap[chaincla[0]];
	  id2=clauseToIDMap[chaincla[1]];
	  // Clause not yet processed
	  if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
	  {
	    ProofNode* n=new ProofNode();
	    mergeClauses(graph[id1]->getClause(),graph[id2]->getClause(),n->getClause(),chainvar[0]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->setId(currId);
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[currClause]=currId;

#ifdef CHECK
	    checkClauseSorting(n->getId());
#endif
	  }
	  id=clauseToIDMap[currClause];
	  // Setting edges, pivot, type
	  graph[id1]->addResolvent(graph[id]);
	  graph[id2]->addResolvent(graph[id]);
	  graph[id]->setAnt1(graph[id1]);
	  graph[id]->setAnt2(graph[id2]);
	  graph[id]->setPivot(chainvar[0]);
	  graph[id]->setType(CLALEARNT);
	  //Sink check
	  if(currClause==NULL)
	    root=id;
	}
	else
	  // Yes internal deduced clauses
	{
	  if(clauseToIDMap.find(chaincla[0])==clauseToIDMap.end())
	  {
	    n=new ProofNode();
	    for(int k=0;k<(*chaincla[0]).size();k++)
	      n->getClause().push_back((*chaincla[0])[k]);
	    //Add node to graph vector
	    currId=(int)graph.size();
	    n->setId(currId);
	    graph.push_back(n);
	    assert(graph[currId]==n);
	    //Update map clause->id
	    clauseToIDMap[chaincla[0]]=currId;
	    //Add clause to queue
	    q.push_back(chaincla[0]);
	    //Sort clause literals
	    std::sort(n->getClause().begin(),n->getClause().end());

#ifdef CHECK
	    checkClauseSorting(n->getId());
#endif
	  }
	  for ( size_t i = 1 ; i < chaincla.size() ; i ++ )
	  {
	    if(clauseToIDMap.find(chaincla[i])==clauseToIDMap.end())
	    {
	      ProofNode* n=new ProofNode();
	      for(int k=0;k<(*chaincla[i]).size();k++)
		n->getClause().push_back((*chaincla[i])[k]);
	      //Add node to graph vector
	      currId=(int)graph.size();
	      n->setId(currId);
	      graph.push_back(n);
	      assert(graph[currId]==n);
	      //Update map clause->id
	      clauseToIDMap[chaincla[i]]=currId;
	      //Add clause to queue
	      q.push_back(chaincla[i]);
	      //Sort clause literals
	      std::sort(n->getClause().begin(),n->getClause().end());

#ifdef CHECK
	      checkClauseSorting(n->getId());
#endif
	    }

	    if(i<chaincla.size()-1)
	    {
	      // Creation new internal deduced node
	      n=new ProofNode();
	      //Add node to graph vector
	      currId=(int)graph.size();
	      n->setId(currId);
	      n->setType(CLADERIVED);
	      n->setPivot(chainvar[i-1]);
	      graph.push_back(n);
	      assert(graph[currId]==n);

	      // Edges creation
	      if(i==1)
		// First internal node deduced from first clauses 0 and 1
	      {
		id1=clauseToIDMap[chaincla[0]];
		id2=clauseToIDMap[chaincla[1]];
		// Setting edges, type
		graph[id1]->addResolvent(graph[currId]);
		graph[id2]->addResolvent(graph[currId]);
		graph[currId]->setAnt1(graph[id1]);
		graph[currId]->setAnt2(graph[id2]);
		mergeClauses(graph[id1]->getClause(),graph[id2]->getClause(),n->getClause(),chainvar[0]);
		lastInternalId=currId;

#ifdef CHECK
		checkClauseSorting(n->getId());
#endif
	      }
	      else
		// Other internal nodes deduced from clause i and last internal node
	      {
		id2=clauseToIDMap[chaincla[i]];
		graph[lastInternalId]->addResolvent(graph[currId]);
		graph[id2]->addResolvent(graph[currId]);
		graph[currId]->setAnt1(graph[lastInternalId]);
		graph[currId]->setAnt2(graph[id2]);
		mergeClauses(graph[id2]->getClause(),graph[lastInternalId]->getClause(),n->getClause(),chainvar[i-1]);
		lastInternalId=currId;

#ifdef CHECK
		checkClauseSorting(n->getId());
#endif
	      }
	    }
	    // End tree reached: examining currClause
	    else
	    {
	      id2=clauseToIDMap[chaincla[i]];
	      if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
	      {
		n=new ProofNode();
		mergeClauses(graph[id2]->getClause(),graph[lastInternalId]->getClause(),n->getClause(),chainvar[i-1]);
		//Add node to graph vector
		currId=(int)graph.size();
		n->setId(currId);
		graph.push_back(n);
		assert(graph[currId]==n);
		//Update map clause->id
		clauseToIDMap[currClause]=currId;

#ifdef CHECK
		checkClauseSorting(n->getId());
#endif
	      }
	      id=clauseToIDMap[currClause];
	      // Setting edges, pivot, type
	      // Edges from last clause and last internal node
	      graph[lastInternalId]->addResolvent(graph[id]);
	      graph[id2]->addResolvent(graph[id]);
	      graph[id]->setAnt1(graph[lastInternalId]);
	      graph[id]->setAnt2(graph[id2]);
	      graph[id]->setPivot(chainvar[i-1]);
	      graph[id]->setType(CLALEARNT);
	      //Sink check
	      if(currClause==NULL)
		root=id;
	    }
	  }
	}
      }
      //Mark clause as visited
      visitedSet.insert(currClause);
    }
  }
  while(!q.empty());

  if(graph.size()>SIZE_BIT_VECTOR)
  {
    cerr << "# Error: Number of nodes too large: " << graph.size() << " but limit is " << SIZE_BIT_VECTOR <<  endl;
    cerr << "# Error: Increase SIZE_BIT_VECTOR to " << graph.size() <<  endl;
    exit( 1 );
  }

  num_vars_limit=nVars;

  //Keep track of visited nodes
  visited.reset();

  building_time=cpuTime()-initTime;
  //checkClauseDuplicates();
  //visitProofChains();
}

//TODO Resolution proof destructor
ProofGraph::~ProofGraph()
{
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL)removeNode(i);
}

// Clause duplication to help swapping, given node w and a resolvent v
// add one copy of w containing all resolvents besides v
// update w antecedents
// update links to and from w resolvents
// If w has already one resolvent, no modifications done
//TODO change parameters
void ProofGraph::dupliClause(clauseid_t wid,clauseid_t vid)
{
  ProofNode*v=graph[vid];
  ProofNode*w=graph[wid];
#ifdef CHECK
  assert(v!=NULL);
  assert(w->getNumResolvents()>0);
  //If w has only one son, it must be v
  assert(w->getNumResolvents()>1 || *(w->res.begin())==v);
#endif
  if(w->getNumResolvents()==1) return;

  set<ProofNode*>::iterator it, it2;
  num_dup++;
#ifdef CHECK
  assert(v->getAnt1()==w || v->getAnt2()==w);
#endif
  //Clone w
  ProofNode* x=new ProofNode();
  x->setId(graph.size());
  for(size_t j=0;j<w->clause.size();j++) x->clause.push_back(w->clause[j]);

  x->pivot=w->pivot;
  x->ant1=w->ant1;
  x->ant2=w->ant2;
  x->type=w->type;

  if(x->ant1!=NULL && x->ant2!=NULL)
  {
    //w antecedents gain x as resolvent
    x->ant1->addResolvent(x);
    x->ant2->addResolvent(x);
  }

  for(it=w->res.begin();it!=w->res.end();)
  {
    //Keep v
    if((*it)->id!=v->id)
      //Move other resolvents to copy while updating antecedents
    {
      if((*it)->ant1==w) (*it)->ant1=x;
      if((*it)->ant2==w) (*it)->ant2=x;
      x->addResolvent((*it));
      it2=it; it++;
      w->removeResolvent(*it2);
    }
    else
      it++;
  }
  //Add new node to proof graph
  graph.push_back(x);

  if(graph.size()>SIZE_BIT_VECTOR)
  {
    cerr << "GRAPH TOO LARGE" << endl;
    assert(false);
  }
#ifdef CHECK
  assert(graph[x->id]==x);
  assert(w->getNumResolvents()==1);
#endif
}

//Input: clause id
//Output: clone (not cloning resolvents though)
ProofNode* ProofGraph::cloneProofNode(clauseid_t id)
{
  ProofNode* w=graph[id];
  assert(w!=NULL);

  //New node
  ProofNode* x=new ProofNode();
  x->id=graph.size();

  //Copy clause content to x
  for(size_t j=0;j<w->clause.size();j++) x->clause.push_back(w->clause[j]);

  //Update x info (not info for interpolation at the moment)
  x->pivot=w->pivot;
  x->ant1=w->ant1;
  x->ant2=w->ant2;
  x->type=w->type;

  //Add new node to proof graph
  graph.push_back(x);
  num_dup++;

  if(graph.size()>SIZE_BIT_VECTOR)
  {
    cerr << "# Error: Number of nodes exceeded limit of " << SIZE_BIT_VECTOR <<  endl;
    exit( 1 );
  }

  return x;
}

// Input: a non root node with multiple resolvents
// Split clause with multiple resolvents creating one node for each resolvent besides the first
void ProofGraph::splitClause(clauseid_t id)
{
  ProofNode*w=graph[id];
#ifdef CHECK
  assert(w->res.size()>0);
#endif
  if(w->res.size()==1) return;

  set<ProofNode*>::iterator it, it2;
  ProofNode* x;

  it=w->res.begin();
  it++;
  //Node keeps first resolvent
  for(;it!=w->res.end();)
  {
    //New node x
    x=cloneProofNode(w->id);

    //Update w antecedents
    if(w->ant1!=NULL && w->ant2!=NULL)
    {
      //w antecedents gain x as resolvent
      x->ant1->res.insert(x);
      x->ant2->res.insert(x);
    }

    if((*it)->ant1==w) (*it)->ant1=x;
    if((*it)->ant2==w) (*it)->ant2=x;
    x->res.insert((*it));
    it2=it; it++; w->res.erase(it2);

    assert(x->res.size()==1);
    assert(graph[x->id]==x);
  }
  assert(graph[w->id]->res.size()==1);
}

//Output: a proof tree corresponding to the proof graph
//NB: due to splitting it might be necessary to visit a node more than once
void ProofGraph::treefyProofGraph()
{
  /*	if ( verbose() )
	{
	cout << "# Treefying proof graph" << endl;
	}*/

  vector<clauseid_t>q;
  ProofNode* n;
  clauseid_t c;

  q.push_back(root);
  do
  {
    c=q.back();
    n=graph[c];
    assert(n!=NULL);
    q.pop_back();

    //Split node if has multiple resolvents
    if(n->res.size()>1 && n->ant1!=NULL && n->ant2!=NULL)
    {
      //cout << "Clause " << n->id << " has " << n->res.size() << " resolvents" << endl;
      splitClause(n->id);
    }

    //Enqueue antecedents not visited
    if(n->ant1!=NULL) q.push_back(n->ant1->id);
    if(n->ant2!=NULL) q.push_back(n->ant2->id);
  }
  while(!q.empty());
}

// Remove redundant pieces of the proof graph
//TODO implement destructor for ProofNodeFly
//returns number of redundant nodes removed
int ProofGraph::cleanProofGraph()
{
  // Visit proof graph from root via DFS
  vector<ProofNode*> q;
  q.push_back(graph[root]);
  int counter=0;

  // Determine the reachable part of the graph
  while(!(q.empty()))
  {
    ProofNode* node=q.back();
    // Remove node
    q.pop_back();
    // Node not yet visited
    if(!(visited[node->id]))
    {
      if(node->ant1!=NULL || node->ant2!=NULL)
      {
	//Enqueue antecedents
	if(node->ant1!=NULL)
	  q.push_back(node->ant1);
	if(node->ant2!=NULL)
	  q.push_back(node->ant2);
      }
      //Mark node as visited
      visited[node->id]=true;
    }
  }

  // Remove the unreachable part of the graph
  for(size_t i=0;i<graph.size();i++)
  {
#ifdef CHECK
    assert(!(visited[i] && graph[i]==NULL));
#endif
    if(!visited[i])
      if(graph[i]!=NULL)
      {
	removeNode(i);
	counter++;
	//cout << "Node " << i << " not reachable anymore has been removed" << endl;
	//assert(false);
      }
  }
  // Visited nodes vector
  visited.reset();
  return counter;
}

//Remove a node from the graph
void ProofGraph::removeNode(clauseid_t vid)
{
  ProofNode* v=graph[vid];
  assert(v!=NULL);

  //Remove v from the list of its antecedents resolvents
  ProofNode* ant1=v->ant1;
  ProofNode* ant2=v->ant2;
  if(ant1!=NULL || ant2!=NULL)
  {
    if(ant1!=NULL)
    {
      //cout << ant1->res.size() << endl;
      ant1->res.erase(v);
    }
    if(ant2!=NULL)
    {
      //cout << ant2->res.size() << endl;
      ant2->res.erase(v);
    }
  }
  //Remove v from its resolvents antecedents
  for(set<ProofNode*>::iterator it=v->res.begin();it!=v->res.end(); it++)
  {
    if((*it)->ant1==v) (*it)->ant1=NULL;
    if((*it)->ant2==v) (*it)->ant2=NULL;
  }
  v->ant1=NULL;
  v->ant2=NULL;
  //Remove interpolant, if any
  if(v->partial_interp!=NULL)
  {
    //delete(v->partial_interp);
    v->partial_interp=NULL;
  }
  //Free memory
  delete v;
  //Remove v
  graph[vid]=NULL;
}

// Remove a subtree radicated in a node v from the graph
void ProofGraph::removeTree( clauseid_t vid )
{
#ifdef CHECK
  assert( graph[ vid ] != NULL );
  assert( graph[ vid ]->res.size( ) == 0 );
#endif
  //Go on removing nodes with 0 resolvents
  //Visit graph from root keeping track of edges and nodes
  std::deque< clauseid_t > q;

  ProofNode * n;
  clauseid_t c;

  q.push_back( vid );
  do
  {
    c = q.front( );
    q.pop_front( );
#ifdef CHECK
    assert( (size_t)c < graph.size( ) );
#endif
    //Node not visited yet
    if( !visited2[ c ] )
    {
      n = graph[ c ];
#ifdef CHECK
      assert( n != NULL );
#endif
      //Mark node as visited
      visited2[ c ] = true;
      //remove node if no more resolvents present
      if( n->res.size( ) == 0 )
      {
	if( n->ant1 != NULL )
	  q.push_back( n->ant2->id );
	if( n->ant2 != NULL )
	  q.push_back( n->ant1->id );

	removeNode( n->id );
      }
    }
  }
  while( !q.empty( ) );
  visited2.reset( );
}

// Collapses a deduced node with its red/green/magenta antecedents into a magenta node
// returns true if the node has been magentified
bool ProofGraph::magentification( clauseid_t nid )
{
  assert( config.produce_inter != 0 );

  ProofNode * n = graph[ nid ];
#ifdef CHECK
  assert( n );
#endif
  // Red and green nodes become magenta
  if( n->type == CLAAXIOM 
   || n->type == CLALEMMA )
  {
    n->type = CLAMAGENTA;
    assert( n->partial_interp );
    return true;
  }
  // NB We can have blu nodes containing light variables, due to preprocessing: they become magenta
  else if( n->type == CLAORIG )
  {
    for( size_t i = 0 ; i < n->clause.size( ) ; i++ )
    {
      if( light_vars.find( var( n->clause[ i ] ) ) != light_vars.end( ) )
      {
	n->type = CLAMAGENTA;
	return true;
      }
    }
  }
  // Orange nodes become magenta and antecedents are removed
  else if( n->ant1 != NULL 
        && n->ant2 != NULL )
  {
    clause_type ty1 = n->ant1->type;
    clause_type ty2 = n->ant2->type;

    // Both antecedents are leaves
    if( ( ty1 == CLALEMMA || ty1 == CLAAXIOM || ty1 == CLAMAGENTA ) 
     && ( ty2 == CLALEMMA || ty2 == CLAAXIOM || ty2 == CLAMAGENTA ) )
    {
      // Remove resolution step
      n->ant1->res.erase( n );
      n->ant2->res.erase( n );
      // If an antecedent has no more resolvents, remove it
      if( n->ant1->res.size( ) == 0 )
	removeNode( n->ant1->id );
      if( n->ant2->res.size( ) == 0 )
	removeNode( n->ant2->id );

      // Update n
      n->type = CLAMAGENTA;
      n->ant1 = NULL;
      n->ant2 = NULL;

      assert( n->partial_interp == NULL );
      n->partial_interp = partialInterpolantWithNelsonOppen( n );

      return true;
    }
  }
  return false;
}

// Magentifies the graph iteratively
// TODO find better algorithm
void ProofGraph::systematicMagentification( )
{
  bool done;
  do
  {
    done = false;
    for( size_t i = 0 ; i < graph.size( ) ; i ++ )
      if( graph[ i ] != NULL )
	done = done || magentification( i );
  }
  while( done );
}

// Input: A set of light variables
// Output: Initializes the graph lightVar set with the set of light variables
void ProofGraph::initializeLightVarSet( set< Var > & lightV )
{
  light_vars.swap( lightV );
  lightV.clear( );
}

#endif
