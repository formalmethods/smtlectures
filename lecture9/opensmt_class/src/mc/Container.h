/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef Container_H
#define Container_H

#include "Global.h"
#include "Egraph.h"
#include "AbstractSolver.h"
#include "Transition.h"
#include "Config.h"
#include "Node.h"
#include "Clusterizer.h"
#include "Invariant.h"

#define   INVARIANT_SEARCH_PERIOD  2

/* This class is used as a container for all the nodes generated
 * by the backward reachability procedure.
 * For now consists of two lists of States objects:
 *  - TBV (To Be Visited) is the list where a new node is inserted
 *  - AV (Already Visited) is the list where an old node already
 *    expanded with 'pre' is inserted */

class Container
{
public:

  Container ( Egraph & e_ 
            , Config & c_ )
    : egraph           ( e_ )
    , config           ( c_ )
    , depth_search     ( false )
    , nodes            ( 0 )
    , nodes_tbv        ( 0 )
    , deleted_nodes    ( 0 )
    , depth            ( 0 )
    , added_node       ( 0 )
  { }

  ~Container ( ) 
  {
    // delete TBV list
    while( !toBeVisited.empty( ) )
    {
      assert( toBeVisited.back( ) );
      delete toBeVisited.back( );
      toBeVisited.pop_back( );
    }

    // delete AV list
    while( !alreadyVisited.empty( ) )
    {
      assert( alreadyVisited.back( ) );
      delete alreadyVisited.back( );
      alreadyVisited.pop_back( );
    }

    // delete Deleted list
    while( !deleted.empty( ) )
    {
      assert( deleted.back( ) );
      delete deleted.back( );
      deleted.pop_back( );
    }
  }

  Egraph &                 egraph;            // Pointer to Egraph
  Config &                 config;            // Configure
  
  void                     addTbvNode                  ( Node * , vector < Enode * > & , bool , bool , bool = false );   // add a new node to the tbv list
  void                     addTbvNodes                 ( vector < Node * > & , vector < Enode * > & , bool , bool , bool = false );   // add a vector of nodes to the tbv list
//  void                     addTbvNodeIfNotPresent      ( Node * );   // add a new node to the tbv list (used only with abstraction)
  Node *                   getNextTbvNode              (  );          // get the next node to be visited
  bool                     hasMoreTbvNodes             (  );          // returns true if there's at least one node to be visited
  void                     addAvNode                   ( Node * );   // move the node from the list tvb to the av one
  void                     removeFromTbv               ( Node * );
  void                     removeFromAv                ( Node * );

  bool                     existsTbvNode               ( Node * );
  bool                     existsAvNode                ( Node * );

  inline list < Node * > & getAvList                   (  )       { return alreadyVisited; }
  inline list < Node * > & getTbvList                  (  )       { return toBeVisited; }
  inline set< Node * > &   getAllNodes                 (  )       { return allNodes; }
  inline unsigned          getNodes                    (  ) const { return nodes; }
  inline unsigned          getDeletedNodes             (  ) const { return deleted_nodes; }
  inline unsigned          getCoveredNodes             (  ) const { return covered_nodes; }
  inline unsigned          getDepth                    (  ) const { return depth; }
  inline unsigned          getNodeNum                  (  ) const { return nodes; }
                                                       
  void                     clear                       (  );
                                                       
  void                     setStrategy                 ( int );
                                                       
  void                     setDeletedNodes             ( const unsigned i ) { deleted_nodes = i; }
  
  void                     setCoveredNodes             ( const unsigned i ) { covered_nodes = i; }
  
  /* Lazy abstraction */
  void                     addDeletedNode              ( Node * n ) { deleted.push_back( n ); }

  
  /* Dotty output */
  void                     outputDotty                 ( ofstream & , unsigned = 0 );
  void                     outputLog                   ( ofstream & , bool = false );

  /* Auto Test */
  void                     autoTestPrepare             (  );

#ifdef PEDANTIC_DEBUG
  void                     checkNodes                  (  );
#endif

private:

  bool                     depth_search;               // depth first search?
  unsigned                 nodes;                      // number of the nodes in this container
  unsigned                 nodes_tbv;                  // number of the nodes in this container
  unsigned                 deleted_nodes;              // number of deleted nodes in this container
  unsigned                 covered_nodes;              // number of covered nodes in this container
  unsigned                 depth;                      // maximum depth
  list< Node * >           alreadyVisited;             // AV list
  list< Node * >           toBeVisited;                // TBV list
  set< Node * >            allNodes;                      // All the nodes (used only for Lazy Abstraction)                                                       
  void                     printLists( );              // used for debug (print the list of tbv nodes and av nodes)

  /* Lazy abstraction */
  list< Node * >           deleted;

  /* Invariant generation */                           
                                                       
  Clusterizer              clusterizer;                // used to cluster the nodes
  unsigned                 added_node;                 // force the invariant generation every force_inv_search node inserted

};

#endif // Container_H
