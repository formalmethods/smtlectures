/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#ifndef InvariantContainer_H
#define InvariantContainer_H

#include "Global.h"
#include "Egraph.h"
#include "AbstractSolver.h"
#include "Transition.h"
#include "Config.h"
#include "Node.h"


/* This class is used as a container for all the nodes generated
 * by the backward reachability procedure.
 * For now consists of two lists of States objects:
 *  - TBV (To Be Visited) is the list where a new node is inserted
 *  - AV (Already Visited) is the list where an old node already
 *    expanded with 'pre' is inserted */

class InvariantContainer
{
public:

  InvariantContainer ( Egraph & e_ 
                     , Config & c_ )
   : egraph           ( e_ )
   , config           ( c_ )
   , depth_search     ( false )
   , nodes            ( 0 )
   , nodes_tbv        ( 0 )
   , deleted_nodes    ( 0 )
   , depth            ( 0 )
  { }

  ~InvariantContainer () {
    // delete TBV list
    while( !toBeVisited.empty( ) )
    {
      delete toBeVisited.back();
      toBeVisited.pop_back( );
    }

    // delete AV list
    while( !alreadyVisited.empty( ) )
    {
      delete alreadyVisited.back( );
      alreadyVisited.pop_back( );
    }
  }

  Egraph &                 egraph;
  Config &                 config;            // Configure
  
  void                     addTbvNode      ( Node * );   // add a new node to the tbv list
  Node *                   getNextTbvNode  ( );          // get the next node to be visited
  bool                     hasMoreTbvNodes ( );          // returns true if there's at least one node to be visited
  void                     addAvNode       ( Node * );   // move the node from the list tvb to the av one
  void                     removeFromTbv   ( Node * );

  inline list < Node * > & getAvList       ( )       { return alreadyVisited; }
  inline list < Node * > & getTbvList      ( )       { return toBeVisited; }
  inline unsigned          getNodes        ( ) const { return nodes; }
  inline unsigned          getDeletedNodes ( ) const { return deleted_nodes; }
  inline unsigned          getDepth        ( ) const { return depth; }
  inline unsigned          getNodeNum      ( ) const { return nodes; }

  void                     clear           ( );

  void                     setStrategy     ( int );

  void                     setDeletedNodes ( const unsigned i ) { deleted_nodes = i; }

private:

  bool                  depth_search;    // depth first search?
  unsigned              nodes;           // number of the nodes in this container
  unsigned              nodes_tbv;       // number of the nodes in this container
  unsigned              deleted_nodes;   // number of deleted nodes in this container
  unsigned              depth;           // maximum depth
  list< Node * >        alreadyVisited;  // AV list
  list< Node * >        toBeVisited;     // TBV list
};

#endif // InvariantContainer_H

#endif
