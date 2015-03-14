/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef Clusterizer_H
#define Clusterizer_H

#include "Global.h"
#include "Egraph.h"
#include "AbstractSolver.h"
#include "Transition.h"
#include "Config.h"
#include "Node.h"

/* This class is used as a container for all the nodes generated
 * by the backward reachability procedure, used by all the thread
 * discovering invariants. */

class Clusterizer
{
public:

  Clusterizer ( )
  : biggest ( 0 )
  , card_biggest( 0 )
   { }
  
  ~Clusterizer ( ) { }


  void                     addNode      ( Node * );   // add a new node to the tbv list
  list <Node *> &          getCluster   ( unsigned n );    // get the next node to be visited
  list <Node *> &          getBiggest   ( );          // get the biggest cluster
  unsigned                 getBiggestId ( ) { return biggest; }
  bool                     ready        ( );

private:

  size_t biggest;
  unsigned card_biggest;
  vector< list < Node * > > clusters;                 // the clusters of nodes

};

#endif // Clusterizer_H
