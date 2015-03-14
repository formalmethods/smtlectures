/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Clusterizer.h"

bool
Clusterizer::ready ( )
{
  if ( clusters.empty( ) )
  {
    return false;
  }
  else
  {
    return true;
  }
}

void 
Clusterizer::addNode ( Node * n )
{
  // the very first method is to cluster the nodes according
  // to the transition number used to generate the node
  
  if ( n->isUnsafe( ) )
  {
    return;
  }

  size_t t = n->getParentTransition()->getId();
  
  if ( clusters.empty() )
  {
    clusters.resize( t+1 );
  }
  
  // resize the array (if needed)
  if ( t >= clusters.size( ) )
  {
    clusters.resize( t+1 );
  }

  // insert the node in the right cluster
  clusters[ t ].push_back( n );

  // update the informations regarding the biggest
  if ( clusters[ t ].size() >= card_biggest )
  {
    biggest = t;
    card_biggest = clusters[ t ].size();
  }
}



list <Node *> & 
Clusterizer::getCluster ( unsigned n )
{
  assert( !clusters.empty() );
  assert ( n < clusters.size() );
  
  return clusters[ n ];
}



list <Node *> & 
Clusterizer::getBiggest ( )
{
  assert( !clusters.empty() );
  return clusters[ biggest ];
}

#endif
