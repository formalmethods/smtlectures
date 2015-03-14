/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "InvariantContainer.h"

void 
InvariantContainer::addTbvNode( Node * n ) 
{
 
  // do not print the first node (it's the UNSAFE one)
  n->setId( nodes );
  if ( nodes )
  {
    nodes_tbv++;
  }
  else
  {
    nodes_tbv = 1;
  }
  
  
  if ( !depth_search )
  { 
    // toBeVisited list is ordered!
    if (toBeVisited.size() == 0)
    {
      toBeVisited.push_back(n);
    }
    else
    {
      list< Node * >::iterator it = toBeVisited.begin();
      bool found = false;
      while ( !found && it != toBeVisited.end() ) {
        if ( (*it)->getMaxId() > n->getMaxId() || ((*it)->getMaxId() == n->getMaxId() && (*it)->getDepth() > n->getDepth()) )
          found = true;
        else
          it++;
      }
 
      if ( it == toBeVisited.end() )
        toBeVisited.push_back(n);
      else
        toBeVisited.insert(it, n);
    }
    
 
    // update depth
    if (n->getDepth( ) > depth)
      depth = n->getDepth( );
  }
  else
  {
    toBeVisited.push_front(n);
  }
  nodes++;
}

Node *
InvariantContainer::getNextTbvNode(  )
{
  // get the next node to be visited
  return toBeVisited.front( );
}

void
InvariantContainer::addAvNode( Node * n )
{
  // move the node from the list tvb to the av one
  // add the node to the AV list
  alreadyVisited.push_back( n );
}
 
void
InvariantContainer::removeFromTbv( Node * n )
{
  // remove the node from the TBV list
  toBeVisited.remove( n );
}

bool
InvariantContainer::hasMoreTbvNodes (  )
{
  return toBeVisited.size() > 0 ? true : false ; 
}

void                     
InvariantContainer::setStrategy ( int strategy )
{
  switch ( strategy ) {
    case DEPTH_FIRST_STRATEGY:
      depth_search = true;
    break;
    default:
      depth_search = false; 
  }
}

void
InvariantContainer::clear( )
{
  depth_search = false;
  nodes = 0;
  nodes_tbv = 0;
  deleted_nodes = 0;
  depth = 0;
  
  alreadyVisited.clear();  // AV list
  toBeVisited.clear();     // TBV list
}

#endif
