/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Container.h"

void 
Container::addTbvNodes( vector < Node * > & preimages
                      , vector < Enode * > & candidate_invariants 
                      , bool print_history
                      , bool invariant_search 
                      , bool skip_declaration 
		      )
{
  for ( size_t i = 0 ; i < preimages.size( ) ; i++ )
  {
    addTbvNode ( preimages[ i ] , candidate_invariants , print_history , invariant_search , skip_declaration );
  }
}

void
Container::autoTestPrepare (  )
{

#ifdef PEDANTIC_DEBUG
  // check that all the nodes in the TBV list are deleted/covered/locked
  for ( list< Node * >::iterator it = toBeVisited.begin( )
      ; it != toBeVisited.end( )
      ; it++ )
  {
    assert( (*it)->isDeleted( ) || (*it)->isLocked( ) || (*it)->isCovered( ) );
  }
#endif

  // clear the TBV list ( memory is freed??? )
  toBeVisited.clear( );
  assert( toBeVisited.empty( ) );

  unsigned unsafes = 0;
  // add to the tbv list all the AV nodes not deleted/covered/locked
  cerr << "Nodes still alive:" << endl;
  for ( list< Node * >::iterator it = alreadyVisited.begin( )
      ; it != alreadyVisited.end( )
      ; it++ , unsafes++ )
  {
    if ( !(*it)->isDeleted( ) && !(*it)->isLocked( ) && !(*it)->isCovered( ) )
    {
#ifdef PEDANTIC_DEBUG
      (*it)->explored = false;
#endif
      cerr << " [" << (*it)->getId( ) << "] --> [" << unsafes << "] = ";
      
      (*it)->setUnsafe( unsafes );
      (*it)->setId( ++nodes );
      (*it)->clearCoveringParents( );
      (*it)->clearCoveredChildren( );
      (*it)->clearChildren( );
      toBeVisited.push_back( (*it) );
      
      (*it)->getLabel( )->yicesPrint( cerr );
      cerr << endl;
    
    }
  }

  // clear the TBV list ( memory is freed??? )
  alreadyVisited.clear( );
  assert( alreadyVisited.empty( ) );

  nodes++;

}

void 
Container::addTbvNode( Node * n 
                     , vector < Enode * > & candidate_invariants 
                     , bool print_history
                     , bool //invariant_search 
                     , bool skip_declaration 
		     )
{

  if ( !skip_declaration )
  {
    assert( n->getId( ) < 0 );
    // do not print the first node (it's the UNSAFE one)
    n->setId( nodes );
  }
  
  if (nodes && print_history && !n->isDeleted( ) )
  {
    cout << "node " << nodes << " = ";
    n->printHistory( );
    nodes_tbv++;
  }
  else
  {
    nodes_tbv = 1;
  }
  
  
  // keep also the list of all nodes!
  if ( config.abstraction_report )
  {
    if ( allNodes.find( n ) == allNodes.end( ) )
    {
      allNodes.insert( n ); 
    }
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
        // TODO: recode the list ordering
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
    toBeVisited.push_back(n);
  }
  

  nodes++;

  if ( config.global_invariant )
  {
    // add the node to the clusterizer
    clusterizer.addNode( n );
 
    // policy to call the candidate invariant generator routine
    if ( clusterizer.ready( ) )
    {
      // new invariant generator obj
      Invariant * inv_creator = new Invariant( egraph , clusterizer.getBiggest( ) ); 
      // get candidate invariants list
      if ( config.classic_invariant )
      {
        inv_creator->basic_guess( candidate_invariants );
      }
      if ( config.invariant_pattern )
      {
        inv_creator->pattern_guess( candidate_invariants );
      }
      delete inv_creator;
    }
  }
  
  
  printLists( );
}




Node * Container::getNextTbvNode(  )
{
  
  if ( toBeVisited.front( )->isDeleted( ) )
  {
    return toBeVisited.front( );
  }

  // covered node will not be explorated
  // untill they are covered
  for (list< Node * >::iterator it = toBeVisited.begin( )
      ; it != toBeVisited.end( )
      ; it++)
  {
    if ( (*it)->isCovered( ) || (*it)->isLocked( ) )
      continue;
      
    if ( config.verbosity > 1 )
    {
      cerr << "Extracting node " << (*it)->getId( ) << endl;
    }
    return (*it);
    
  }
  return NULL;
}

void Container::addAvNode( Node * n )
{
  alreadyVisited.push_back( n );
  printLists( );
}
 
void Container::removeFromTbv( Node * n )
{
  // remove the node from the TBV list
  toBeVisited.remove( n );
  printLists( );
}

bool Container::hasMoreTbvNodes (  )
{
  if ( toBeVisited.empty( ) )
    return false;

  // covered node will not be explorated
  // untill they are covered
  for (list< Node * >::iterator it = toBeVisited.begin( )
      ; it != toBeVisited.end( )
      ; it++)
  {
    if ( !(*it)->isCovered( ) && !(*it)->isDeleted( ) && !(*it)->isLocked( ) )
    {
      return true;
    }
  }

  return false;
}

void                     
Container::setStrategy ( int strategy )
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
Container::clear( )
{
  depth_search = false;
  nodes = 0;
  nodes_tbv = 0;
  deleted_nodes = 0;
  depth = 0;
  added_node = 0;
  
  alreadyVisited.clear();  // AV list
  toBeVisited.clear();     // TBV list
}

void
Container::removeFromAv( Node * n )
{
  assert( false );
//  cerr << "Removing node " << n->getId( ) << " from AV..." << endl;
  list< Node * >::iterator it = alreadyVisited.begin( );
  while ( it != alreadyVisited.end( ) )
  {
    if ( (*it)->getId( ) == n->getId( ) )
    {
//      cerr << "Node " << n->getId( ) << " removed from AV" << endl;
      it = alreadyVisited.erase( it );
    }
    else
    {
      it++;
    }
  }

  printLists( );
}

void
Container::printLists( )
{
  if ( config.verbosity > 1 )
  {
    cerr << "TBV:";
    for ( list< Node * >::iterator it = toBeVisited.begin( )
        ; it != toBeVisited.end( )
        ; it++ )
    {
      cerr << (*it)->getId( ) << "(" << (*it) << ")";
      if ( (*it)->isDeleted( ) )
        cerr << "(D)";
      if ( (*it)->isCovered( ) )
        cerr << "(C)";
      cerr << "\t";
    }
    cerr << endl;
    
    cerr << "AV:";
    for ( list< Node * >::iterator it = alreadyVisited.begin( )
        ; it != alreadyVisited.end( )
        ; it++ )
    {
      cerr << (*it)->getId( ) << "(" << (*it) << ")";
      if ( (*it)->isDeleted( ) )
        cerr << " (D)";
      if ( (*it)->isCovered( ) )
        cerr << "(C)";
      cerr << "\t";
    }
    cerr << "\n\n";
  }
}

bool
Container::existsTbvNode( Node * n )
{
  for ( list< Node * >::iterator it = toBeVisited.begin( )
      ; it != toBeVisited.end( )
      ; it++ )
  {
    if ( (*it)->getId( ) == n->getId( ) )
    {
      return true;
    }
  }
  return false;
}

bool
Container::existsAvNode( Node * n )
{
  for ( list< Node * >::iterator it = alreadyVisited.begin( )
      ; it != alreadyVisited.end( )
      ; it++ )
  {
    if ( (*it)->getId( ) == n->getId( ) )
    {
      return true;
    }
  }
  return false;
}


void
Container::outputDotty ( ofstream & of , unsigned highlighted ) {
  
  of << "digraph state_space_explored {" << endl;
  
  // print all non-deleted nodes with the transition and covering relation
  for ( set< Node * >::iterator it = allNodes.begin( )
      ; it != allNodes.end( )
      ; it++ )
  {
    if ( (*it)->isDeleted( ) )
    {
      // print the identifier
      of << (*it)->getId( ) << " [shape=circle,color=gray,style=filled];" << endl;
    }
    else if ( (*it)->isLocked( ) )
    {
      // print the identifier
      of << (*it)->getId( ) << " [shape=circle,color=blue];" << endl;
    }
    else
    {
      // print the identifier
      of << (*it)->getId( ) << " [shape=circle,color=";
      if ( (*it)->isCovered( ) )
        of << "gray";
      else
        of << "black";
     
      // highlight any node of interest
      if ( (*it)->identifier == highlighted )
        of << ",style=bold";
      
      of << "];" << endl;
    }
  }



  // transition relation
  for ( set< Node * >::iterator it = allNodes.begin( )
      ; it != allNodes.end( )
      ; it++ )
  {

    if ( !(*it)->isUnsafe( ) )
    {
      of << (*it)->getId( ) << " -> " << (*it)->getParent( )->getId( );
      of << " [label=\"t" << (*it)->getParentTransition( )->getId( );
      of << "_" << (*it)->getVar( FIRST );
      if ( (*it)->getVar( SECOND ) )
        of << "_" << (*it)->getVar( SECOND );
      of << "\"];" << endl;
    }
  }


  // covering relation
  for ( set< Node * >::iterator it = allNodes.begin( )
      ; it != allNodes.end( )
      ; it++ )
  {

    if ( (*it)->isCovered( ) )
    {
      set < Node * > covering = (*it)->getCoveringParents( );
      for ( set< Node * >::iterator c_it = covering.begin( )
          ; c_it != covering.end( )
          ; c_it++ )
      {
        of << (*it)->getId( ) << " -> " << (*c_it)->getId( ) << "[style=dashed,color=gray];" << endl;
      }
    }
  }

  
  // locking relation
  for ( set< Node * >::iterator it = allNodes.begin( )
      ; it != allNodes.end( )
      ; it++ )
  {
    if ( (*it)->isCovered( ) )
    {
      set < Node * > locked = (*it)->getLockedChildren( );
      for ( set< Node * >::iterator c_it = locked.begin( )
          ; c_it != locked.end( )
          ; c_it++ )
      {
        of << (*c_it)->getId( ) << " -> " << (*it)->getId( ) << "[style=dashed,color=blue];" << endl;
      }
    }
  }


  of << "}" << endl;

}


void
Container::outputLog ( ofstream & of , bool only_alive ) {
  // print all non-deleted nodes with the transition and covering relation
  for ( set< Node * >::iterator it = allNodes.begin( )
      ; it != allNodes.end( )
      ; it++ )
  {
    if ( (*it)->isDeleted( ) )
      continue;
    if ( only_alive && ( (*it)->isCovered( ) || (*it)->isLocked( ) ) )
      continue;

    // print the identifier
    of << (*it)->getId( ) << " = ";
    (*it)->getLabel( )->yicesPrint( of );
    of << endl;
  }
}



#ifdef PEDANTIC_DEBUG
void
Container::checkNodes( )
{
  for ( list < Node * >::iterator it = alreadyVisited.begin( )
      ; it != alreadyVisited.end( )
      ; it++ )
  {
    (*it)->checkLabel( );
    (*it)->checkCovering( );
    (*it)->checkDescendants( );
    if ( (*it)->isLocked( ) )  (*it)->checkLockedNode( );
    if ( !(*it)->isDeleted( ) && !(*it)->isCovered( ) )
    {
      (*it)->checkParents( (*it) );
    }
  }
  for ( list < Node * >::iterator it = toBeVisited.begin( )
      ; it != toBeVisited.end( )
      ; it++ )
  {
    (*it)->checkLabel( );
    (*it)->checkCovering( );
    (*it)->checkDescendants( );
    if ( (*it)->isLocked( ) )  (*it)->checkLockedNode( );
    if ( !(*it)->isDeleted( ) && !(*it)->isCovered( ) )
    {
      (*it)->checkParents( (*it) );
    }
  }
  for ( set < Node * >::iterator it = allNodes.begin( )
      ; it != allNodes.end( )
      ; it++ )
  {
    (*it)->checkLabel( );
    (*it)->checkCovering( );
    (*it)->checkDescendants( );
    if ( (*it)->isLocked( ) )  (*it)->checkLockedNode( );
    if ( !(*it)->isDeleted( ) && !(*it)->isCovered( ) )
    {
      (*it)->checkParents( (*it) );
    }
  }
}
#endif

#endif
