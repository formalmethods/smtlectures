/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Node.h"

void
Node::setLabel ( Enode * f )
{
  if ( label )
    delete label;

  label = new Formula ( egraph , f );
}

void
Node::setAbstractLabel ( Enode * f )
{
  if ( abstract_label )
    delete abstract_label;

  abstract_label = new Formula ( egraph , f );
}

void
Node::setParent ( Node * p )
{
  parent = p;
  depth = parent->depth+1;
}

Enode *
Node::getVar ( int n_var )
{
  assert( n_var == FIRST || n_var == SECOND );
  return ( n_var == FIRST ) ? v1 : v2 ;
}

void
Node::setVar ( int n_var , Enode * v )
{
  assert( n_var == FIRST || n_var == SECOND );
  ( n_var == FIRST ) ? v1 = v : v2 = v;
}

void
Node::setParentTransition ( Transition * t )
{
  assert(t);
  parent_transition = t;
}

void
Node::printHistory (  )
{
  if ( !is_unsafe ) {
    cout << "[t" << parent_transition->getId( ) << "_" << v1;
    if ( v2 ) 
    {
      cout << "_" << v2;
    }
    cout << "]" ;
    parent->printHistory( );
  }
  else {
    cout << "[" << unsafe << "]" << endl;
  }
}

Enode *
Node::getValue ( Enode * v , Enode * a , bool global_variable ) {
  return label->getValue( v , a , global_variable );
}

Enode *
Node::getAbstractValue ( Enode * v , Enode * a , bool global_variable ) {
  return abstract_label->getValue( v , a , global_variable );
}

bool
Node::hasChild( Node * n )
{
  if ( descendants.find( n ) != descendants.end( ) )
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool
Node::hasParent( Node * n )
{
  if ( parents.find( n ) != parents.end( ) )
  {
    return true;
  }
  else
  {
    return false;
  }
}

// every node that has first as ancestors and does not have last as descendant must be deleted!
void
Node::refineKinship ( Node * last )
{
  assert( last );

  if ( id == last->getId( ) )
  {
    // I am the last!
    return;
  }

//  cerr << "Refine kinship on node " << id << " (" << this << ")" << endl;
  
  if ( deleted )
  {
    // I am deleted
    return;
  }

  if ( !isOnPath( last ) )
  {
    // auto-destruction!!
    if ( id >= 0 && !deleted )
    {
      cout << "node " << id << " has been deleted [ancestor refined, path does not end with node " << last->getId( ) << "]" << endl;
    }
    deleted = true;
  }
}


// every node that has first as has first as ancestors and last as descendant must be deleted!
void
Node::deleteHierarchy(  )
{

  for ( set< Node * >::iterator it = descendants.begin( )
      ; it != descendants.end( )
      ; it++ )
  {
    if ( !(*it)->isDeleted( ) )
    {
      (*it)->Delete( );
    }
    (*it)->deleteHierarchy(  );
  }
  
  // auto-destruction!!
  if ( id >= 0 && !deleted )
  {
    cout << "node " << id << " has been deleted [ancestor deleted]" << endl;
  }
  deleted = true;
}

void
Node::printCoveringRelation( )
{
  cerr << "\nNode " << id << " (" << this << "), ";
  label->getFormula( )->yicesPrint( cerr );
  cerr << "\n\tis covered by: ";
  for ( set< Node * >::iterator it = covering_parents.begin( )
      ; it != covering_parents.end( )
      ; it ++ )
  {
    cerr << "\n\t\t" << (*it)->getId( ) << " (" << (*it) << ")";
    if ( (*it)->isDeleted( ) )
      cerr << "(D)";
    if ( (*it)->isCovered( ) )
      cerr << " (C)";
    cerr << "\t";
    (*it)->getLabel( )->yicesPrint( cerr );
  }
  
  cerr << "\n\tcovers: ";
  for ( set< Node * >::iterator it = covered_children.begin( )
      ; it != covered_children.end( )
      ; it ++ )
  {
    cerr << (*it)->getId( ) << " (" << (*it) << ")\t";
  }
  
  cerr << endl << endl;
  
}

void
Node::informCoveringParentsImFree( )
{
  for ( set< Node * >::iterator it = covering_parents.begin( )
      ; it != covering_parents.end( )
      ; it++ )
  {
    (*it)->removeCoveredChild( this );
  }
}

void
Node::addChild ( Node * n )
{
  assert( n );
  children.insert( n );
  descendants.insert( n );
  if ( !is_unsafe )
  {
    parent->addDescendant( n );
  }
}

void
Node::addChildren ( vector < Node * > & c )
{
  if ( c.empty( ) )
  {
    return;
  }

  // call the same function up to the first unsafe!
  children.insert( c.begin( ) , c.end( ) );
  descendants.insert( c.begin( ) , c.end( ) );
  if ( !is_unsafe )
  {
    parent->addDescendants( c );
  }
}

void
Node::addDescendant ( Node * n )
{
  assert( n );
  descendants.insert( n );
  if ( !is_unsafe )
  {
    parent->addDescendant( n );
  }
}

void
Node::addDescendants ( vector < Node * > & c )
{
  if ( c.empty( ) )
  {
    return;
  }

  // call the same function up to the first unsafe!
  descendants.insert( c.begin( ) , c.end( ) );
  if ( !is_unsafe )
  {
    parent->addDescendants( c );
  }
}


void
Node::setCaseVar( unsigned v , unsigned c )
{
  if ( cases.empty ( ) )
  {
    cases.resize( label->getVariables( ).size( ) , 0 );
  }
  assert( v < cases.size( ) );
  cases[ v ] = c;
}

void
Node::setCases( vector < Enode * > & j_vars , vector < unsigned > & j_cases )
{
  assert( j_vars.size( ) == j_cases.size( ) );
  if ( cases.empty ( ) )
  {
    cases.resize( MAX_INDEX_VARS , 0 );
  }
  assert( j_vars.size( ) <= cases.size( ) );

  for ( size_t v = 0 ; v < j_vars.size( ) ; v++ )
  {
    assert( j_vars[ v ]->getMcmtId( ) < cases.size( ) );
    cases[ j_vars[ v ]->getMcmtId( ) ] = j_cases[ v ];
  }
}

void
Node::lockChildren(  )
{
  // every child of n is locked!
  for ( set< Node * >::iterator it = descendants.begin( )
      ; it != descendants.end( )
      ; it++ )
  {
    
    // if there is a covered children, this children is no more covered, it is just locked
    if ( (*it)->isCovered( ) )
    {
      (*it)->setCovered( false );
      (*it)->informCoveringParentsImFree( );
      (*it)->clearCoveringParents( );
    }

    // it can be the case that one node is already locked...
    if ( !(*it)->isLocked( ) )
    {
      (*it)->lock( );
      locked_children.insert( (*it) );
    }
  }
}

void
Node::printChildren( )
{
  cerr << "Node " << id << " (" << this << ") has these children:";
  for ( set< Node * >::iterator it = children.begin( )
      ; it != children.end( )
      ; it ++ )
  {
    cerr << (*it)->getId( ) << " (" << (*it) << ")\t";
  }
  cerr << endl << endl;
}

void
Node::printDescendants( )
{
  cerr << "Node " << id << " (" << this << ") has these descendants:";
  for ( set< Node * >::iterator it = descendants.begin( )
      ; it != descendants.end( )
      ; it ++ )
  {
    cerr << (*it)->getId( ) << " (" << (*it) << ")\t";
  }
  cerr << endl << endl;
}

bool
Node::isOnPath ( Node * n ) {
  
  if ( id == n->getId( ) )
  {
    return true;
  }
  
  // search if we are on the path ending with last !
  for ( set< Node * >::iterator it = descendants.begin( )
      ; it != descendants.end( )
      ; it++ )
  {
    if ( (*it)->getId( ) == n->getId( ) )
    {
      return true;
    }
  }
  return false;
}

#ifdef PEDANTIC_DEBUG
/* CHECKING FUNCTIONS! */

// check that all ancestors of this node are still alive and not covered
void
Node::checkParents( Node * n ) {
  if ( n->getId( ) != id && !n->isDeleted( ) && !n->isLocked( ) && ( covered || deleted ) ) {
    cerr << "\n\nERROR!!! ---------------------------------" << endl;
    cerr << " node " << n->getId( ) << " has node " << id << " as ancestor, but this node has been";
    if ( covered ) cerr << " covered ";
    if ( deleted ) cerr << " deleted ";
    cerr << endl << endl;

    // print the sequences of nodes and transitions from n to this node
    while ( !n->isUnsafe( ) )
    {
      cerr << " n" << n->getId( ) << " <--t" << n->getParentTransition( )->getId( ) << "(";
      cerr << n->getVar( FIRST );
      if ( n->getVar( SECOND ) )
      {
        cerr << "," << n->getVar( SECOND );
      }
      cerr << ")--";
      n = n->getParent( );
    }
    cerr << endl << endl;

    assert( false );
  }
  if ( parent )
  {
    parent->checkParents( n );
  }
}

// check that the covering relation is correct
void
Node::checkCovering( ) {
  if ( covered )
  {
    // this node is covered.
    // it must have at least one node in the list of parent_covering
    if ( covering_parents.empty( ) )
    {
      cerr << "\n\nERROR!!! ---------------------------------" << endl;
      cerr << " n" << id << " is set as covered, but has no covering parents!";
      cerr << endl << endl;
      assert( false );
    }
    
    // every node that covers this node must be alive
    for ( set < Node * >::iterator it = covering_parents.begin( )
        ; it != covering_parents.end( )
        ; it++ )
    {
      if ( (*it)->isDeleted( ) )
      {
        cerr << "\n\nERROR!!! ---------------------------------" << endl;
        cerr << " n" << id << " is covered by " << (*it)->getId( ) << " but this node has deleted!";
        this->printCoveringRelation( );
        cerr << endl << endl;
        assert( false );
      }
    }
    
    // if A covers B, B must be inside A's list of covered children
    for ( set < Node * >::iterator it = covering_parents.begin( )
        ; it != covering_parents.end( )
        ; it++ )
    {
      set < Node * > covered_by_these_parents = (*it)->getCoveredChildren( );
      if ( covered_by_these_parents.find( this ) == covered_by_these_parents.end( ) )
      {
        cerr << "\n\nERROR!!! ---------------------------------" << endl;
        cerr << " n" << id << " is covered by n" << (*it)->getId( ) << " but n" << (*it)->getId( ) << " does not have n" << id << " in the list of covered children!";
        cerr << endl << endl;
        assert( false );
      }
    }
  }
  else
  {
    // this node is not covered
    // the list of parents covering must be empty
    if ( !covering_parents.empty( ) )
    {
      cerr << "\n\nERROR!!! ---------------------------------" << endl;
      cerr << " n" << id << " is set as NOT covered, but has " << covering_parents.size( ) << " covering parents:" << endl;
      for ( set < Node * >::iterator it = covering_parents.begin( )
          ; it != covering_parents.end( )
          ; it++ )
      {
        cerr << "\t n" << (*it)->getId( ) << endl;
      }
      cerr << endl << endl;
      assert( false );
    }
  }
  
  // if A covers B, A must be inside B's list of covering parents
  for ( set < Node * >::iterator it = covered_children.begin( )
      ; it != covered_children.end( )
      ; it++ )
  {
    set < Node * > covering_parents_this_child = (*it)->getCoveringParents( );
    if ( covering_parents_this_child.find( this ) == covering_parents_this_child.end( ) )
    {
      cerr << "\n\nERROR!!! ---------------------------------" << endl;
      cerr << " n" << id << " has n" << (*it)->getId( ) << " in the list of covered children, but n" << (*it)->getId( ) << " does not have n" << id << " in the list of covering parents!";
      cerr << endl << endl;
      assert( false );
    }
  }
}

void
Node::checkLabel( )
{
  // formulas with disjunctions are allowed!  
  return;

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( label->getFormula( ) );
  egraph.initDup1( );
  while ( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );
    unprocessed_enodes.pop_back( );
    if ( egraph.isDup1( e ) )
      continue;

    Enode * arg_list;
    if ( e->isAnd( ) )
    {
      for ( arg_list = e->getCdr( )
	  ; !arg_list->isEnil( )
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	if ( !egraph.isDup1( arg ) )
	  unprocessed_enodes.push_back( arg );
      }
    }
    else
    {
      if ( !e->isLit( ) )
      {
        cerr << "\n\nERROR!!! ---------------------------------" << endl;
        cerr << "Node n" << id << " has an unprocessable label: ";
        label->getFormula( )->yicesPrint( cerr );
        cerr << endl << endl;
        assert( false );
      }
      //literals.push_back( e );
    }

    egraph.storeDup1( e );
  }
  egraph.doneDup1( );

}


void
Node::checkDescendants( )
{
  // every children is also a descendant!
  for ( set < Node * >::iterator it = children.begin( )
      ; it != children.end( )
      ; it++ )
  {
    if ( (*it)->isDeleted( ) ) continue ;
    if ( descendants.find( (*it) ) == descendants.end( ) )
    {
      cerr << "\n\nERROR!!! ---------------------------------" << endl;
      cerr << "Node n" << id << " has node n" << (*it)->getId( ) << " as children but not as descendant!";
      cerr << endl << endl;
      assert( false );
    }
  }
  
  // every children is also a descendant!
  for ( set < Node * >::iterator it = children.begin( )
      ; it != children.end( )
      ; it++ )
  {
    if ( (*it)->getParent( )->getId( ) != id )
    {
      cerr << "\n\nERROR!!! ---------------------------------" << endl;
      cerr << "Node n" << id << " has node n" << (*it)->getId( ) << " as children but, this node has a different parent (n" << (*it)->getParent( )->getId( ) << ")!";
      cerr << endl << endl;
      assert( false );
    }
  }
}


void
Node::checkLockedNode( )
{
  // a locked node must have a covered parent and all the nodes
  // between it and the covered parent must be locked

  // go towards the unsafe and stop when a covered parent is found!
  
  if ( deleted ) return;

  if ( is_unsafe ) return;

  // recursive function!

  if ( !parent->isLocked( ) && !parent->isCovered( ) )
  {
    cerr << "\n\nERROR!!! ---------------------------------" << endl;
    cerr << "Node n" << id << " is locked but its parent (node " << parent->getId( ) << ") is neither locked nor covered!";
    cerr << endl << endl;
    assert( false );
  }

  if ( parent->isLocked( ) && parent->isCovered( ) )
  {
    cerr << "\n\nERROR!!! ---------------------------------" << endl;
    cerr << "Node " << parent->getId( ) << " is locked and covered!";
    cerr << endl << endl;
    assert( false );
  }

  if ( parent->isLocked( ) )
    parent->checkLockedNode( );

}


#endif

#endif
