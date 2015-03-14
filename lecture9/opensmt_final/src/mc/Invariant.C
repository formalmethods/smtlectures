/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Invariant.h"

void
Invariant::basic_guess( vector < Enode * > & guessed )
{
  // very simple guessing: collect all the literals that are in common to every node in the list
  if ( nodes.size() < 2 )
  {
    return;
  }
  
  // search in the last FORMULAS elements of the list
  vector < Formula * > formulas;
  
  int c = 0;
  for( list< Node * >::reverse_iterator it = nodes.rbegin()
     ; it != nodes.rend() && c < FORMULAS
     ; ++it , c++ )
  {
    formulas.push_back( (*it)->getFormula() );
  }


  assert( formulas[ 0 ] != NULL );
  // explore all the literals
  vector < Enode * > & literals0 = formulas[ 0 ]->getLiterals( ); 
  // here we place literals to be conjunct
  list < Enode * > tbc;
  for ( size_t l0 = 0 ; l0 < literals0.size() ; l0++ )
  {
    bool found = false;

    assert( formulas[ 1 ] );
    vector < Enode * > & literals1 = formulas[ 1 ]->getLiterals( ); 
    for ( size_t l1 = 0; l1 < literals1.size( ) && !found; l1++ )
    {
      
      if ( literals0[ l0 ] == literals1[ l1 ] )
      {
        tbc.push_back( literals0[ l0 ] );
        continue;
      }
      else
      {
        // TODO: improve the search of invariants!
        continue;
      }
      
      
      Enode *lit0, *lit1;
      lit0 = literals0[ l0 ];
      lit1 = literals1[ l1 ]; 
      
      // check if we have the same literal in literals1 and literals0
      if ( lit0->isNot( ) == lit1->isNot( ) )
      {
        // both are negated or not
        // discard the negation (it there is one)
        if ( lit0->isNot( ) )
        {
          lit0 = lit0->get1st( );
          lit1 = lit1->get1st( ); 
        }
        
        if ( lit0->getCar( ) == lit1->getCar( ) )
        {
          // same car
        }
      }
    }
    guessed.push_back( egraph.mkAnd( egraph.cons( tbc ) ) );
  }
}



void
Invariant::pattern_guess( vector < Enode * > & guessed )
{
  
  // first we search for a literal like  (a[x] >< a[y])  -  the predicate!
  // then we search a literal like (x = i[x] + c)  -  the iterator!
  // last we search a literal like (p[x] = n)  -  the program counter!
  // the final invariant will be like
  //  (y < x) AND (y >= 0) AND (a[y] >< b[x]) AND (y = i[y]) AND (p[x] > n)

  if ( nodes.empty() )
  {
    return;
  }
  
  Enode *iterator = NULL, *pc = NULL, *n = NULL, *upperbound = NULL;

  // we start from the first formula of the list (should be easier)
  Formula *f = nodes.front( )->getFormula( );
  //cerr << "Starting from: " << f << endl;

  vector < Enode * > lits = f->getLiterals( );

  
  for ( size_t i = 0 ; i < lits.size( ) ; i++ )
  {

      
    // then we search a literal like (x = i[x])  -  the iterator! (we should search for i[x] + c...)
    if ( lits[ i ]->isNot( ) 
         && lits[ i ]->get1st( )->isEq( ) 
         && lits[ i ]->get1st( )->get1st( )->isSelect( )
         && egraph.hasSortIndex( lits[ i ]->get1st( )->get2nd( ) ) 
       )
    {
      iterator = lits[ i ]->get1st( )->get1st( )->get1st( );
      assert( iterator->hasSortArray( ) );
    }
    if ( lits[ i ]->isNot( ) 
         && lits[ i ]->get1st( )->isEq( ) 
         && lits[ i ]->get1st( )->get2nd( )->isSelect( )
         && egraph.hasSortIndex( lits[ i ]->get1st( )->get1st( ) ) 
       )
    {
      iterator = lits[ i ]->get1st( )->get2nd( )->get1st( );
      assert( iterator->hasSortArray( ) );
    }
    if ( !lits[ i ]->isNot( ) 
         && lits[ i ]->isEq( ) 
         && lits[ i ]->get1st( )->isSelect( )
         && egraph.hasSortIndex( lits[ i ]->get2nd( ) ) 
       )
    {
      iterator = lits[ i ]->get1st( )->get1st( );
      assert( iterator->hasSortArray( ) );
    }
    if ( !lits[ i ]->isNot( ) 
         && lits[ i ]->isEq( ) 
         && lits[ i ]->get2nd( )->isSelect( )
         && egraph.hasSortIndex( lits[ i ]->get1st( ) ) 
       )
    {
      iterator = lits[ i ]->get2nd( )->get1st( );
      assert( iterator->hasSortArray( ) );
    }

    for ( size_t j = 0 ; j < lits.size( ) && iterator ; j++ )
    {

      // now, we search a literal like (l[x] <= {t})  -  the bound of the array!
      if ( lits[ j ]->isNot( ) 
           && !lits[ j ]->get1st( )->isEq() 
           && lits[ j ]->get1st( )->get1st( )->isSelect( )
         )
      {
        upperbound = lits[ j ]->get1st( )->get1st( )->get1st( );
        assert( upperbound->hasSortArray( ) );
      }
      if ( lits[ j ]->isNot( ) 
           && !lits[ j ]->get1st( )->isEq( ) 
           && lits[ j ]->get1st( )->get2nd( )->isSelect( )
         )
      {
        upperbound = lits[ j ]->get1st( )->get2nd( )->get1st( );
        assert( upperbound->hasSortArray( ) );
      }
      if ( !lits[ j ]->isNot( ) 
           && !lits[ j ]->isEq( ) 
           && lits[ j ]->get1st( )->isSelect( )
         )
      {
        upperbound = lits[ j ]->get1st( )->get1st( );
        assert( upperbound->hasSortArray( ) );
      }
      if ( !lits[ j ]->isNot( ) 
           && !lits[ j ]->isEq( ) 
           && lits[ j ]->get2nd( )->isSelect( )
         )
      {
        upperbound = lits[ j ]->get2nd( )->get1st( );
        assert( upperbound->hasSortArray( ) );
      }

      
      
      for ( size_t k = 0 ; k < lits.size( ) && upperbound ; k++ )
      {
          
        // last we search a literal like (p[x] = n)  -  the program counter!
        if ( lits[ k ]->isNot( ) 
             && lits[ k ]->get1st( )->isEq( ) 
             && lits[ k ]->get1st( )->get1st( )->isSelect( )
             && lits[ k ]->get1st( )->get2nd( )->isConstant( ) 
           )
        {
          pc = lits[ k ]->get1st( )->get1st( )->get1st( );
          n = lits[ k ]->get1st( )->get2nd( );
          assert( pc->hasSortArray( ) );
          assert( n->isConstant( ) );
        }
        if ( lits[ k ]->isNot( ) 
             && lits[ k ]->get1st( )->isEq( ) 
             && lits[ k ]->get1st( )->get2nd( )->isSelect( )
             && lits[ k ]->get1st( )->get1st( )->isConstant( ) 
           )
        {
          pc = lits[ k ]->get1st( )->get2nd( )->get1st( );
          n = lits[ k ]->get1st( )->get1st( );
          assert( pc->hasSortArray( ) );
          assert( n->isConstant( ) );
        }
        if ( !lits[ k ]->isNot( ) 
             && lits[ k ]->isEq( ) 
             && lits[ k ]->get1st( )->isSelect( )
             && lits[ k ]->get2nd( )->isConstant( ) 
           )
        {
          pc = lits[ k ]->get1st( )->get1st( );
          n = lits[ k ]->get2nd( );
          assert( pc->hasSortArray( ) );
          assert( n->isConstant( ) );
        }
        if ( !lits[ k ]->isNot( ) 
             && lits[ k ]->isEq( ) 
             && lits[ k ]->get2nd( )->isSelect( )
             && lits[ k ]->get1st( )->isConstant( ) 
           )
        {
          pc = lits[ k ]->get2nd( )->get1st( );
          n = lits[ k ]->get1st( );
          assert( pc->hasSortArray( ) );
          assert( n->isConstant( ) );
        }
       


        // now build the candidate invariant!
        if ( iterator && pc && n && upperbound )
        {
        
          assert( iterator->hasSortArray() );
          assert( pc->hasSortArray() );
          assert( upperbound->hasSortArray() );
        
          // iterator, upperboud and pc must be different arrays
          if ( iterator == pc || iterator == n || iterator == upperbound )
            continue;
          if ( pc == n || pc == upperbound )
            continue;
          if ( iterator == upperbound )
            continue;
        
      
          /*
          if ( iterator )
            cerr << "FOUND iterator: " << iterator << endl;
          if ( pc )
            cerr << "FOUND pc: " << pc << endl;
          if ( n )
            cerr << "FOUND n: " << n << endl;
          if ( upperbound )
            cerr << "FOUND upperbound: " << upperbound << endl;
          */
      
          // build the candidate
          Enode * x = egraph.mkVar( "z0" );
          Enode * y = egraph.mkVar( "z1" );
          
          // BUILD THE FORMULA  (x < y)  /\  (y <= upperbound)  /\   (y = i[y])  /\  (p[x] > n)  /\  (arr1[?] >< arr2[?]) 
          list< Enode * > new_lits;
      
          // (x < y)
          new_lits.push_back(
            egraph.mkLt( egraph.cons( x , egraph.cons( y ) ) )
          );
          // (y <= upperbound[y])
          new_lits.push_back(
            egraph.mkLeq( egraph.cons( y , egraph.cons( egraph.mkSelect( upperbound , y ) ) ) )
          );
          // (pc[x] > n) 
          new_lits.push_back(
            egraph.mkGt( egraph.cons( egraph.mkSelect( pc , x ) , egraph.cons( n ) ) )
          );
      
          
          // now we conjunct the unused literals
          for ( size_t l = 0 ; l < lits.size() ; l++ )
          {
            if ( l != i && l != j && l != k )
            {
              
              // we add this literal only if it do not contains aritmetic constraints
              if ( ( lits[ l ]->isNot( ) && 
                     ( lits[ l ]->get1st( )->get1st( )->isPlus( ) || lits[ l ]->get1st( )->get1st( )->isMinus( )  ||
                       lits[ l ]->get1st( )->get2nd( )->isPlus( ) || lits[ l ]->get1st( )->get2nd( )->isMinus( ) ) )
                 || 
                   (  ( lits[ l ]->get1st( )->isPlus( ) || lits[ l ]->get1st( )->isMinus( )  ||
                        (lits[ l ]->getArity( ) > 1 && lits[ l ]->get2nd( )->isPlus( ) ) || ( lits[ l ]->getArity( ) > 1 && lits[ l ]->get2nd( )->isMinus( ) ) ) )
                 )
                 {
                   continue;
                 }
              
              new_lits.push_back( lits[ l ] );
            
              Enode * candidate = egraph.mkAnd( egraph.cons( new_lits ) );
              guessed.push_back( candidate );
              // candidate
              //cerr << "Candidate: " << candidate << endl << endl;
          

              // (y = i[y]) -- this can be omitted sometime, or can be (x = i[x])
              new_lits.push_back(
                egraph.mkEq( egraph.cons( y , egraph.cons( egraph.mkSelect( iterator, y ) ) ) )
              );
              candidate = egraph.mkAnd( egraph.cons( new_lits ) );
              guessed.push_back( candidate );
              new_lits.pop_back();
              new_lits.push_back(
                egraph.mkEq( egraph.cons( x , egraph.cons( egraph.mkSelect( iterator, x ) ) ) )
              );
              candidate = egraph.mkAnd( egraph.cons( new_lits ) );
              guessed.push_back( candidate );
              new_lits.pop_back();

            }
          }
          
          pc = NULL;
          n = NULL;
          upperbound = NULL;
          iterator = NULL;
        }
      }
    }
  }
/*
  cerr << "Candidate invariants" << endl;
  for ( size_t i = 0 ; i < guessed.size() ; i++)
  {
    cerr << guessed[ i ] << endl;
  }
  cerr << endl;
*/

}

#endif
