/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef Formula_H
#define Formula_H

#include <algorithm>
#include "Global.h"
#include "Egraph.h"
#include "Enode.h"

/* This class is an "encapsulating" class for Enodes.
   Contains data structures used to speed up preimages
   computation, fix point checks and other operations
   performed by MCMT.
*/

class Formula
{
public:
  Formula ( 
         Egraph  & e
       , Enode   * f )
    : egraph             ( e )
    , formula            ( f )
    , literals_ready     ( false )
    , variables_ready    ( false )
    , variables_max_id   ( 0 )
    , arrays_max_id      ( 0 )
    , matrix_ready       ( false )
    , has_disjunctions   ( false )
  { }
  
  ~Formula ( )
  { }

  vector < Enode * > &            getLiterals( ); 
  vector < Enode * > &            getVariables( ); 
  vector < Enode * > &            getArrays( ); 
  Enode *                         getValue( Enode * , Enode * , bool = false ); // [ VAR_ID ][ ARRAY_ID ]
  inline Enode *                  getFormula( ) { assert( formula ); return formula; }
  unsigned                        getVarMaxId( );
  void                            print ( ostream & );
  void                            printMatrix ( ostream & );
  inline bool                     hasDisjunctions( ) { return has_disjunctions; }

  inline friend ostream &  operator<<( ostream & os, Formula * f )    { assert( f ); f->print( os ); return os; }

private:
  
  Egraph &                        egraph;       // Egraph
  Enode *                         formula;      // This formula
  vector < Enode * >              literals;     // literals of the formula
  vector < Enode * >              variables;    // variables of the formula
  vector < Enode * >              arrays;       // arrays of the formula
  vector < vector < Enode * > >   matrix;       // matrix of the constants
  
  bool                            literals_ready;   // tells if the data structures of literals are ready
  bool                            variables_ready;  // tells if the data structures of variables are ready
  unsigned                        variables_max_id;
  unsigned                        arrays_max_id;
  bool                            matrix_ready;     // tells if the matrix is ready
  bool                            has_disjunctions; // tells if the formula contains disjunctions

  void                            retrieveVars( );
  void                            retrieveLits( );
  void                            buildMatrix( );
  void                            checkDisjunctions( );
};

#endif // Formula_H
