/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef TRANSITION_H
#define TRANSITION_H

#define BOTH 0

#include "Global.h"
#include "Egraph.h"
#include "Structures.h"

class Transition
{
public:

  struct Case;

  Transition( Egraph                & e_
            , SStore                & ss_
            , const int               id_
            , Enode *                 v1_
            , Enode *                 v2_
            , Enode *                 vj_
	    , Enode *                 g_
	    , vector< Enode * >       ug_           
            , vector< Case * >      & c_
            , bool                    gbl )
    : id                            ( id_ )
    , v1                            ( v1_ )
    , v2                            ( v2_ )
    , vj                            ( vj_ )
    , guard                         ( g_ )
    , new_var_x                     ( true )
    , new_var_y                     ( true )
    , new_var_xy                    ( true )
    , ready                         ( false )
    , preprocessed                  ( false )
    , identical_preprocessing_done  ( false )
    , abstracted                    ( false )
    , egraph                        ( e_ )
    , sstore                        ( ss_ )
    , global                        ( gbl )
  { 
    assert( vj );
    for ( size_t i = 0 ; i < ug_.size( ) ; ++ i )
      uguards.push_back( ug_[ i ] );
    for ( size_t i = 0 ; i < c_.size( ) ; ++ i )
      cases.push_back( c_[ i ] );
  }

  ~Transition( )
  {
    // Eliminate cases
    while( !cases.empty( ) )
    {
      delete cases.back( );
      cases.pop_back( );
    }
  }

  // Specific structure for a case
  struct Case
  {
    Case ( Enode *             c_
	 , vector< Enode * > & v_ )
    {
      assert( c_ );
      condition = c_;
      values = v_;
      identical = false;
    }

    ~Case ( ) { }


    Enode *           condition;              // Case condition
    vector< Enode * > values;                 // Value associated to the case
    bool identical;                           // true when this update does not change anything
  };
  
  Enode *                                     getVar                    ( int );     // returns a var of the transition
  int                                         getId                     ( ) { return id; };         // returns the id of the transition
  void                                        setId                     ( int );
  Enode *                                     getVj                     ( ) { return vj; }
  Enode *                                     getGuard                  ( ) { return guard; }
  vector< Enode * > &                         getUGuards                ( ) { return uguards; }
                                                                        
  // Getty function for cases                                           
  inline vector< Case * > &                   getCases                  ( ) { return cases; }
  Case *                                      getCase                   ( size_t );
  void                                        print                     ( ostream & );
  bool                                        avoidNewVariable          ( int );
  void                                        setNewVar                 ( int, bool );
  
  bool                                        getGlobal                 (  ) { return global; }
  void                                        setGlobal                 ( bool g ) { global = g; }

  vector < Enode * > &                        getUpdates                ( size_t , size_t );           // var index , case
  Enode *                                     getUpdate                 ( size_t , size_t , size_t );  // var index , case , array
  inline bool                                 isIdenticalUpdate         ( size_t c ) { /* assert( c < cases.size( ) ); */ return cases[ c ]->identical; }

  inline friend ostream &  operator<<( ostream & os, Transition * t )   { assert( t ); t->print( os ); return os; }

  void                                        identicalPreprocessing    ( vector < ArrayVar * > & );
  void                                        preprocess                (  );

  bool                                        getAbstracted             (  ) { return abstracted; }
  void                                        setAbstracted             ( bool a ) { abstracted = a; }

private:
  int	                                      id;                       // Unique identifier
  Enode *                                     v1;                       // First variable
  Enode *                                     v2;                       // Second variable
  Enode *                                     vj;                       // Variable used in lambda terms
  int                                         info_pre;                 // Value of PC before exec of trans
  int                                         info_post;                // Value of PC after exec of trans
  // int info_post_bounded;
  Enode *                                     guard;                    // Guard of the transition
  vector< Enode * >                           uguards;                  // uGuard of the transition
  vector< Case * >                            cases;                    // List of case conditions
  bool                                        new_var_x;                // Prevent an useless introduction of a new variable
  bool                                        new_var_y;                // Prevent an useless introduction of a new variable
  bool                                        new_var_xy;               // Prevent an useless introduction of a new variable
                                              
  void                                        uselessVariablePreprocess( );
  void                                        uguardPreprocess( );
                                              
  // this "cube" contains all the updates already instantiated
  // retrieve values using     [ Zn ID ] [ CASE ID ] [ ARRAY ID ]
  bool                                        ready;
  bool                                        preprocessed;
  bool                                        identical_preprocessing_done;
  vector < vector < vector < Enode * > > >    updates;
  void                                        setUpCube ( );

  bool                                        abstracted;               // says if the transition is "abstract", i.e. we abstract its preimage

  Egraph &                                    egraph;                   // Sort Store
  SStore &                                    sstore;                   // Sort Store

  bool                                        global;

};

#endif
