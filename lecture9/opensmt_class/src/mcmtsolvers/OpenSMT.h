/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#include "AbstractSolver.h"
#include "OpenSMTContext.h"

class OpenSMT : public AbstractSolverInt
{
public:

  OpenSMT( const char * name
         , Config &     config_ 
	 , Egraph &     egraph_
	 , SStore &     sstore_
	 , const bool   inv_gen_ = false
	 )
    : AbstractSolverInt ( name, config_, egraph_ )
    , ctx_p             ( new OpenSMTContext( config_, sstore_, egraph_ ) )
    , ctx               ( *ctx_p )
    , sstore            ( sstore_ )
    , inv_gen           ( inv_gen_ )
  { }

  ~OpenSMT( )
  {
    ctx.Exit( );
    delete ctx_p;
  }

  void     SetLogic           ( const logic_t );
  void     SetOption          ( const char *, const char * );

  void     DeclareInitial     ( Enode * 
                              , const vector< Enode * > & 
                              , const vector< ArrayVar * > & 
			      ); 
  
  void     DeclareIndexVar    ( const char *
                              , const vector< Enode * > & 
                              , const vector< ArrayVar * > & 
			      ); 
  
  void     Declare            ( const char *, Snode *, Snode * );
  void     DefineType         ( char *, int, int );
  void     Push               ( );
  void     Pop                ( );
  lbool    Check              ( );
  
  void     Assert             ( Enode *, const bool neg = false );
  
  void     Define             ( Node *, vector< ArrayVar * > & );
  
  void     Comment            ( const char * );

  void     Instantiate        ( Node *
                              , const vector< ArrayVar * > &
                              , const vector< Enode * > &
			      , const vector< unsigned > &
			      , const bool );

  void     InstantiateInitial ( const size_t 
                              , const vector< ArrayVar * > &
			      , const vector< Enode * > &
			      , unsigned * );

  // Interpolation related APIs

  void     AssertInt          ( Enode *, const unsigned );
  Enode *  GetInt             ( const unsigned );

private:

  OpenSMTContext *             ctx_p;
  OpenSMTContext &             ctx;
  SStore &                     sstore;
  const bool                   inv_gen;      
};
