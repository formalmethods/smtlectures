/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#include "AbstractSolver.h"
#include "yices_c.h"
#include "yicesl_c.h"

#define USE_LITE 1

class Yices : public AbstractSolver
{
public:

  Yices ( const char * name
        , Config & config 
	, Egraph & egraph
	)
    : AbstractSolver( name, config, egraph )
    // Type cast initialization
    , nat_str  ( "nat" )
    , int_str  ( "int" )
    , real_str ( "real" )
    , bool_str ( "bool" )
    // Yices context
    , ctx      ( NULL )
  { 
#if USE_LITE
    ctx = yicesl_mk_context( );
    char log_name [ 32 ];
    char out_name [ 32 ];
    sprintf( log_name, "%s-log.ys", name ); 
    sprintf( out_name, "%s-out.ys", name ); 
    if ( config.log )
    {
      yicesl_enable_log_file( const_cast< char * >( log_name ) );
      yicesl_set_output_file( const_cast< char * >( out_name ) );
    }
    else
    {
      yicesl_set_output_file( const_cast< char * >( "/dev/null" ) );
    }
#else
    ctx = yices_mk_context( ); 
#endif
    assert( ctx );
    
  }

  ~Yices( )
  {
#if USE_LITE
    yicesl_del_context( ctx );
#else
    yices_del_context( ctx );
#endif
  }

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

private:

  // Private shorthand for yices only
  void         define_           ( const char * );
  void         assert_           ( const char *, const bool = false );
  void         declare_          ( const char *, Snode *, Snode * );

  string       typeToYices_      ( Snode * );

  // yices_expr   enodeToYicesExpr_ ( Enode * );   // Translate expressions
  // string       enodeToString_    ( Enode * );   // Translate expressions

  const char * nat_str;
  const char * int_str;
  const char * real_str;
  const char * bool_str;

#if USE_LITE
  yicesl_context               ctx;           // Yices context
#else
  yices_context                ctx;           // Yices context
#endif
  map< enodeid_t, yices_expr > enode_to_expr; // Translate only once
};
