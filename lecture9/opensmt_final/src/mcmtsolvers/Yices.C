/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Yices.h"
#include <string.h>

void 
Yices::DeclareInitial ( Enode * initial 
                      , const vector< Enode * > & initial_vars
		      , const vector< ArrayVar * > & array_vars
                      )
{
  stringstream ss;
  ss << "(initial ";
  for ( size_t i = 0; i < initial_vars.size( ) ; i ++ )
  {
    ss << initial_vars[ i ] << "::nat ";
    for ( size_t a = 0 ; a < array_vars.size( ) ; a ++ )
    {
      ss << ARR_INST( array_vars[ a ]->enode, initial_vars[ i ] ) 
	 << "::" 
	 << typeToYices_( array_vars[ a ]->getType( )->get3rd( ) )
	 << " ";
    }
  }
  ss << ")::bool "; 
  initial->yicesPrint( ss );

  define_( ss.str().c_str( ) );
}

void
Yices::Declare( const char * name
              , Snode * arg_sort
	      , Snode * ret_sort )
{
  // First of all declare internally
  declare_( name, arg_sort, ret_sort );
  // Yices, as defined here, supports only
  // variable declarations (not functions)
  assert( arg_sort == NULL );

  char buf[ 256 ];
  if( ret_sort->isNat( ) )
    sprintf( buf, "%s::nat", name );
  else if ( ret_sort->isInt( ) )
    sprintf( buf, "%s::int", name );
  else
    mcmt_error2( "Can't declare sort in yices: ", ret_sort );

  define_( buf );
}

void 
Yices::DeclareIndexVar( const char * ind_var
                      , const vector< Enode * > & z_variables 
		      , const vector< ArrayVar * > & array_vars
		      )
{
  // initialize this variable in yices
  // declare the variable
  char buf[ 256 ];
  sprintf( buf, "%s::nat", ind_var );
  define_( buf );

  // makes this variable different from others
  for ( size_t j = 0 ; j < z_variables.size( ) ; j++)
  {
    stringstream ss;
    ss <<  "(not (= " << ind_var << " " << z_variables[ j ] << "))";
    assert_( ss.str( ).c_str( ) );
  }
  
  // declare the arrays with this new variable
  for ( size_t j = 0 ; j < array_vars.size( ) ; j ++ )
  {
    Snode * type = array_vars[ j ]->getType( )->get3rd( );

    sprintf( buf
	   , ARR_FMT3
	   , array_vars[ j ]->getName( )
	   , ind_var
	   , typeToYices_( type ).c_str( ) );

    define_( buf );
 
    // check if the array is global
    if ( array_vars[ j ]->global 
      && z_variables.size( ) > 0 )
    {
      stringstream ss;
      ss <<  "(= " 
	 << ARR_INST( array_vars[ j ]->enode, ind_var ) 
	 << " "
	 << ARR_INST( array_vars[ j ]->enode, z_variables.back( ) ) 
	 << ")";
      assert_( ss.str( ).c_str( ) );
    }
  }
}

void 
Yices::DefineType( char * n, int l, int u )
{ 
  char buf[ 256 ];
  sprintf( buf, "(define-type %s (subrange %d %d))", n, l, u ); 

  int r = yicesl_read( ctx, buf );
  
  // print message passed to yices
  if(config.verbosity > 2 )
  {
    cerr << "YICES INPUT: " << buf << endl;
  }
  // check for errors
  if (!r)
  {
    // yices returned an error.
    char* err = yicesl_get_last_error_message( );
    assert( err );
    cerr << "YICES ERROR: \n\tINPUT: " << buf << "\n\tERROR: " << err << endl;
  }
}

void  
Yices::Push( ) 
{
  if(config.verbosity > 2 )
  {
    cerr << "YICES PUSH" << endl;
  }
#if USE_LITE
  yicesl_read(ctx, const_cast< char * >( "(push)" ) );
#else
  yices_push( ctx );
#endif
}

void 
Yices::Pop( )
{
  if(config.verbosity > 2 )
  {
    cerr << "YICES POP" << endl;
  }
#if USE_LITE
  yicesl_read(ctx, const_cast< char * >( "(pop)" ) );
#else
  yices_pop( ctx );
#endif
}

lbool 
Yices::Check( )
{
  calls++;

  if(config.verbosity > 2 )
  {
    cerr << "YICES CHECK";
  }
#if USE_LITE
  yicesl_read(ctx, const_cast< char * >( "(check)" ) );
  int res = yicesl_inconsistent(ctx);
  if (res) {
    if(config.verbosity > 2 )
    {
      cerr << "--> INCONSISTENT" << endl;
    }
    Comment(" --> INCONSISTENT");
    return l_False;
  }
  else {
    if(config.verbosity > 2 )
    {
      cerr << "--> CONSISTENT" << endl;
    }
    Comment(" --> CONSISTENT");
    return l_True;
  }
#else
  lbool res = yices_check( ctx );
  if ( res == l_true )  return l_True;
  if ( res == l_false )  return l_False;
  return l_Undef;
#endif
}

void  
Yices::Assert( Enode * e, const bool neg )
{
  assert( e );
  // Assert the string representing the yices term
  stringstream ss;
  ss << "(assert ";
  if ( neg )
    ss << "(not ";
  e->yicesPrint( ss );
  if ( neg )
    ss << ")";
  ss << ")";

  // Print message passed to yices
  if(config.verbosity > 2 )
  {
    cerr << "YICES INPUT: " << ss.str( ) << endl;
  }
  int r = yicesl_read( ctx, const_cast< char * >( ss.str( ).c_str( ) ) );
  // check for errors
  if (!r)
  {
    // yices returned an error.
    char * err = yicesl_get_last_error_message( );
    assert( err );
    cerr << "YICES ERROR: \n\tINPUT: " << ss.str( ) << "\n\tERROR: " << err << endl;
  }
}

void  
Yices::Define( Node * n
             , vector< ArrayVar * > & array_vars )
{
  Formula * f = n->getFormula( );
  const vector< Enode * > & variables = f->getVariables( );

  assert( !variables.empty( ) );

  // now create the string to instantiate
  stringstream sse;
  if ( !n->isInvariant( ) )
  {
    sse << "(node[" << n->getId( ) << "_" << n->getRedefinition( ) << "] ";
  }
  if ( n->isInvariant( ) )
  {
    sse << "(inv[" << n->getId( ) << "_" << n->getRedefinition( ) << "] ";
  }
  for ( size_t i = 0 ; i < variables.size( ) ; i ++ )
  {
    sse << variables[ i ] << "::nat ";
    for ( size_t a = 0 ; a < array_vars.size( ) ; a ++ )
    {
      // assert( array_vars[ a ]->getType( )->get3rd( )->isNat( ) );
      sse << ARR_INST( array_vars[ a ]->enode, variables[ i ] ) 
	  << "::"
	  << typeToYices_( array_vars[ a ]->getType( )->get3rd( ) )
	  // nat" 
	  << " ";
    }
  }
  sse << ")::bool " << f;

  define_( sse.str( ).c_str( ) );
}

void  
Yices::Comment( const char * e )
{
  // assert the string representing the yices term
  stringstream ss;
  if ( !strcmp( name.c_str(), "yices_i" ) )
  {
    ss << ";i; " << e;
  }
  else
  {
    ss << ";; " << e;
  }

  // create the string
  string str = ss.str();

  int r = yicesl_read( ctx, const_cast< char * >( ss.str( ).c_str( ) ) );
  if (!r)
  {
    // yices returned an error.
    char* err = yicesl_get_last_error_message( );
    assert( err );
    cerr << "YICES ERROR: \n\tINPUT: " << str << "\n\tERROR: " << err << endl;
  }
  //delete str_for_yices;
}

void
Yices::Instantiate ( Node * n
                   , const vector< ArrayVar * > & array_vars
                   , const vector< Enode * > & variables
		   , const vector< unsigned > & order
		   , const bool negate )
{
  assert( order.size( ) <= variables.size( ) );
  // now create the string to instantiate
  stringstream ss;
  if ( !n->isInvariant( ) )
  {
    ss << "(node[" << n->getId( ) << "_" << n->getRedefinition( ) << "] ";
  }
  if ( n->isInvariant( ) )
  {
    ss << "(inv[" << n->getId( ) << "_" << n->getRedefinition( ) << "] ";
  }
  for ( size_t  i = 0 ; i < order.size( ) ; i ++ )
  {
    assert( order[i] < variables.size( ) );
    ss << variables[ order [ i ] ] << " ";
    for (size_t  a = 0 ; a < array_vars.size() ; a++ )
    {
      ss << ARR_INST( array_vars[ a ]->enode, variables[ order [ i ] ] ) 
	 << " ";
    }
  }
  ss << ")";

  //cerr << "Instantiating " << ss.str() << endl;
  assert_( ss.str( ).c_str( ), negate );
  //getchar();
}

void
Yices::InstantiateInitial ( const size_t                 av_positions
                          , const vector< ArrayVar * > & array_vars
			  , const vector< Enode * > &    vars
			  , unsigned *                   inst_vars 
			  )
{
  // Now create the string to instantiate
  stringstream ss;
  ss << "(initial ";
  for (size_t  i = 0; i < av_positions ; i++ )
  {
    assert( inst_vars[i] < vars.size() );
    ss << vars[ inst_vars [ i ] ] << " ";
    for (size_t  a = 0 ; a < array_vars.size( ) ; a++ )
    {
      ss << ARR_INST( array_vars[ a ]->enode, vars[ inst_vars [ i ] ] ) 
	 << " ";
    }
  }
  ss << ")";

  assert_( ss.str( ).c_str( ) );
  //getchar();
}

//
// Private shorthands for yices only
//

void  
Yices::define_( const char * e )
{
  assert( e );
  // assert the string representing the yices term
  stringstream ss;
  ss << "(define " << e << ")";

  // create the string
  string str = ss.str( );

  // print message passed to yices
  if(config.verbosity > 2 )
  {
    cerr << "YICES INPUT: " << str << endl;
  }
  int r = yicesl_read( ctx, const_cast< char * >( ss.str( ).c_str( ) ) );
  // check for errors
  if (!r)
  {
    // yices returned an error.
    char * err = yicesl_get_last_error_message( );
    assert( err );
    cerr << "YICES ERROR: \n\tINPUT: " << str << "\n\tERROR: " << err << endl;
  }
  //delete str_for_yices;
}

// This function is used to declare
// variables internally, if not already
// there -- notice that arg_sort is assumed 
// NULL
void 
Yices::declare_ ( const char * name
                , Snode * arg_sort
                , Snode * ret_sort )
{
  if ( arg_sort != NULL )
    mcmt_error2( "Received arg sort, but assumed none ", arg_sort );

  // Add variable only if not there before
  if ( !egraph.hasSymbol( name, arg_sort, ret_sort ) )
  {
    egraph.newSymbol( name
		    , arg_sort
		    , ret_sort );
  }
  assert( egraph.hasSymbol( name, arg_sort, ret_sort ) );
}


void
Yices::assert_( const char * e, const bool neg )
{
  assert( e );
  // assert the string representing the yices term
  stringstream ss;
  if ( neg )
    ss << "(assert (not " << e << "))";
  else
    ss << "(assert " << e << ")";

  // print message passed to yices
  if( config.verbosity > 2  )
  {
    cerr << "YICES INPUT: " << ss.str( ) << endl;
  }
  int r = yicesl_read( ctx, const_cast< char * >( ss.str( ).c_str( ) ) );
  // check for errors
  if (!r)
  {
    // yices returned an error.
    char* err = yicesl_get_last_error_message( );
    assert( err );
    cerr << "YICES ERROR: \n\tINPUT: " << ss.str( ) << "\n\tERROR: " << err << endl;
  }
}

string
Yices::typeToYices_ ( Snode * s )
{
       if ( s->isNat( ) )  return nat_str;
  else if ( s->isInt( ) )  return int_str;
  else if ( s->isReal( ) ) return real_str;
  else if ( s->isBool( ) ) return bool_str;
  else
  {
    stringstream ss;
    ss << s;
    return ss.str( );
  }

  return "";
}

#endif
