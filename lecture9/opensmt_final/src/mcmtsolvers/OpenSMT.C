/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "OpenSMT.h"

void
OpenSMT::SetLogic( const logic_t l )
{
  ctx.SetLogic( l );
}

void
OpenSMT::SetOption( const char * key, const char * value )
{
  ctx.SetOption( key, value );
}

void 
OpenSMT::DeclareInitial ( Enode * initial 
                        , const vector< Enode * > & initial_vars
		        , const vector< ArrayVar * > & array_vars
                        )
{
  assert( initial );
  // Construct the list of terms to be used
  list< Enode * > var_list;
  for ( size_t i = 0; i < initial_vars.size( ) ; i ++ )
  {
    for ( size_t a = 0 ; a < array_vars.size( ) ; a ++ )
    {
      Enode * sel = egraph.mkSelect( array_vars[ a ]->enode
	                           , initial_vars[ i ] );
      var_list.push_front( sel );
    }
  }
  // This is actually a Define, as we declare
  // a shortcut for the initial state
  ctx.DefineFun( "initial"
               , egraph.cons( var_list )
	       , initial );

  if ( config.verbosity > 2 )
  {
    cerr << "OPENSMT INPUT: " 
	 << "initial " 
	 << egraph.cons( var_list )
	 << " " 
	 << initial 
	 << endl;
  }
}

void
OpenSMT::Declare( const char * name
                , Snode * arg_sort
	        , Snode * ret_sort )
{
  assert( name );
  assert( arg_sort == NULL );
  assert( ret_sort );
  ctx.DeclareFun( name, arg_sort, ret_sort );

  if ( config.verbosity > 2 )
  {
    cerr << "OPENSMT INPUT: " 
	 << name
	 << " " 
	 << ret_sort 
	 << endl;
  }

  // Because it's natural number, we have 
  // to enforce that it's bigger than 0
  if ( ret_sort->isNat( ) )
  {
    Enode * var = egraph.mkVar( name );
    Enode * con = egraph.mkLeq( egraph.mkNum( "0" ), var );
    Assert( con );
  }
}

void 
OpenSMT::DeclareIndexVar( const char * ind_var
                        , const vector< Enode * > & z_variables 
		        , const vector< ArrayVar * > & array_vars
		        )
{
  assert( ind_var );
  // Declare variable in solver
  Declare( ind_var, NULL, sstore.mkNat( ) );

  Enode * var = egraph.mkVar( ind_var );

  if ( config.verbosity > 2 )
  {
    cerr << "OPENSMT INPUT: " 
	 << ind_var
	 << " " 
	 << sstore.mkNat( )
	 << endl;
  }

  // Say that this variable is different from all the others
  for ( size_t j = 0 ; j < z_variables.size( ) ; j ++ )
  {
    Assert( egraph.mkNot( egraph.mkEq( var, z_variables[ j ] ) ) );
  }
  
  if ( ! z_variables.empty( ) )
  {
    for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
    {
      if ( array_vars[ a ]->global )
      {
        Assert( egraph.mkEq( egraph.cons( egraph.mkSelect( array_vars[ a ]->enode , var ) , egraph.cons( egraph.mkSelect( array_vars[ a ]->enode , z_variables.back( ) ) ) ) ) );
      }
    }
  }
}

void 
OpenSMT::DefineType( char * n, int l, int u )
{ 
  assert( n );
  assert( 0 <= l );
  assert( l <= u );

  if ( config.verbosity > 2 )
    cerr << "OPENSMT INPUT: new type " << l << " <= " << n << " <= " << u << endl;

  Snode * s = ctx.mkSortVar( n );
  ctx.DeclareSubrange( s, l, u );
}

void  
OpenSMT::Push( ) 
{
  if ( config.verbosity > 2 )
    cerr << "OPENSMT PUSH" << endl;

  ctx.Push( );
}

void 
OpenSMT::Pop( )
{
  if ( config.verbosity > 2 )
    cerr << "OPENSMT POP" << endl;

  ctx.Pop( );
}

lbool 
OpenSMT::Check( )
{
  calls ++;

  if( config.verbosity > 2 )
    cerr << "OPENSMT CHECK";

  lbool res = ctx.CheckSAT( );

  if ( config.verbosity > 2 )
  {
    if ( res == l_False )
      cerr << "--> INCONSISTENT" << endl;
    else if ( res == l_True )
      cerr << "--> CONSISTENT" << endl;
    else
      mcmt_error( "weird answer from OpenSMT" );
  }

  return res;
}

void  
OpenSMT::Assert( Enode * e, const bool neg )
{
  assert( e );
  ctx.Assert( e, neg );

  if( config.verbosity > 2 )
  {
    Enode * lit = neg ? egraph.mkNot( e ) : e ;
    cerr << "OPENSMT INPUT: " << lit << endl;
  }
}

void  
OpenSMT::Define( Node * n
               , vector< ArrayVar * > & array_vars )
{
  assert( n );
  Formula * f = n->getFormula( );
  Enode * fe = f->getFormula( );
  const vector< Enode * > & variables = f->getVariables( );

  assert( !variables.empty( ) );

  // now create the string to instantiate
  stringstream sse;
  if ( !n->isInvariant( ) )
  {
    sse << "node[" << n->getId( ) << "_" << n->getRedefinition( ) << "]";
  }
  if ( n->isInvariant( ) )
  {
    sse << "inv[" << n->getId( ) << "_" << n->getRedefinition( ) << "]";
  }

  list< Enode * > var_list;
  for ( size_t i = 0; i < variables.size( ) ; i ++ )
  {
    var_list.push_front( variables[ i ] );
    for ( size_t a = 0 ; a < array_vars.size( ) ; a ++ )
    {
      Enode * sel = egraph.mkSelect( array_vars[ a ]->enode
	                           , variables[ i ] );
      var_list.push_front( sel );
    }
  }
  // This is actually a Define, as we declare
  // a shortcut for the node
  ctx.DefineFun( sse.str( ).c_str( )
               , egraph.cons( var_list )
	       , fe );

  if ( config.verbosity > 2 )
  {
    cerr << "OPENSMT INPUT: " 
         << sse.str( ) 
	 << " " 
	 << egraph.cons( var_list )
	 << " " 
	 << fe 
	 << endl;
  }
}

void  
OpenSMT::Comment( const char * e )
{
  assert( e );
}

void
OpenSMT::Instantiate ( Node * n
                     , const vector< ArrayVar * > & array_vars
                     , const vector< Enode * > &    variables
		     , const vector< unsigned > &   order
		     , const bool                   negate 
		     )
{
  assert( n );
  assert( order.size( ) <= variables.size( ) );
  // now create the string to instantiate
  stringstream ss;

  if ( !n->isInvariant( ) )
    ss << "node[" << n->getId( ) << "_" << n->getRedefinition( ) << "]";

  if ( n->isInvariant( ) )
    ss << "inv[" << n->getId( ) << "_" << n->getRedefinition( ) << "]";

  list< Enode * > var_list;
  for ( size_t i = 0 ; i < order.size( ) ; i ++ )
  {
    assert( order[ i ] < variables.size( ) );

    var_list.push_front( variables[ order[ i ] ] );

    for ( size_t a = 0 ; a < array_vars.size( ) ; a ++ )
    {
      Enode * sel = egraph.mkSelect( array_vars[ a ]->enode
	                           , variables[ order[ i ] ] );
      var_list.push_front( sel );
    }
  }

  Enode * e = ctx.mkFun( ss.str( ).c_str( ), egraph.cons( var_list ) );
  Assert( e, negate );
}

void
OpenSMT::InstantiateInitial ( const size_t                 av_positions
                            , const vector< ArrayVar * > & array_vars
			    , const vector< Enode * > &    vars
			    , unsigned *                   inst_vars 
			    )
{
  assert( inst_vars );
  list< Enode * > var_list;
  for ( size_t i = 0; i < av_positions ; i ++ )
  {
    assert( inst_vars[i] < vars.size() );
    for ( size_t a = 0 ; a < array_vars.size( ) ; a ++ )
    {
      Enode * sel = egraph.mkSelect( array_vars[ a ]->enode
	                           , vars[ inst_vars[ i ] ] );
      var_list.push_front( sel );
    }
  }

  Enode * e = ctx.mkFun( "initial", egraph.cons( var_list ) );
  Assert( e );
}

// Interpolation related functions
void
OpenSMT::AssertInt( Enode * e, const unsigned p )
{
  assert( e );
  assert( p != 0 );
  ctx.AssertPartition( e, p );
}

Enode *
OpenSMT::GetInt( const unsigned n )
{
  return ctx.GetInterpolant( n );
}

#endif
