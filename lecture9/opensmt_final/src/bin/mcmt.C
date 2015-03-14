/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Egraph.h"
#include "MCMTContext.h"
#include "MC.h"

#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <iostream>

namespace mcmt {

void        catcher            ( int );
extern bool stop;

} // namespace mcmt

extern int  mcmt1set_in          ( FILE * );
extern int  mcmt1parse           ( );
extern int  mcmt2set_in          ( FILE * );
extern int  mcmt2parse           ( );
MCMTContext * parser_ctx;

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

int main( int argc, char * argv[] )
{
  mcmt::stop = false;
  // Allocates Command Handler
  MCMTContext context( argc, argv );
  // Catch SigTerm, so that it answers even on ctrl-c
  signal( SIGTERM, mcmt::catcher );
  signal( SIGINT , mcmt::catcher );
  // Initialize pointer to context for parsing
  parser_ctx = &context;
  const char * filename = argv[ argc - 1 ];
  assert( filename );
  FILE * fin = NULL;
  // Print help if required
  if ( strcmp( filename, "--help" ) == 0
    || strcmp( filename, "-h" ) == 0 )
  {
    context.getConfig( ).printHelp( );
    return 0;
  }
  // File must be last arg
  if ( strncmp( filename, "--", 2 ) == 0
    || strncmp( filename, "-", 1 ) == 0 )
    mcmt_error( "input file must be last argument" );
  // Make sure file exists
  if ( (fin = fopen( filename, "rt" )) == NULL )
    mcmt_error( "can't open file" );

  if ( context.getConfig( ).verbosity > 0 )
  {
    const char * tool_string = "MCMT 2.0";
    const int len_pack = strlen( tool_string );
    const char * site = "http://homes.dsi.unimi.it/~ghilardi/mcmt/";
    const int len_site = strlen( site );

    cerr << "#" << endl
         << "# -------------------------------------------------------------------------" << endl
         << "# " << tool_string;

    for ( int i = 0 ; i < 73 - len_site - len_pack ; i ++ )
      cerr << " ";

    cerr << site << endl
	 << "# Compiled with gcc " << __VERSION__ << " on " << __DATE__ << endl
         << "# -------------------------------------------------------------------------" << endl
         << "#" << endl;
  }

  if ( context.getConfig( ).verbosity > 1 )
    cerr << "Main::Parsing BEGINS" << endl;

  // Parse
  mcmt1set_in( fin );      // Use mcmt2set_in( fin ); for new parser
  mcmt1parse ( );          // Use mcmt2parse ( );     for new parser

  if ( context.getConfig( ).verbosity > 1 )
    cerr << "Main::Parsing ENDS" << endl;

  fclose( fin );

  if ( context.getConfig( ).verbosity > 1 )
    cerr << "Main::Execution BEGINS" << endl;

  if ( context.getConfig( ).generate_invariants )
  {
    // Artificially adds command for invariants generation
    context.addGenerateInvariants( );
  }
  else
  {
    // Artificially adds command for checking safety
    context.addCheckSafety( );
  }

  // Execute
  const int ret = context.execute( );
  
  if ( context.getConfig( ).verbosity > 1 )
    cerr << "Main::Execution ENDS with return value " << ret << endl;

  context.PrintResult( );

  return ret;
}

namespace mcmt {

void catcher( int sig )
{
  switch (sig)
  {
    case SIGINT:
    case SIGTERM:
      if ( stop )
      {
	if ( parser_ctx->getConfig( ).verbosity > 0 )
	{
	  fprintf( stderr, "\n# ----------+--------------------------+----------+------------+-----------\n");
	  fprintf( stderr, "#\n");
	}
	parser_ctx->PrintResult( );
	exit( 1 );
      }
      stop = true;
      break;
  }
}

} // namespace mcmt

#else

#include <iostream>

int main( ) { std::cerr << "Sorry, I don't work with SMTCOMP flag enabled :-/" << std::endl; return 0; }

#endif // #ifndef SMTCOMP
