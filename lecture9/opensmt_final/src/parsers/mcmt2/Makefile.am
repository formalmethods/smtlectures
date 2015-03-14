noinst_LTLIBRARIES = libmcmt2parser.la

BUILT_SOURCES = mcmt2parser.cc mcmt2parser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=mcmt2
AM_LFLAGS = -olex.yy.c -Pmcmt2

libmcmt2parser_la_SOURCES = mcmt2parser.yy mcmt2lexer.ll
