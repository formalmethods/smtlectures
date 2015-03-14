noinst_LTLIBRARIES = libmcmt1parser.la

BUILT_SOURCES = mcmt1parser.cc mcmt1parser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=mcmt1
AM_LFLAGS = -olex.yy.c -Pmcmt1

libmcmt1parser_la_SOURCES = mcmt1parser.yy mcmt1lexer.ll
