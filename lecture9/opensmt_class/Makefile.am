SUBDIRS = src

bin_PROGRAMS = opensmt #mcmt

INCLUDES = $(config_includedirs)

opensmt_SOURCES = src/bin/opensmt.C
opensmt_LDFLAGS = 

#mcmt_SOURCES = src/bin/mcmt.C
#mcmt_LDFLAGS = ../yices/lib/libyices.a

LDADD = src/libopensmt.la -lgmpxx -lgmp
