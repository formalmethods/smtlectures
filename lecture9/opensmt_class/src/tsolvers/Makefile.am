SUBDIRS = axdiffsolver bvsolver dlsolver emptysolver lrasolver ctsolver rdsolver

noinst_LTLIBRARIES = libtsolvers.la

INCLUDES=$(config_includedirs)

libtsolvers_la_SOURCES = TSolver.h THandler.C THandler.h
libtsolvers_la_LIBADD = axdiffsolver/libaxdiffsolver.la \
			bvsolver/libbvsolver.la \
			dlsolver/libdlsolver.la \
			lrasolver/liblrasolver.la \
			ctsolver/libctsolver.la \
			rdsolver/librdsolver.la \
			emptysolver/libemptysolver.la
