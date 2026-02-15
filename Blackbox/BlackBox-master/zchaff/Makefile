#CC = CC
CC = g++
cc = gcc

#SHELL = /bin/csh

# Use CCFLAGS instead, inherited from main Makefile
#CFLAGS = -g
#CFLAGS = -O3 -pg 
#CFLAGS = -O3
#CFLAGS = -DNDEBUG -O3 

MFLAGS = 
ifeq (solaris, $(OSTYPE))
  MFLAGS = -D_NEED_REDEFINE_RAND_MAX_
endif
ifeq (cygwin, $(OSTYPE))
  MFLAGS = -DWIN32
endif

# Following seemingly harmless code breaks this Makefile UNLESS your
# shell is csh!  Go figure!!!
#  ifneq (posix, $(OSTYPE))
#  ifneq (linux, $(OSTYPE))
#  echo "WARNING This thing are not tested under os other than Linux and Solaris"
#  endif
#  endif


RANLIB = ranlib
AR = ar

.SUFFIXES: .o .cpp .c

HEADERS = asap_base.h asap_clsgen.h asap_common.h asap_dbase.h asap_solver.h

# Don't actually build asap!
# SOLVER_SRCS = sat_solver.cpp 
# SOLVER_OBJS = $(SOLVER_SRCS:.cpp=.o)

LIB_SRCS =  asap_utils.cpp asap_solver.cpp asap_dbase.cpp asap_c_wrapper.cpp  asap_cpp_wrapper.cpp
LIB_OBJS = $(LIB_SRCS:.cpp=.o)

#TARGET:   $(SOLVER_OBJS) libsat.a

TARGET: libsat.a
	echo "built zchaff libsat.a"
	# Don't actually build asap!
	# $(CC) $(LINKFLAGS) $(CCFLAGS) $(MFLAGS) -o asap $(SOLVER_OBJS) libsat.a

$(LIB_OBJS): $(HEADERS) Makefile

libsat.a:   $(LIB_OBJS)
	@rm -f libsat.a
	$(AR) cr libsat.a $(LIB_OBJS)
	$(RANLIB) libsat.a
.c.o:
	$(cc) $(CCFLAGS) $(MFLAGS) -c $<
.cpp.o:
	$(CC) $(CCFLAGS) $(MFLAGS) -c $< 


clean:
	rm -f *.o libsat.a asap
