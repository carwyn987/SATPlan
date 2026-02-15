# General CC flags exported to sub-Makefiles
CCFLAGS = -O3  -DNDEBUG -O1 -fpermissive -std=c++11 -m32
export CCFLAGS

# Link flags
LFLAGS = 
ifeq ($(OSTYPE), linux)
  LFLAGS = -lfl
endif
ifeq ($(OSTYPE), posix)
  LFLAGS = -lfl
endif

# Special defined variables
DFLAGS =
ifeq ($(OSTYPE), cygwin)
  DFLAGS = -DUSENAMESPACESTD
endif
export DFLAGS

# Turn on or off code for control, learning, variable ordering
#BBFLAGS = -DBBCTRL
#BBFLAGS = -DBBLEARN
#BBFLAGS = -DBBVARORDER

CC = g++ $(BBFLAGS) $(DFLAGS) $(CCFLAGS)
V = 45

.SUFFIXES: .o .cpp .c

OBJS = bbpddl.tab.o lex.yy.o graphplan.o utilities.o hash.o planner.o dummy.o graph2wff.o control.o justify.o tim.o learn.o verify.o bbio.o sat_solver.o

blackbox: $(OBJS)
	cd compact; make
	cd satz-rand; make
	cd walksat; make
	cd zchaff; make
	$(CC) compact/*.o satz-rand/*.o walksat/*.o $(OBJS) $(LFLAGS) zchaff/libsat.a -lm -o $@ 

graphplan: y.tab.o lex.yy.o graphplan.o utilities.o hash.o planner.o dummy.o
	$(CC) lex.yy.o y.tab.o hash.o utilities.o graphplan.o planner.o dummy.o -o graphplan

all:
	make clean; make; make install; make clean

y.tab.o: y.tab.h graphplan.h 

graph2wff.o: graphplan.h interface.h

hash.o: graphplan.h

graphplan.o: graphplan.h interface.h graphplan.cpp
	$(CC) -c -DVERSION=\"$(V)\" graphplan.cpp

utilities.o: graphplan.h

planner.o: graphplan.h interface.h

justify.o: justify.h graphplan.h

tim.o: tim.h graphplan.h

learn.o: tim.h learn.h graphplan.h

bbio.o: learn.h graphplan.h

verify.o: verify.h learn.h graphplan.h

sat_solver.o: sat_solver.cpp
	$(CC) -c sat_solver.cpp

lex.yy.cpp: bbpddl.l
	flex  -olex.yy.cpp bbpddl.l 

bbpddl.tab.cpp: bbpddl.y lex.yy.cpp
	bison -d bbpddl.y -o bbpddl.tab.cpp

lex.yy.o: graphplan.h bbpddl.tab.hpp control.h lex.yy.cpp

bbpddl.tab.o: graphplan.h control.h

.cpp.o:
	$(CC) $(CFLAGS) -c $< 

install: blackbox
	cp blackbox $(HOME)/bin/`cputype`/blackbox
	cp extract $(HOME)/bin/`cputype`
	cp Run-bb $(HOME)/bin/`cputype`

clean:
	rm -f *.o blackbox lex.yy.cpp bbpddl.tab.cpp bbpddl.tab.hpp bbpddle.output
	cd satz-rand; make clean
	cd walksat; make clean
	cd compact; make clean
	cd zchaff; make clean


