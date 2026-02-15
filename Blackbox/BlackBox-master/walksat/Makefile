SHELL = /bin/sh
# CCFLAGS set in top level shell
CC = g++ $(CCFLAGS)
VERSION = 36

walksat.o: walksat.cpp
	$(CC) -c -DHuge walksat.cpp

clean:
	rm -f walksat *.o

