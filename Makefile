CC     = gcc
RACKET = racket
RM     = rm

runtime.o: runtime.c runtime.h
	$(CC) -arch x86_64 -march=x86-64 -c -g -std=c99 runtime.c

test: runtime.o
	$(RACKET) run-tests.rkt

clean:
	$(RM) -f *.o *.out *.exe *.s *~
