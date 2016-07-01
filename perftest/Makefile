# Usage:
#  "make test" or "make all" makes and runs all tests
#  "make clean" removes *.out and *.fidget
#  "make foo.out" makes foo.out from foo.hb or foo.lhb
TESTSOUT=ackermann.out cheney.out eq.out neq.out nmeq.out nmneq.out newboolperftest.out newbooltest.out recurse.out shalloweq.out shallowneq.out shallowrecurse.out basicloop.out eqloop.out neqloop.out monad1.out monad2.out monad3.out mutualrecursion.out area1.out md5demo.out
all: $(TESTSOUT)



TESTS=ackermann.fidget cheney.fidget eq.fidget neq.fidget nmeq.fidget nmneq.fidget newboolperftest.fidget newbooltest.fidget recurse.fidget shalloweq.fidget shallowneq.fidget shallowrecurse.fidget basicloop.fidget eqloop.fidget neqloop.fidget monad1.fidget monad2.fidget monad3.fidget mutualrecursion.fidget area1.fidget md5demo.fidget sortarea.fidget

OPTS=

ALB=../alb
ALBHPC=../alb-hpc
COMPCERT=../../../compcert2.0-hasp
CCOMP=$(COMPCERT)/ccomp
OTHER_FILES=$(COMPCERT)/test/fidget/harness.c $(COMPCERT)/runtime/gc/cheney.o
AS=gcc -m32 -c
LD=ld
OTHER_DEPS=$(ALB) $(COMPCERT)/ccomp
MORELIBS=$(COMPCERT)/test/fidget/harness.o $(COMPCERT)/runtime/gc/cheney.o
.PHONY: test
.SECONDARY:

tests : $(TESTS)

tests0 : $(TESTS:.fidget=.fidget0)
	
tests1 : $(TESTS:.fidget=.fidget1)

tests2 : $(TESTS:.fidget=.fidget2)

tests3 : $(TESTS:.fidget=.fidget3)

tests4 : $(TESTS:.figet=.fidget4)

test : tests
	./test.sh

%.fidgettest1: %.hb $(ALB)
	$(ALB) -i ../tests:. -f -F1cidl $< -o $*.fidgettest1

%.fidgettest2: %.hb $(ALB)
	$(ALB) -i ../tests:. -f -F2cidl $< -o $*.fidgettest2

%.fidgettest3: %.hb $(ALB)
	$(ALB) -i ../tests:. -f -F3cidl $< -o $*.fidgettest3

%.fidgettest4: %.hb $(ALB)
	$(ALB) -i ../tests:. -f -F3cidl $< -o $*.fidgettest4

%.fidget: %.hb $(ALB)
	$(ALB) -i ../tests:. -f -O4$(OPTS) $< -o $*.fidget
#	$(ALB) -O2 -f $< -o $*.fidget

%.fidget0: %.hb $(ALB)
	$(ALB) -i ../tests:. -O 0$(OPTS)  -f $< -o $*.fidget0

%.fidget1: %.hb $(ALB)
	$(ALB) -i ../tests:. -O1$(OPTS) -f $< -o $*.fidget1

%.fidget2: %.hb $(ALB)
	$(ALB) -i ../tests:. -O2$(OPTS) -f $< -o $*.fidget2

%.fidget3: %.hb $(ALB)
	$(ALB) -i ../tests:. -O3$(OPTS) -f $< -o $*.fidget3

%.out: %.fidget $(CCOMP) $(OTHER_FILES)
	$(CCOMP)  -L$(COMPCERT)/lib/compcert -o $@ $*.fidget $(OTHER_FILES)

%.gcm: %.fidget $(CCOMP) $(OTHER_FILES)
	$(CCOMP) -dgcminor -L$(COMPCERT)/lib/compcert $*.fidget $(OTHER_FILES) -o $*.out

%.cm: %.fidget $(CCOMP) $(OTHER_FILES)
	$(CCOMP) -dcminor  -L$(COMPCERT)/lib/compcert $*.fidget $(OTHER_FILES) -o $*.out

%.s: %.fidget $(CCOMP) $(OTHER_FILES)
	$(CCOMP) -dasm -L$(COMPCERT)/lib/compcert $*.fidget $(OTHER_FILES) -o $*.out

#1's are Done to prevent collision with compcert generated .o files
%.o1: %.s $(CCOMP) $(OTHER_FILES)
	$(AS) -32 -g $*.s -o $*.o1

%.out1: %.o1 $(CCOMP) $(OTHER_FILES)
	$(LD) -g $*.o1 -o $*.out1 -lc --dynamic-linker /lib/ld-linux.so.2 -m elf_i386 -ehb_main $(MORELIBS)

clean:
	rm -f *.o
	rm -f *.o1
	rm -f *.gcm
	rm -f *.cm
	rm -f *.out
	rm -f *.out1
	rm -f results.txt
	rm -f *.s
	rm -f *.hi
	rm -f *.fidget
	rm -f *.fidget1
	rm -f *.fidget2
	rm -f *.fidget3
	rm -f *.fidget0
