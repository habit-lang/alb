# Usage:
#  "make test" or "make all" makes and runs all tests
#  "make clean" removes *.out and *.fidget
#  "make foo.out" makes foo.out from foo.hb or foo.lhb
all: test

# WARNING: Be sure to include the "./" at the front.  Otherwise, testHarness.hs will fail the whole file.
TESTS=./example-test.out ./three.out ./Lambda.out  ./State.out ./listdriver.out ./redblack.out ./foo.out ./prioset.out ./bug0050.out ./bugIxBound.out ./cases2.out ./requirements.out ./BigArray.out ./md5driver.out ./Mersenne.out

# If any code is broken please move it from TESTS to BROKEN_TESTS and add a comment on why it broke!
# largeword-driver gives "context too weak to prove"
BROKEN_TESTS=./largeword-driver.out

COV=./example-test.cov ./three.cov ./Lambda.cov ./Mersenne.cov ./State.cov ./listdriver.cov ./redblack.cov ./foo.cov ./largeword-driver.cov ./bug0050.out ./md5driver.out ./bugIxBound.out

COV_HI_MEM=./prioset.cov

ALB=../alb
ALBHPC=../alb-hpc
#COMPCERT=../../../compcert1.11-hasp
COMPCERT=../../../compcert2.0-hasp
CCOMP=$(COMPCERT)/ccomp
OTHER_FILES=$(COMPCERT)/test/fidget/harness.c $(COMPCERT)/runtime/gc/cheney.o
OTHER_DEPS=$(ALB) $(COMPCERT)/ccomp

.PHONEY: all test

all-tests: test broken

broken: $(BROKEN_TESTS)
	runghc testHarness.hs $(BROKEN_TESTS)

test: $(TESTS)
	runghc testHarness.hs $(TESTS)

coverage: $(COV)
	hpc combine --output tmp.tix ./alb-hpc.tix ../alb-hpc.tix
	mv tmp.tix ../alb-hpc.tix
	cd .. ; hpc report alb-hpc --exclude=Printer.Common --exclude=Printer.IMPEG --exclude=Printer.LambdaCase --exclude=Printer.Specialized --exclude=Printer.Surface --exclude=Printer.WadlerLeijen --exclude=Printer.XMPEG

coverage-hi-mem: $(COV) $(COV_HI_MEM)
	hpc combine --output tmp.tix ./alb-hpc.tix ../alb-hpc.tix
	mv tmp.tix ../alb-hpc.tix
	cd .. ; hpc report alb-hpc --exclude=Printer.Common --exclude=Printer.IMPEG --exclude=Printer.LambdaCase --exclude=Printer.Specialized --exclude=Printer.Surface --exclude=Printer.WadlerLeijen --exclude=Printer.XMPEG

%.fidget: %.lhb $(ALB)
	$(ALB) -O2 -f $< -o $*.fidget

%.fidget: %.hb $(ALB)
	$(ALB) -O2 -f $< -o $*.fidget

%.out: %.fidget $(CCOMP) $(OTHER_FILES)
	$(CCOMP)  -L$(COMPCERT)/lib/compcert -o $@ $*.fidget $(OTHER_FILES)

%.cov: %.hb $(ALBHPC)
	$(ALBHPC) -f $< > /dev/null

%.cov: %.lhb $(ALBHPC)
	$(ALBHPC) -f $< > /dev/null

clean:
	rm -f *.o
	rm -f *.out
	rm -f *.fidget
	rm -f *.tix
	rm -f ../alb-hpc.tix
