ifneq ("$(wildcard ./.useStack)","")
	GHC=stack exec ghc --
	SDEP=stack
else
	GHC=ghc
	SDEP=
endif
OPT=-XOverloadedStrings -O2 -j3 -o $@ -odir obj -hidir obj -isrc src/Driver.hs
HIDE=-hide-package indentation-parsec-0.0 -hide-package indentation-core-0.0 -hide-package indentation-trifecta-0.0
OBJDIR=obj
TARGETS=ilab alb albp alb-hpc albc

.PHONY: all alb albp alb-hpc test ilab

all: $(TARGETS)

stack: stack.yaml
	stack setup && stack build --only-dependencies --library-profiling --ghc-options="-j3" && touch .useStack

nostack:
	rm .useStack

clean:
	rm -fr $(TARGETS) obj .stack-work .cabal-sandbox

alb: $(SDEP)
	$(GHC) $(HIDE) --make $(OPT) -rtsopts

albp: $(SDEP)
	$(GHC) $(HIDE) --make $(OPT) -rtsopts -prof -auto-all -osuf p_o -hisuf p_hi

alb-hpc: $(SDEP)
	$(GHC) $(HIDE) -fhpc --make -fforce-recomp $(OPT)

albc:   ./src/albc/Albc.hs $(SDEP)
	$(GHC) $(HIDE) --make -O2 -o $@ -odir obj -hidir obj src/albc/Albc.hs

ilab: $(SDEP)
	$(GHC) $(HIDE) --make -XOverloadedStrings -O2 -j3 -o ilab -odir obj -hidir obj -isrc -main-is Solver.REPL.main Solver.REPL

test: alb
	./alb -i tests -f main $(TEST)
