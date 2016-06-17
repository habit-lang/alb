GHC=stack exec ghc --
OPT=-XOverloadedStrings -O2 -j4 -o $@ -odir obj -hidir obj -isrc src/Driver.hs
HIDE=-hide-package indentation-parsec-0.0 -hide-package indentation-core-0.0 -hide-package indentation-trifecta-0.0
OBJDIR=obj

.PHONY: all alb albp alb-hpc test ilab

all: ilab alb

stack: stack.yaml
	stack setup && stack build --only-dependencies --ghc-options="-j4"

alb: stack
	$(GHC) $(HIDE) --make $(OPT) -rtsopts

albp: alb
	$(GHC) --make $(OPT) -rtsopts -prof -auto-all -osuf p_o -hisuf p_hi

alb-hpc: stack
	$(GHC) -fhpc --make -fforce-recomp $(OPT)

albc:   ./src/albc/Albc.hs stack
	$(GHC) --make -O2 -o $@ -odir obj -hidir obj src/albc/Albc.hs

ilab: stack
	ghc --make -XOverloadedStrings -O2 -o ilab -odir obj -hidir obj -isrc -main-is Solver.REPL.main Solver.REPL

test: alb
	./alb -i tests -f main $(TEST)
