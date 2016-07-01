GHC=ghc
OBJDIR=obj

.PHONY: all alb albp alb-hpc test ilab

all: ilab alb

alb:
	$(GHC) --make -XOverloadedStrings -O2 -o $@ -odir obj -hidir obj -isrc src/Driver.hs -rtsopts

albp: alb
	$(GHC) --make -XOverloadedStrings -O2 -o $@ -odir obj -hidir obj -isrc src/Driver.hs -rtsopts -prof -auto-all -osuf p_o -hisuf p_hi

alb-hpc:
	$(GHC) -fhpc --make -fforce-recomp -XOverloadedStrings -O2 -o $@ -odir objhpc -hidir objhpc -isrc src/Driver.hs

albc:   ./src/albc/Albc.hs
	$(GHC) --make -O2 -o $@ -odir obj -hidir obj src/albc/Albc.hs

ilab:
	ghc --make -XOverloadedStrings -O2 -o ilab -odir obj -hidir obj -isrc -main-is Solver.REPL.main Solver.REPL

test:
	./alb -i tests -f main $(TEST)
