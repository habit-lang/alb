include tests/Makefile

# executables to be produced
TARGETS=install-ilab install-alb

# This directory stores the executables for alb and ilab
# This path should be added to $PATH or %PATH%
BINDIR = $(HOME)/.local/bin

.PHONY: all

all: alb ilab tests-alb tests-ilab

alb:
	cabal new-build --user alb

ilab:
	cabal new-build --user ilab

install-alb: alb tests-alb
	cabal new-install --user alb --symlink-bindir=$(BINDIR)

install-ilab: ilab tests-ilab
	cabal new-install --user ilab --symlink-bindir=$(BINDIR)

clean:
	rm -fr $(OBJDIR) .cabal-sandbox dist-newstyle dist $(BINDIR)/alb $(BINDIR)/ilab alb ilab
	rm -rf **/*.o
	rm -rf **/*.out
	rm -rf $(TESTS)
