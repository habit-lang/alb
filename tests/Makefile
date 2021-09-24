# Usage:
#  "make tests-alb"" makes and runs alb tests
#  "make tests-ilab"" makes and runs ilab tests
#  "make clean" removes *.out files
#  "make foo.out" makes foo.out from foo.hb or foo.lhb

### TODO! We need a better system (probably hspec?) that automatically pulls in all the *.hb files compiles them and runs them

# WARNING: Be sure to include the "./" at the front.  Otherwise, testHarness.hs will fail the whole file.
TESTS=$(ALB_TEST_DIR)/example-test.out $(ALB_TEST_DIR)/State.out $(ALB_TEST_DIR)/foo.out $(ALB_TEST_DIR)/requirements.out

# Need to add them or leave them out?
NON_EXISTENT_TESTS=$(ALB_TEST_DIR)/prioset.out $(ALB_TEST_DIR)/cases2.out $(ALB_TEST_DIR)/bugIxBound.out

# If any code is broken please move it from TESTS to BROKEN_TESTS and add a comment on why it broke!

# largeword-driver gives "context too weak to prove"
# ---------------

# three.out fails because
# --------
# external primIncIx$5cg9 {primIncIx 3} :: Ix 3 -> Maybe__Ix_3
#          ^
# No generated implementation: Bitdata representations ("b" pass) required

# Lambda.out fails because:
# ----------
# Context too weak to prove:
    # Monad Maybe arising at Lambda.hb:24:20-27
    # In Lambda.hb

# listdriver.hb fails because:
# -------------
# Undefined symbols for architecture x86_64:
#   "_alloc", referenced from:
#       _func_b1112 in listdriver-557a89.o
#       _func_b1535 in listdriver-557a89.o
#       _func_b739 in listdriver-557a89.o
#       _func_b785 in listdriver-557a89.o
#       _func_b531 in listdriver-557a89.o
#       _func_b563 in listdriver-557a89.o
#       _func_b769 in listdriver-557a89.o
#       ...
#   "_halt", referenced from:
#       _func_b498 in listdriver-557a89.o
# ld: symbol(s) not found for architecture x86_64

# redblack.hb fails becuase
# INTERNAL ERROR: multiple alternatives for B$58g4
# java.lang.Exception
# 	at debug.Internal.error(Unknown Source)
# 	at mil.CfunAlt.cfunsUsed(Unknown Source)
# 	at mil.CfunAlt.cfunsUsed(Unknown Source)
# 	at mil.CfunAlt.cfunsUsed(Unknown Source)
# 	at mil.Case.cfunSimplify(Unknown Source)
# 	at mil.Block.cfunSimplify(Unknown Source)
# 	at mil.MILProgram.cfunSimplify(Unknown Source)
# 	at mil.MILProgram.cfunRewrite(Unknown Source)
# 	at driver.Main.process(Unknown Source)
# 	at driver.Main.run(Unknown Source)
# 	at driver.Main.main(Unknown Source)

# bug0050.hb fails because
# Reading "miniprelude.hb":
# "miniprelude.hb" (line 154, column 20):
# unexpected "("
# expecting "," or "::"

# BigArray.hb fails because
# Reading "miniprelude.hb":
# "miniprelude.hb" (line 154, column 20):
# unexpected "("
# expecting "," or "::"

# md5driver.hb fails because
# Reading "miniprelude.hb":
# "miniprelude.hb" (line 154, column 20):
# unexpected "("
# expecting "," or "::"

# Mersenne.out fails because
# Reading "miniprelude.hb":
# "miniprelude.hb" (line 154, column 20):
# unexpected "("
# expecting "," or "::"

BROKEN_TESTS=$(ALB_TEST_DIR)/largeword-driver.out $(ALB_TEST_DIR)/three.out $(ALB_TEST_DIR)/Lambda.out $(ALB_TEST_DIR)/listdriver.out
BROKEN_TESTS+= $(ALB_TEST_DIR)/redblack.out $(ALB_TEST_DIR)/bug0050.out $(ALB_TEST_DIR)/BigArray.out $(ALB_TEST_DIR)/md5driver.out $(ALB_TEST_DIR)/Mersenne.out

ALB_DIR=$(pwd)
ALB_TEST_DIR=tests

# MIL locations
#FIXME! we assume that mil-tools and alb are under the same root directory. It may not be the case.
MIL_DIR=../mil-tools
MILC=milc

CLANG_EXE=/usr/bin/clang

# Workaround for cabal run not defaulting to exe component (see: https://github.com/haskell/cabal/issues/7403)
ALB_EXE=cabal run alb:exe:alb

MIL_OPTS=--milc=$(MIL_DIR)/$(MILC) --include-mil $(MIL_DIR)/lib/basic.mil --llvm-main main

ALB_OPTS=--verbose --no-dot-files --path=$(ALB_TEST_DIR) --clang=$(CLANG_EXE)

broken-alb: $(BROKEN_TESTS)
	runghc tests/testHarness.hs $(BROKEN_TESTS)

tests-alb: $(TESTS)
	runghc tests/testHarness.hs $(TESTS)

tests-ilab: ilab
	runghc -irc tests/Solver/Runtests.hs

# FIXME! out is necessary to add an extra file-extention as alb drops the first one while generating the program executable
%.out:
	$(ALB_EXE) -- $*.hb -o $@.out $(ALB_OPTS) $(MIL_OPTS)

all-tests: tests-alb broken-alb tests-ilab
