```
  |             |     _)  |         |                      
  __ \    _` |  __ \   |  __|       |   _` |  __ \    _` | 
  | | |  (   |  |   |  |  | _____|  |  (   |  |   |  (   | 
 _| |_| \__,_| _.__/  _| \__|      _| \__,_| _|  _| \__, | 
                                                    |___/  
```

ALBATROSS
=========

This is Albatross, a tool for compiling relatively efficient implementations of priority queues.
It has consumed instancelab, which was an interface for playing with advanced type class features.

DEPENDENCIES
------------

Albatross attempts to be relatively self-contained; however, it does require some packages that may
or may not be installed on your machine.  The alb.cabal file should have up-to-date dependencies.

Alb compiles using GHC 7.10, and hopefully later versions, but does not compile on version 7.8 or
earlier (as a result of having to work around the Applicative Monad Phoolishness).

BUILDING
-------
#### Via cabal:

Optionally, set up a cabal sandbox:

```shell
$ cabal new-build alb
```

Otherwise, proceed to installation with:

```shell
$ cabal new-install alb
```

#### Via make:

```shell
$ make alb
```

RUNNING
-------

Albatross is a batch compiler, and currently lacks an interactive mode.
Flags can be listed using command line option `--help`.

Without overriding flags, Alb will attempt to generate LC and invoke the MIL tools to produce an
executable.

Unless the `--no-dot-files` option is specified, Alb will look for files called ".alb" in your home
directory and the current directory, and will read options from those files.  Options on the command
line override options in files, and options in the local directory override options in your home
directory.

HABIT LANGUAGE EXTENSIONS
-------------------------

#### IMPORT CHASING

This extension adds two features:

1. You can set a `search path` for Habit source files by using a command something like the
following:

```shell
$ ./alb --path=folder1:folder2 X Y Z
```
The front end will then try each of the names in the list `X`, `folder1/X.hb`, `folder1/X.lhb`,
`folder2/X.hb`, `folder2/X.lhb` in an attempt to find the source for file `X`.  Once `X` has been loaded, `Y`
and `Z` will be loaded in the same way.

If you don't set a search path using `--path`, then the default setting `[""]` is used.  The front end
uses the conventions of the host, so, for example, syntax for the command above on a Windows machine
should look more like the following (untested):

```shell
$ ./alb --path=folder1;folder2 X Y Z
```

2. You can annotate individual habit source files with statements of the form:

```
requires Name[, Name]
```

(Name can be any sequence of one or more Habit identifiers (varids or conids) separated by periods,
but can't include any other punctuation or symbols.)  If the file X contains a declaration like
this, then the front-end will automatically load the file for Name before it actually processes X.
Each Name will be interpreted in the same way as if you had typed it on the command line except
that any periods will be replaced with the appropriate file path separator for your OS (typically
either / or \).  For example, if X.hb and Name.hb are valid Habit source files in the current
directory, then:

```shell
$ ./alb Name.hb X.hb           # ... other command line arguments
```

and

```shell
$ ./alb X            #... other command line arguments
```

should have exactly the same effect.  Similarly, if X contains a line `requires foo.bar`, and
there is a file called `bar.hb` in the `foo` subdirectory, then the front end will attempt to
load that file before loading X.

The `requires Name` construct can appear at any point in the input code, and the same file can be
named more than once without causing an error.

INSTANCELAB
===========

BUILDING
--------

Via cabal:

Optionally, set up a cabal sandbox:

```shell
$ cabal new-build ilab
```

Otherwise, proceed to installation with:

```shell
$ cabal new-install ilab
```

Via make:

```shell
$ make ilab
```

Dependencies are as above.

RUNNING
-------

`ilab` has both batch and interactive modes.  To run `ilab` over a set of files, specify them on the
command line:

```shell
$ ./ilab tests/1 tests/2
```

Note: `ilab` reads all axioms from all the files, then checks any predicate queries.  So in the above
examples, predicates in tests/1 will be able to see axioms in tests/2.

To run `ilab` interactively, specify no files on the command line or specify `-i` along with a list of
files.  The files will be read for axioms and predicate queries, and the axioms will be added to the
working set for the interactive session.

`ilab` can attempt to print proofs for predicate queries it solves. To display proofs, supply `-p` on
the command line, or use the command `p on` from inside the REPL.

At the prompt ('>'), you may type:

 * `q` - to quit

 * `f <filename>` - to load filename, add its axioms to the working set, and print
   the results of its predicate queries.

 * `r` - which resets the working set

 * `d` - which dumps the working set

 * `p` (on|off) - turn proof display on or off

 * `n` (on|off) - display number of tree nodes generated while solving

 * An axiom, functional dependency, or requirement - which is added to the working set

 * A predicate query - which ilab attempts to prove using the axioms and
   functional dependencies in its working set.

SYNTAX
------

Concrete syntax is between single quotes.

`Tycon` - any alphanumeric string starting with an uppercase letter, or any symbol or sequence of symbols.

`Tyvar` - any alphanumeric string starting with a lowercase letter.

`Clname` - same as Tycon

`Ident` - same as Tyvar

`Natural` - any natural number

```
Type        ::= AType | AType Type
AType       ::= Tycon | Tyvar | '(' Type ')' | Natural | 'P'Natural
X           ::= | 'fails'
Pred        ::= Clname AType* X
QPred       ::= Pred | Pred 'if' Pred+
Axiom       ::= QPred '.' | QPred ';' Axiom
NamedAxiom  ::= Ident ':' Axiom
FunDepRule  ::= Clname Tyvar+ '|' FunDep+ '.'
FunDep      ::= Tyvar* '~>' Tyvar+
Requirement ::= Pred 'requires' Pred+
PredQuery   ::= QPred '?'
```

All qpreds in an axiom must refer to the same class.  Instances must not overlap - context and
functional dependencies are considered when making this determination - and must meet the covering
condition for their functional dependencies.

PROOFS
------
Proofs are displayed as evidence expressions.  For instance, with two axioms:

```
eq_int: Eq Int.
eq_list: Eq t => Eq (List t).
```

Then a proof that Eq (List (List Int)) holds would be:

```
eq_list(eq_list(eq_int))
```

Rules from an axiom are selected with the '!' operator.  For instance with the
axioms:

```
eq_int: Eq Int.
eq_t_fails: Eq T fails.
eq_list: Eq t => Eq (List t); Eq t fails -> Eq (List t) fails.
```

then a proof that Eq (List T) fails would be:

`eq_list!1(eq_t_fails)`

EXAMPLE
-------

The `tests/solver/tests` directory contains some sample files.

TESTS
-----

A crude testing framework is implemented in RunTests.hs.  This file reads tests from
`./tests/solver/catalog`, and compares the result of each test to the output saved in the results
directory.  Examine the `RunTests.hs` file for more detail on the data types used.  To run the tests,
use:

```shell
$ make tests-ilab
```

Or if you're in the compiler/ directory

```shell
$ runghc -irc tests/Solver/RunTests.hs
```

This has been tested on both Windows and Mac OS.  The test framework requires some version
of the process package - I currently seem to be using 1.0.1.1.  I assume this is in the
standard GHC/Haskell Platform distribution at this point.

Additional contributors
=======================

Members of the HASP project at Portland State University contributed to the development and testing
of Alb before it was made publicly visible.  They are listed here.  Corrections/additions are
welcomed.

- Andrew Sackville-West
- Andrew Tolmach
- Caylee Hogg
- J. Garrett Morris
- James Hook
- Justin Bailey
- Lewis Coates
- Mark P. Jones
- Michael D. Adams
- Thomas M. DuBuisson
