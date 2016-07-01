> module Literate where

> import Common
> import Control.Monad.State
> import Data.Char
> import Printer.Common

Literate comments
-----------------

[This file contains an executable version of the program for
processing literate scripts that appears in Appendix C of the Haskell
report, version 1.2.]

Many Haskell implementations support the ``literate comment''
convention, first developed by Richard Bird and Philip Wadler for
Orwell, and inspired in turn by Donald Knuth's ``literate programming''.
The convention is not part of the Haskell language, but it is
supported by the implementations known to us (Chalmers, Glasgow,
and Yale).

The literate style encourages comments by making them the default.
A line in which ">" is the first character is treated as part of
the program; all other lines are comment.  Within the program part,
the usual "--" and "{- -}" comment conventions may still be used.
To capture some cases where one omits an ">" by mistake, it is an
error for a program line to appear adjacent to a non-blank comment
line, where a line is taken as blank if it consists only of
whitespace.

By convention, the style of comment is indicated by the file
extension, with ".hs" indicating a usual Haskell file, and ".lhs"
indicating a literate Haskell file.

To make this precise, we present a literate Haskell program to
convert literate programs.  The program expects a single name "file"
on the command line, reads "file.lhs", and either writes the
corresponding program to "file.hs" or prints error messages to
"stderr".

Each of the lines in a literate script is a program line, a blank
line, or a comment line.  In the first case, the text is kept with
the line.

> data Classified  =  Program String | Blank | Comment

In a literate program, program lines begins with a `>' character,
blank lines contain only whitespace, and all other lines are comment
lines.

> classify                       	::  String -> Classified
> classify ('>':s)			=   Program s
> classify s  |  all isSpace s		=   Blank
> classify s  |  otherwise		=   Comment

In the corresponding program, program lines have the leading `>'
replaced by a leading space, to preserve tab alignments.

> unclassify                		::  Classified -> String
> unclassify (Program s)		=   " " ++ s
> unclassify Blank			=   ""
> unclassify Comment			=   ""

Process a literate program into error messages (if any) and the
corresponding non-literate program.

> process    :: String -> ([String], String)
> process lhs = (errors cs, unlines (map unclassify cs))
>               where cs = map classify (lines lhs)

Check that each program line is not adjacent to a comment line.

> errors	::  [Classified] -> [String]
> errors cs	=   concat (zipWith3 adjacent [1..] cs (tail cs))

Given a line number and a pair of adjacent lines, generate a list
of error messages, which will contain either one entry or none.

> adjacent	::  Int -> Classified -> Classified -> [String]
> adjacent n (Program _) Comment  =  [message n "program" "comment"]
> adjacent n Comment (Program _)  =  [message n "comment" "program"]
> adjacent n this           next  =  []

> message n p c = "Line "++show n++": "++p++" line before "++c++" line."

Finally, we can wrap the deliterating process as a string to string
compiler pass.

> unlit :: Pass () String String
> unlit s = case process s of
>             ([], hs) -> return hs
>             (err, _) -> failWith (text (unlines err))

> delit :: String -> String -> Either String String
> delit source contents
>   = case process contents of
>       ([], hs) -> Right hs
>       (err, _) -> Left (unlines(("In \"" ++ source ++ "\":") : map ("  "++) err))
