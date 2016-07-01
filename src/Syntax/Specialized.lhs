> module Syntax.Specialized (module Syntax.XMPEG, module Syntax.Specialized) where

> import Syntax.XMPEG

A specialized program provides a specialized list of top decls, an expression
corresponding to the program entry point, a list of specialized value decls,
and a list of the required primitives.

> data Specialized = Specialized (TopDecls Type) [Expr] Decls
