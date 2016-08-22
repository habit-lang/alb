> {-# LANGUAGE FlexibleInstances #-}

----------------------------------------------------------------------------------------------------
-- Printer for Mon6.

> module Printer.Mon6 (Printable(..), module Printer.Mon6) where

> import Printer.Common
> import Printer.XMPEG
> import Syntax.Mon6
> import Utils.BDD

> import Prelude hiding ((<$>))

Basically the same printer as originally defined for Mon6, but adapted to the Wadler-Leijen
approach.

> instance Printable (Defn primimpl)
>     where ppr (BlockDefn b vs c) =
>               hang 4 (ppr b <> parens (pprList' vs) <+> "=" </>
>                       align (ppr c))
>           ppr (ClosureDefn k vs v t) =
>               hang 4 (ppr k <> braces (pprList' vs) <+> ppr v <+> "=" </>
>                       align (ppr t))
>           ppr (Init v t) =
>               hang 4 (ppr v <+> "<-" </> ppr t)
>           ppr (PrimDefn name _) = "primitive" <+> ppr name

> instance Printable Code
>     where ppr (Done t) = ppr t
>           ppr (Bind v t c) = ppr v <+> "<-" <+> ppr t <$> ppr c
>           ppr (Case v as d) = hang 4 ("case" <+> ppr v <+> "of" <$> vcat (map printAlt as) <$> printDef d)
>               where printAlt (c, vs, t) = hang 4 (ppr c <> parens (pprList' vs) <+> "->" </> ppr t)
>                     printDef d = hang 4 ("_ ->" <+> ppr d)
>           ppr (BitCase x as d) = hang 4 ("case" <+> ppr x <+> "of" <$> vcat (map printAlt as) <$> printDef d)
>               where printAlt (b, v, t) = hang 4 (ppr b <> parens (ppr v) <+> "->" </> ppr t)
>                     printDef d = hang 4 ("_ ->" <+> ppr d)

> instance Printable Atom
>     where ppr (Var v) = ppr v
>           ppr (Const w) = text (show w)

> instance Printable Tail
>     where ppr (Return a)         = "return" <+> ppr a
>           ppr (BlockCall b vs)   = ppr b <> parens (pprList vs)
>           ppr (DataAlloc c vs)   = ppr c <> parens (pprList vs)
>           ppr (ClosAlloc k vs)   = ppr k <> braces (pprList vs)
>           ppr (Enter f x)        = ppr f <+> "@" <+> ppr x
>           ppr (PrimCall p vs)    = ppr p <> parens (parens (pprList vs))

> instance Printable (Code, [Defn primimpl])
>     where ppr (main, defns) = vcat (map ppr defns) <$> "\nEntry point:" <$> ppr main
