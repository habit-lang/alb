> module Printer.Specialized (module Printer.XMPEG, module Printer.Specialized) where

> import Printer.Common
> import Printer.XMPEG
> import Syntax.Specialized

> instance Printable Specialized where
>   ppr (Specialized topdecls entries decls)
>     = vcat (punctuate line [ppr topdecls,
>                             ppr decls,
>                             text "entry points:" <+> cat (punctuate (comma <> space) (map (ppr . fst) entries))])

> {- The definitions of Primtives and DApp are now local to Specializer.lhs
> instance Printable Primitives where
>    ppr (Primitives ps)
>     = vcat ({-punctuate line-} [ text "primitive:" <+> symbol id <+> text "=" <+> ppr d | (d, id) <- ps ])

> instance Printable DApp where
>   ppr (DApp id ts ds) = atPrecedence 9 $
>              cat (punctuate space (symbol id <> braces (cat (punctuate comma (map ppr ts)))
>                                   : map (withPrecedence 10 . ppr) ds))
> -}
