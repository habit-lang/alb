> {-# LANGUAGE OverloadedStrings #-}
> module Normalizer.EtaInit(etaInit) where

The code in this module implements a walk over the AST of a LambdaCase program
that:

Eta-expands any top-level definitions that have function type with right hand
sides that are not already lambdas.

These transformations are designed to align generated LambdaCase code with the
requirements of the previous back-end, and may now be entirely unnecessary.

> import Syntax.Common
> import Syntax.LambdaCase

> etaInit :: Program -> Program
> etaInit  = eta

-- Expand uses of Init: ------------------------------------------------------

AST fragments and constructors:

> arrKId    :: Kinded Id
> arrKId     = Kinded "->" (KFun KStar (KFun KStar KStar))

> arrTyCon  :: Type
> arrTyCon   = TyCon arrKId

-- Eta-expand top-level decls: -----------------------------------------------

Confusingly, the "top-level decls" referred to here are the entries in the
"decls" component at the top of a program, and not the entries in the "topDecls"
component ...

> class Eta a where eta :: a -> a

Here's the instance that does the work for this pass:

> instance Eta Defn where
>   eta d = case d of
>            Defn i t (Left _) -> d
>            -- ignore if there's already a lambda on the rhs
>            Defn i t (Right (ELam _ _ _)) -> d
>            Defn i t (Right e)
>              -> case t of
>                   -- eta expand if the binding has a function type
>                   (h `TyApp` dom) `TyApp` _
>                     | h == arrTyCon -> Defn i t (Right (ELam etav dom (EApp e (EVar etav dom))))
>                   -- Otherwise return the original definition
>                   _ -> d

The name of the variable that we'll use for eta expansion:

> etav = "eta$x" :: Id

The remaining instances just list this behavior to Decls, and then to complete
programs:

> instance Eta a => Eta [a] where
>   eta = map eta

> instance Eta Decl where
>   eta (Mutual ds) = Mutual (eta ds)
>   eta (Nonrec d)  = Nonrec (eta d)

> instance Eta Decls where
>   eta (Decls ds) = Decls (eta ds)

> instance Eta Program where
>   eta (Program decls tops) = Program (eta decls) tops

------------------------------------------------------------------------------
