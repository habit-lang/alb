> {-# LANGUAGE OverloadedStrings #-}
> module Normalizer.EtaInit(etaInit) where

The code in this module implements a walk over the AST of a LambdaCase program
that:
(1) replaces any type expression of the form "Init t" in the abstract syntax
    tree with a function type "ARef 1 t -> Result"
(2) Eta-expand any top-level definitions that have function type (after the
    transformations of Step (1) are complete) with right hand sides that are
    not already lambdas.

These transformations are designed to align generated LambdaCase code with the
requirements of the current back-end.

> import Syntax.Common
> import Syntax.LambdaCase

> etaInit :: Program -> Program
> etaInit  = eta . deInit

-- Expand uses of Init: ------------------------------------------------------

AST fragments and constructors:

> initKId   :: Kinded Id
> initKId    = Kinded "Init" (KFun KArea KStar)

> initTyCon :: Type
> initTyCon  = TyCon initKId

> arrKId    :: Kinded Id
> arrKId     = Kinded "->" (KFun KStar (KFun KStar KStar))

> arrTyCon  :: Type
> arrTyCon   = TyCon arrKId

> arefTy    :: Type
> arefTy     = TyCon (Kinded "ARef" (KFun KNat (KFun KArea KStar))) `TyApp` TyLit 1

> resultTy  :: Type
> resultTy   = TyApp (TyCon (Kinded "I" (KStar `KFun` KStar)))
>                    (TyCon (Kinded "Unit" KStar))

AST walker:

> class DeInit a where deInit :: a -> a

> instance DeInit Type where
>   deInit (TyApp l r)
>      | l == initTyCon = (arrTyCon `TyApp` (arefTy `TyApp` r)) `TyApp` resultTy
>      | otherwise      = TyApp (deInit l) (deInit r)
>   deInit t
>      | t == initTyCon = error "partially applied Init"  -- correct behavior?
>      | otherwise      = t

> instance DeInit a => DeInit [a] where
>   deInit = map deInit

> instance DeInit Expr where
>   deInit (EVar i t)          = EVar i (deInit t)
>   deInit (ECon i ts t)       = ECon i (deInit ts) (deInit t)
>   deInit (ELam i t e)        = ELam i (deInit t) (deInit e)
>   deInit (ELet ds e)         = ELet (deInit ds) (deInit e)
>   deInit (ECase e alts)      = ECase (deInit e) (deInit alts)
>   deInit (EApp f x)          = EApp (deInit f) (deInit x)
>   deInit (EFatbar l r)       = EFatbar (deInit l) (deInit r)
>   deInit (EBind i t e e1)    = EBind i (deInit t) (deInit e) (deInit e1)
>   deInit e                   = e -- covers EBits, ENat

> instance DeInit Alt where
>   deInit (Alt c ts is e)     = Alt c (deInit ts) is (deInit e)

> instance DeInit Defn where
>   deInit (Defn i t (Left impl))  = Defn i (deInit t) (Left impl)
>   deInit (Defn i t (Right e)) = Defn i (deInit t) (Right (deInit e))

> instance DeInit Decl where
>   deInit (Mutual defns)      = Mutual (deInit defns)
>   deInit (Nonrec defn)       = Nonrec (deInit defn)

> instance DeInit Decls where
>   deInit (Decls decls)       = Decls (deInit decls)

> instance DeInit TopDecl where
>   deInit (Datatype i ts ctors)
>                              = Datatype i (deInit ts) [ (i, deInit as) | (i, as) <- ctors ]
>   deInit (Bitdatatype i w ctors)
>                              = Bitdatatype i w [ (i, deInit fs) | (i, fs) <- ctors ]
>   deInit (Struct i w fields) = Struct i w (deInit fields)
>   deInit (Area i v e t s a)  = Area i v (deInit e) (deInit t) s a

> instance DeInit BitdataField where
>   deInit (LabeledField i t w o) = LabeledField i (deInit t) w o
>   deInit constantField          = constantField

> instance DeInit StructField where
>   deInit (StructField mi t w o) = StructField mi (deInit t) w o

> instance DeInit Program where
>   deInit (Program ds tops)      = Program (deInit ds) (deInit tops)

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

