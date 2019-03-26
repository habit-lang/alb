> {-# LANGUAGE FlexibleInstances, PatternGuards #-}
> module Normalizer.BitPatterns (compilePatterns) where

The code in this module performs a simple inlining pass on LambdaCase
declarations lists, eliminating trivial bindings of the form v = e where e is
either an EPrim or an EVar.  It also attempts to rename bindings with names
that might not be linker friendly.

Come to think of it, this code could easily be modified to propagate type
annotations to EVar nodes if we weren't going to rely on full type checking.

> import Syntax.XMPEG
> import Syntax.Specialized

> import Debug.Trace

Transform the input "expression" e by performing dependency analysis on every
Mutual group that it contains, returning the transformed version of e as well
as the set of free variables in e.

> class HasBitPatterns e where
>   compile :: e -> e

> instance HasBitPatterns Expr where
>   compile e@(ECon (Inst n ts []))
>       | n == ":#"                  = let [TyNat lo, TyNat hi, TyNat total] = ts
>                                      in trace ("Built a :#! {" ++ show [lo, hi, total] ++ "}") e
>       | otherwise                  = e
>   compile (ECon (Inst _ _ _))      = error "BitPatterns.lhs:30"
>   compile (EBitCon i fields)       = EBitCon i [(f, compile e) | (f, e) <- fields]
>   compile (EStructInit k fields)   = EStructInit k [(f, compile e) | (f, e) <- fields]
>   compile (ELam i t e)             = ELam i t (compile e)
>   compile (ELet ds e)              = ELet (compile ds) (compile e)
>   compile (EMatch m)               = EMatch (compile m)
>   compile (EApp f x)               = EApp (compile f) (compile x)
>   compile (EBitSelect e f)         = EBitSelect (compile e) f
>   compile (EBitUpdate e f e')      = EBitUpdate (compile e) f (compile e')
>   compile (EBind ta tb tm me i e e1) = EBind ta tb tm me i (compile e) (compile e1)
>   compile (EReturn e)              = EReturn (compile e)
>   compile e                        = e -- covers EPrim, EBits, ENat, ELamVar, ELetVar

> instance HasBitPatterns Match where
>   compile MFail = MFail
>   compile (MCommit e) = MCommit (compile e)
>   compile (MElse m1 m2) = MElse (compile m1) (compile m2)
>   compile (MGuarded g@(GFrom (PCon (Inst ":#" [TyNat lo, TyNat hi, TyNat total] []) [xlo, xhi]) w) m)=
>       -- MGuarded (GLet (Decls [(xlo, ... ), (xhi, ...)]) (compile m)
>       trace (concat ["Found a :# pattern! ", fromId xlo, " :: Bit ", show lo, ", ", fromId xhi, " :: Bit ", show hi])
>             (MGuarded g (compile m))
>   compile (MGuarded (GLet ds) m) = MGuarded (GLet (compile ds)) (compile m)
>   compile (MGuarded g m) = MGuarded g (compile m)

> instance HasBitPatterns Defn where
>   compile (Defn i t (Left impl))  = Defn i t (Left impl)
>   compile (Defn i t (Right (Gen [] [] e))) = Defn i t (Right (Gen [] [] (compile e)))

> instance HasBitPatterns Decls where
>   compile (Decls ds) = Decls (map compile ds)

> compilePatterns :: Specialized -> Specialized
> compilePatterns (Specialized topDecls entries decls)
>     = Specialized topDecls entries (compile decls)
