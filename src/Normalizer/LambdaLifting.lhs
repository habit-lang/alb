> {-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
> module Normalizer.LambdaLifting (liftDefinitions) where

> import Common
> import Control.Monad.Reader
> import Control.Monad.Writer
> import Data.Graph (stronglyConnCompR, SCC(..))
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe (fromMaybe)
> import Printer.Common (pprList')
> import Printer.XMPEG
> import Syntax.Specialized
> import Syntax.XMPEG

> import Debug.Trace

We implement a limited lambda-lifting pass for XMPEG.  The goal is to lift recursive definitions to
the top-level, as MIL only supports recursive definition in the global scope.  However, we do not
try to lift other definitions (or, indeed, lambda-expressions) to the top level.

Let's reconsider the initial scenario for lambda-lifting.

    let f x = g x + y
        g x = f x + z
    in M

We intend to produce new top-level definitions

    f' y z x = g y z x + y
    g' y z x = f y z x + z

What about the source expression?  As I read the Gofer report, we might expect it to be

    M[f' y z/f, g' y z/g]

But that's not safe for call-by-value---and it requires doing substitution.  What if instead we did
the following?

    let f = f' y z
        g = g' y z in M

Now this is safe for call-by-value, and I think it avoids any need to do source-level substitutions.
Of course, a final problem is that we need to compute new types for the new bindings, so we track
the types of local bindings as we go.

> type TyEnv = Map Id Type
> type CtorEnv = [((Id, [Type]), [Type])]
> data Envs = Envs{ locals :: TyEnv, globals :: TyEnv, ctors :: CtorEnv, binds :: [(Id, Id)] }
> newtype M a = M{ runM :: WriterT [Defn] (ReaderT Envs Base) a }
>     deriving (Functor, Applicative, Monad, MonadBase, MonadWriter [Defn], MonadReader Envs)

> bind :: (TyEnv -> TyEnv) -> M t -> M t
> bind f = local (\envs -> envs{ locals = f (locals envs) })

> liftDefns :: [Defn] -> M [Defn]
> liftDefns ds =
>     do ds' <- concatMapM liftDefnGroup dss
>        return (primitives ++ ds')
>     where (primitives, defns) = foldr f ([], []) ds
>               where f d@(Defn _ _ (Left _)) (prims, real) = (d : prims, real)
>                     f d@(Defn _ _ (Right _)) (prims, real) = (prims, d : real)
>           sccNodes = [(d, name, freeVariables body) | d@(Defn name _ (Right (Gen _ _ body))) <- defns]
>           dss = stronglyConnCompR sccNodes

>           liftDefnGroup (AcyclicSCC (Defn name tys rhs, _, _)) =
>               case rhs of
>                 Left _ -> return [Defn name tys rhs]
>                 Right (Gen [] [] body) ->
>                     do body' <- liftDefnsFrom body
>                        return [Defn name tys (Right (Gen [] [] body'))]
>           liftDefnGroup (CyclicSCC [(Defn name (Forall [] [] t) (Right (Gen [] [] body)), _, fvs)]) =
>               do env <- asks locals
>                  let local = Map.keys env
>                      fvs' = filter (`elem` local) fvs
>                      ts = map (\v -> fromMaybe (error ("Unknown variable: " ++ show (ppr v))) (Map.lookup v env)) fvs'
>                  name' <- fresh name
>                  body' <- liftDefnsFrom body
>                  let localDefn = Defn name (Forall [] [] t) (Right (Gen [] [] (foldl EApp (ELamVar name') (map ELamVar fvs'))))
>                  tell [Defn name' (Forall [] [] (allTo ts t)) (Right (Gen [] [] (addBindings (Decls [localDefn]) (lambdas fvs' ts body'))))]
>                  return [localDefn]
>           liftDefnGroup (CyclicSCC triples) =
>               do env <- asks locals
>                  let local = Map.keys env
>                      fvs' = filter (`elem` local) fvs
>                      us = map (\v -> fromMaybe (error ("Unknown variable: " ++ show (ppr v))) (Map.lookup v env)) fvs'
>                      ts' = [allTo us t | t <- ts]
>                  names' <- mapM fresh names
>                  let localDefns = [Defn name (Forall [] [] t) (Right (Gen [] [] (foldl EApp (ELamVar name') (map ELamVar fvs')))) | (name, name', t) <- zip3 names names' ts]
>                      oneDefn (name', t', Defn name t (Right (Gen [] [] body))) =
>                         do body' <- liftDefnsFrom body
>                            tell [Defn name' (Forall [] [] t') (Right (Gen [] [] (lambdas fvs' us (addBindings (Decls localDefns) body'))))]
>                  mapM_ oneDefn (zip3 names' ts' ds)
>                  return localDefns
>               where (ds, names, ts, fvss) = unzip4 [(d, name, t, fvs) | (d@(Defn _ (Forall [] [] t) _), name, fvs) <- triples]
>                     fvs = concat fvss

>           arrTy = TyCon (Kinded (Ident "->" 0 (Just (Fixity RightAssoc 5))) (KFun KStar (KFun KStar KStar)))
>           allTo :: [Type] -> Type -> Type
>           allTo ts t = foldr (\t t' -> TyApp (TyApp arrTy t) t') t ts
>           lambdas [] _ e = e
>           lambdas (x:xs) (t:ts) e = ELam x t (lambdas xs ts e)
>           addBindings ds (ELam x t b) = ELam x t (addBindings ds b)
>           addBindings ds e = ELet ds e

In the following, I'm assuming that we have no remaining nests of the sort (let x = y; y = x in E)

> inlineVariableBindings :: [Defn] -> ([Defn] -> M t) -> M t
> inlineVariableBindings ds f = local (\envs -> envs{ binds = s ++ binds envs }) (f ds')
>     where split (Defn x _ (Right (Gen _ _ (ELamVar y)))) (s, ds)
>               | x /= y    = ((x, y) : s, ds)
>           split d (s, ds) = (s, d : ds)
>           (s, ds') = foldr split ([], []) ds

With the work out of the way, we can implement a straight-forward pass over the syntax tree.

> class HasDefinitions t
>     where liftDefnsFrom :: t -> M t

> instance HasDefinitions Expr
>     where liftDefnsFrom (ELamVar x) = asks (ELamVar . flip replacement x . binds)
>           liftDefnsFrom (ELam x t e) = bind (Map.insert x t) (liftM (ELam x t) (liftDefnsFrom e))
>           liftDefnsFrom (ELet (Decls ds) e) =
>               do ds' <- liftDefns ds
>                  inlineVariableBindings ds' $ \ds'' ->
>                      if null ds''
>                      then liftDefnsFrom e
>                      else bind (Map.union (Map.fromList [(name, ty) | Defn name (Forall [] [] ty)  _ <- ds'']))
>                                (liftM (ELet (Decls ds'')) (liftDefnsFrom e))
>           liftDefnsFrom (EMatch m) = liftM EMatch (liftDefnsFrom m)
>           liftDefnsFrom (EApp e e') = liftM2 EApp (liftDefnsFrom e) (liftDefnsFrom e')
>           liftDefnsFrom (EBind ta tb tm me x e e') = liftM2 (EBind ta tb tm me x) (liftDefnsFrom e) (liftDefnsFrom e')

Base cases: ELamVar, Bits, ECon
Cases that shouldn't be present any more: ELetVar, EMethod, ELetTypes, ESubst

>           liftDefnsFrom e = return e

> instance HasDefinitions Match
>     where liftDefnsFrom MFail = return MFail
>           liftDefnsFrom (MCommit e) = liftM MCommit (liftDefnsFrom e)
>           liftDefnsFrom (MElse m m') = liftM2 MElse (liftDefnsFrom m) (liftDefnsFrom m')
>           liftDefnsFrom (MGuarded g m) = do g' <- liftDefnsFrom g
>                                             guarded g' m

Perhaps we should store the types of pattern-bound variables in constructor patterns?

> guarded (GFrom p x) m =
>     do bs <- boundBy p
>        x' <- asks (flip replacement x . binds)
>        bind (Map.union bs) (liftM (MGuarded (GFrom p x')) (liftDefnsFrom m))
>     where boundBy PWild = return Map.empty
>           boundBy (PVar x t) =
>                  return (Map.singleton x t)
>           boundBy (PCon (Inst id ts []) xs) =
>               do ts <- asks (fromMaybe (error ("Unknown constructor: " ++ show (ppr (Inst id ts [])))) . lookup (id, ts) . ctors)
>                  return (Map.fromList (zip xs ts))
> guarded (GLet (Decls ds)) m =
>     do ds' <- liftDefns ds
>        inlineVariableBindings ds' $ \ds'' ->
>            if null ds''
>            then liftDefnsFrom m
>            else bind (Map.union (Map.fromList [(name, ty) | Defn name (Forall [] [] ty)  _ <- ds'']))
>                      (liftM (MGuarded (GLet (Decls ds''))) (liftDefnsFrom m))

Cases that shouldn't be present: GSubst, GLetTypes

> instance HasDefinitions Guard
>     where liftDefnsFrom (GLet (Decls defns)) = liftM (GLet . Decls) (liftDefns defns)
>           liftDefnsFrom g = return g

> liftDefinitions :: Pass s Specialized Specialized
> liftDefinitions (Specialized tds entries (Decls defns)) =
>     liftBase $ do ((entries', defns'), defns'') <- runReaderT (runWriterT (runM go)) (Envs Map.empty globals cenv [])
>                   return (Specialized tds entries' (Decls (defns' ++ defns'')))
>     where globals = Map.fromList [(name, t) | Defn name (Forall [] [] t) _ <- defns]
>           cenv = concatMap ctorsFrom tds
>               where ctorsFrom (Datatype _ ts ctors) = [((ctorName, ts), args) | (ctorName, _, _, args) <- ctors]
>                     ctorsFrom (Bitdatatype tyName _ bitctors) = [((ctorName, []), [typeFrom ctorName]) | (ctorName, _, _) <- bitctors]
>                         where bitdataCaseTy = TyCon (Kinded "BitdataCase" (KFun KStar (KFun KLabel KStar)))
>                               typeFrom ctorName = (bitdataCaseTy `TyApp` (TyCon (Kinded tyName KStar))) `TyApp` TyLabel ctorName
>                     ctorsFrom _ = []  -- structs and areas
>           topDefn d@(Defn _ _ (Left _)) = return d
>           topDefn (Defn name tys (Right (Gen [] [] e))) =
>               liftM (Defn name tys . Right . Gen [] []) (liftDefnsFrom e)
>           go = do defns' <- mapM topDefn defns
>                   entries' <- mapM liftDefnsFrom entries
>                   return (entries', defns')
