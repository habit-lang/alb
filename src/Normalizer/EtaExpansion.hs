{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Normalizer.EtaExpansion where

import Common
import Control.Monad.Reader
import Data.Maybe (fromMaybe)
import Printer.XMPEG
import Syntax.Specialized
import Syntax.XMPEG

import Prelude hiding (pure)


type CtorMap = [((Id, [Type]), [Type])]
type PrimMap = [(Id, [Type])]
newtype M a = M{ runM :: ReaderT (CtorMap, PrimMap) Base a }
    deriving (Functor, Applicative, Monad, MonadReader (CtorMap, PrimMap), MonadBase)

etaExpand :: [Type] -> Expr -> M Expr
etaExpand ts e = loop ts [] e
    where loop [] xs e = return (foldl (\e x -> EApp e (ELamVar x)) e (reverse xs))
          loop (t:ts) xs e = do x <- fresh "x"
                                e' <- loop ts (x:xs) e
                                return (ELam x t e')

expandCtor :: Id -> [Type] -> Int -> Expr -> M Expr
expandCtor ctor us n e =
    do ts <- asks (fromMaybe (error ("Unknown constructor: " ++ fromId ctor)) . lookup (ctor, us) . fst)
       etaExpand (drop n ts) e

expandPrim :: Id -> Int -> Expr -> M Expr
expandPrim prim n e =
    do ts <- asks (fromMaybe (error ("Unknown primitive: " ++ fromId prim)) . lookup prim . snd)
       etaExpand (drop n ts) e

class HasConstructors t
    where fullyApplied :: t -> M t

instance HasConstructors Expr
    where fullyApplied e@(ELamVar x) =
              do prims <- asks (map fst . snd)
                 if x `elem` prims then expandPrim x 0 e else return e
          fullyApplied e@(ECon (Inst ctor ts [])) = expandCtor ctor ts 0 e
          fullyApplied e@(ECon (Inst ctor _ _)) = error ("Constructors.hs:34 " ++ show (ppr e))
          fullyApplied e@EApp{} =
              do args' <- mapM fullyApplied args
                 prims <- asks (map fst . snd)
                 case op of
                   ECon (Inst ctor ts []) -> expandCtor ctor ts (length args) (foldl EApp op args)
                   ECon (Inst ctor _ _) -> error ("Constructors.hs:39 " ++ show (ppr e))
                   ELamVar x | x `elem` prims -> expandPrim x (length args) (foldl EApp (ELamVar x) args)
                   _ -> do op' <- fullyApplied op
                           return (foldl EApp op' args')
              where (op, args) = flattenApp e
          fullyApplied (ELam x t e) = liftM (ELam x t) (fullyApplied e)
          fullyApplied (ELet ds e) = liftM2 ELet (fullyApplied ds) (fullyApplied e)
          fullyApplied (EMatch m) = liftM EMatch (fullyApplied m)
          fullyApplied (EBind ta tb tm evm x e k) = liftM2 (EBind ta tb tm evm x) (fullyApplied e) (fullyApplied k)
          fullyApplied e = return e -- includes both variables and impossible (because post-specialization) cases

instance HasConstructors Match
    where fullyApplied MFail = return MFail
          fullyApplied (MCommit e) = liftM MCommit (fullyApplied e)
          fullyApplied (MElse m m') = liftM2 MElse (fullyApplied m) (fullyApplied m')
          fullyApplied (MGuarded g m) = liftM2 MGuarded (fullyApplied g) (fullyApplied m)

instance HasConstructors Guard
    where fullyApplied (GLet ds) = liftM GLet (fullyApplied ds)
          fullyApplied g         = return g

instance HasConstructors Decls
    where fullyApplied (Decls ds) = liftM Decls (mapM defn ds)
              where defn d@(Defn _ _ (Left _)) = return d
                    defn (Defn name tys (Right (Gen [] [] body))) = liftM (Defn name tys . Right . Gen [] []) (fullyApplied body)

expand :: Pass s Specialized Specialized
expand (Specialized tds entries ds@(Decls defns)) =
    liftBase $
    do entries' <- runReaderT  (runM (mapM fullyApplied entries)) (cenv, penv)
       ds' <- runReaderT (runM (fullyApplied ds)) (cenv, penv)
       return (Specialized tds entries' ds')
    where cenv = concatMap ctorsFrom tds
              where ctorsFrom (Datatype _ ts ctors) = [((ctorName, ts), args) | (ctorName, _, _, args) <- ctors]
                    ctorsFrom (Bitdatatype tyName _ bitctors) = [((ctorName, []), [typeFrom ctorName]) | (ctorName, _, _) <- bitctors]
                        where bitdataCaseTy = TyCon (Kinded "BitdataCase" (KFun KStar (KFun KLabel KStar)))
                              typeFrom ctorName = (bitdataCaseTy `TyApp` (TyCon (Kinded tyName KStar))) `TyApp` TyLabel ctorName
                    ctorsFrom _ = []  -- structs and areas
          penv = [(name, argTypes t) | Defn name (Forall [] [] t) (Left (_, _)) <- defns]
              where argTypes (TyApp (TyApp (TyCon (Kinded (Ident "->" _ _) _)) t) u) = t : argTypes u
                    argTypes _ = []
