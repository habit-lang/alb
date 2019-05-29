{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies,
       GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeSynonymInstances,
       UndecidableInstances, OverloadedStrings #-}
module Analyzer.FunctionalNotation (rewriteFunctionalNotation, emptyFunctionalNotationState, TConEnv(..), Arity(..)) where

import Common
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List ((\\), nub)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Printer.Common
import Printer.IMPEG hiding (paramName)
import Syntax.IMPEG
import qualified Syntax.IMPEG as IMPEG
import Syntax.IMPEG.TSubst

import Debug.Trace

-- Basically proceeds as follows: First, collect an environment identifying classes with their
-- arities; second, identify "top-level" occurrences of types---in signatures, constructors, and so
-- forth; for each top-level occurence, collect any occurences of arity-n classes with n-1
-- parameters and then add corresponding constraints to the top-level type.

type TConEnv = Map Id Arity
data Arity = ClassArity Int Bool | TypeArity Int | None deriving Show
type PrimitiveClasses = [Id]

-- Once again with the monads
newtype M t = M { runM :: ReaderT (TConEnv, PrimitiveClasses) Base t }
    deriving (Functor, Applicative, Monad, MonadReader (TConEnv, PrimitiveClasses), MonadBase)

arity :: MonadReader (TConEnv, PrimitiveClasses) m => Id -> m Arity
arity name = asks (fromMaybe None . Map.lookup name . fst)

isPrimitive :: MonadReader (TConEnv, PrimitiveClasses) m => Id -> m Bool
isPrimitive name = asks ((name `elem`)  . snd)

----------------------------------------------------------------------------------------------------
-- We'll start with the rewriting-types-and-collecting-predicates phase

rewriteType :: Located (Type Id) -> WriterT [(Located (PredType Pred Id), Id)] M (Located (Type Id))
rewriteType t@(At loc (TyApp t0 t1)) =
    failAt loc $
    case flattenType t of
      (At l (TyCon name), args) ->
          do args' <- mapM rewriteType args
             a <- arity name
             case a of
               ClassArity n True
                   | n > length args' + 1 ->
                       failAt loc $ failWithS ("Insufficient number of arguments for functional notation with class " ++ fromId name)
                   | n == length args' + 1 ->
                       do v <- lift (fresh "f")
                          tell [(At l $ Pred name (args' ++ [At loc (TyVar v)]) Holds, v)]
                          return (At loc (TyVar v))
                   | otherwise ->
                       do v <- lift (fresh "f")
                          tell [(At l $ Pred name (take (n - 1) args' ++ [At loc (TyVar v)]) Holds, v)]
                          return (foldl (@@) (At loc (TyVar v)) (drop (n - 1) args'))
               ClassArity n _ -> failAt loc $ failWithS ("Invalid use of functional notation with class " ++ fromId name)
               TypeArity n ->
                   if length args' > n
                   then failAt loc $ failWithS ("Too many arguments to type constructor " ++ fromId name)
                   else return (foldl (@@) (At loc (TyCon name)) args')
               -- although one imagines these errors would have been caught in scope resolution
               None -> failAt loc $ failWithS ("Unbound type constructor '" ++ fromId name ++ "'")
          where t @@ t' = at t (TyApp t t')
      _ -> do t' <- liftM2 TyApp (rewriteType t0) (rewriteType t1)
              return (At loc t')
rewriteType t@(At loc (TyCon name)) =
    failAt loc $
    do a <- arity name
       case a of
         ClassArity 1 True ->
             do v <- lift (fresh "f")
                tell [(introduced $ Pred name [At loc (TyVar v)] Holds, v)]
                return (At loc (TyVar v))
         ClassArity 1 False ->
             failWithS "Invalid use of functional notation"
         _ -> return t
rewriteType (At loc (TyKinded t k)) =
    do t' <- rewriteType t
       return (At loc (TyKinded t' k))
rewriteType t = return t

rewritePredicate :: Located (PredType PredFN Id) -> WriterT [(Located (PredType Pred Id), Id)] M (Located (PredType Pred Id))
rewritePredicate (At loc (PredFN name args marg flag)) =
    failAt loc $
    do args' <- mapM rewriteType args
       a <- arity name
       case a of
         ClassArity n b ->
             case marg of
               Nothing  | length args' /= n     -> failWithS "Incorrect number of predicate arguments"
                        | otherwise             -> return (At loc (Pred name args' flag))
               Just arg | not b                 -> failWithS "Invalid use of functional notation"
                        | length args' /= n - 1 -> failWithS "Incorrect number of predicate arguments"
                        | otherwise             -> do arg' <- rewriteType arg
                                                      return (At loc (Pred name (args' ++ [arg']) flag))
         TypeArity _ -> failWithS "Expected class name but found type constructor"
         None -> failWithS ("Unknown class name \"" ++ fromId name ++ "\"")

rewritePredicates :: [Located (PredType PredFN Id)] -> M ([Located (PredType Pred Id)], [Id])
rewritePredicates ps =
    do (ps', qs) <- runWriterT (mapM rewritePredicate ps)
       let (rs, vs) = unzip qs
       return (ps' ++ rs, vs)

rewriteQualType :: Qual (PredType PredFN Id) (Type Id) -> M (Qual (PredType Pred Id) (Type Id), [Id])
rewriteQualType (ps :=> t) =
    do (t', qs) <- runWriterT (rewriteType t)
       (ps', qs') <- runWriterT (mapM rewritePredicate ps)
       let (rs, vs) = unzip qs
           (rs', vs') = unzip qs'
       return ((ps' ++ rs ++ rs') :=> t', vs ++ vs')

rewriteScheme :: [Id] -> Scheme PredFN Id -> M (Scheme Pred Id)
rewriteScheme ws s@(Forall qvars qt) =
    do (qt', vs) <- rewriteQualType qt
       let qvars' = filter (`notElem` ws) vs
       let s = new (zip qvars' (map TyGen [length qvars..]))
       return (Forall (qvars ++ qvars') (s # qt'))

rewriteKScheme :: [Id] -> KScheme (Scheme PredFN Id) -> M (KScheme (Scheme Pred Id))
rewriteKScheme ws (ForallK kvars tys) =
    ForallK kvars `fmap` rewriteScheme ws tys

----------------------------------------------------------------------------------------------------
-- The remainder of the process involves walking over the syntax tree, calling rewrite whenever we
-- encounter a qualified type.  This is not tedious.

class HasTypeFunctions t u | t -> u
    where rewrite :: t -> M u

-- Instances for common types
instance HasTypeFunctions t u => HasTypeFunctions (Located t) (Located u)
    where rewrite (At loc t) = failAt loc (At loc `fmap` rewrite t)

instance HasTypeFunctions t u => HasTypeFunctions (Maybe t) (Maybe u)
    where rewrite Nothing  = return Nothing
          rewrite (Just k) = Just `fmap` rewrite k

instance HasTypeFunctions (Expr PredFN Id) (Expr Pred Id)
    where rewrite (ELet decls body)         = liftM2 ELet (rewrite decls) (rewrite body)
          rewrite (ELam var body)           = liftM (ELam var) (rewrite body)
          rewrite (EVar id)                 = return (EVar id)
          rewrite (ECon id)                 = return (ECon id)
          rewrite (EBitCon id es)           = EBitCon id `fmap` mapSndM rewrite es
          rewrite (EBits value size)        = return (EBits value size)
          rewrite (EMatch m)                = liftM EMatch (rewrite m)
          rewrite (EApp e e')               = liftM2 EApp (rewrite e) (rewrite e')
          rewrite (EBind mvar e body)       = liftM2 (EBind mvar) (rewrite e) (rewrite body)
          rewrite (EStructInit name fields) = liftM (EStructInit name) (mapSndM rewrite fields)

instance HasTypeFunctions (Match PredFN Id) (Match Pred Id)
    where rewrite MFail          = return MFail
          rewrite (MCommit e)    = liftM MCommit (rewrite e)
          rewrite (MElse m m')   = liftM2 MElse (rewrite m) (rewrite m')
          rewrite (MGuarded g m) = liftM2 MGuarded (rewrite g) (rewrite m)

instance HasTypeFunctions (Guard PredFN Id) (Guard Pred Id)
    where rewrite (GFrom p e) = liftM2 GFrom (rewrite p) (rewrite e)
          rewrite (GLet ds)   = liftM GLet (rewrite ds)

instance HasTypeFunctions (Pattern PredFN Id) (Pattern Pred Id)
    where rewrite PWild           = return PWild
          rewrite (PVar id)       = return (PVar id)
          rewrite (PCon id ps)    = return (PCon id ps)
          rewrite (PTyped p ty)   = liftM2 PTyped (rewrite p) (rewriteScheme [] ty)
          rewrite (PGuarded p g)  = liftM2 PGuarded (rewrite p) (rewrite g)

instance HasTypeFunctions (Signature PredFN Id) (Signature Pred Id)
    where rewrite (Signature id ty) = liftM  (Signature id) (rewriteKScheme [] ty)

instance HasTypeFunctions (Function PredFN Id) (Function Pred Id)
    where rewrite (name, params, body) =
              do body' <- rewrite body
                 return (name, params, body')

instance HasTypeFunctions (TypingGroup PredFN Id) (TypingGroup Pred Id)
    where rewrite (Explicit f tys)         = liftM2 Explicit (rewrite f) (rewriteKScheme [] tys)
          rewrite (Implicit fs)            = liftM Implicit (mapM rewrite fs)
          rewrite (Pattern p e signatures) = liftM3 Pattern (rewrite p) (rewrite e) (mapM rewrite signatures)
          rewrite (PrimValue s name)       = liftM2 PrimValue (rewrite s) (return name)

instance HasTypeFunctions (Decls PredFN Id) (Decls Pred Id)
    where rewrite (Decls groups) = liftM Decls (mapM rewrite groups)

rewriteCtor :: (HasTypeVariables t Id, HasTypeVariables u Id)
  => ([Located t]
  -> M ([Located u], [(Located (PredType Pred Id), Id)]))
  -> Ctor Id (PredType PredFN Id) t
  -> M (Ctor Id (PredType Pred Id) u)
rewriteCtor f (Ctor name univs exis preds fields) =
    do let tyvars  = map TyVar (univs ++ exis)
           preds'  = inst tyvars preds
           fields' = inst tyvars fields
       (fields'', qs') <- f fields'
       let (qs, vs) = unzip qs'
       (ps', vs') <- rewritePredicates preds
       let newVs = vs ++ vs'
       return (Ctor name (univs ++ newVs) exis
                         (gen 0 (univs ++ newVs) (ps' ++ qs))
                         (gen 0 (univs ++ newVs) fields''))

instance HasTypeFunctions (TopDecl PredFN Id (Either KId Id)) (TopDecl Pred Id (Either KId Id))
    where rewrite (Datatype name params constraints ctors drv) =
              do ctors' <- mapM (rewriteCtor (runWriterT . mapM rewriteType)) ctors
                 (constraints', vs) <- rewritePredicates constraints
                 when (not (null vs)) (error "FunctionalNotation.hs:209")
                 return (Datatype name params constraints' ctors' drv)
              where enclosing = map (paramName . dislocate) params

          rewrite (Bitdatatype name size ctors drv) =
              do size' <- case size of
                            Nothing -> return Nothing
                            Just size -> Just `fmap` rewriteScheme [] size
                 ctors' <- mapM (rewriteCtor (runWriterT . mapM rewriteBitdataField)) ctors
                 return (Bitdatatype name size' ctors' drv)
              where rewriteBitdataField :: Located (BitdataField Id) -> WriterT [(Located (PredType Pred Id), Id)] M (Located (BitdataField Id))
                    rewriteBitdataField (At loc (ConstantField e))           = return (At loc (ConstantField e))
                    rewriteBitdataField (At loc (LabeledField name ty init)) = do ty' <- rewriteType ty
                                                                                  return (At loc (LabeledField name ty' init))
          rewrite (Struct name size ctor align drv) =
              do size' <- case size of
                            Nothing -> return Nothing
                            Just size -> Just `fmap` rewriteScheme [] size
                 ctor' <- rewriteCtor (runWriterT . mapM rewriteStructRegion) ctor
                 align' <- case align of
                             Nothing -> return Nothing
                             Just (At loc align) -> (Just . At loc) `fmap` rewriteScheme [] align
                 return (Struct name size' ctor' align' drv)
              where rewriteStructRegion :: Located (StructRegion Id) -> WriterT [(Located (PredType Pred Id), Id)] M (Located (StructRegion Id))
                    rewriteStructRegion (At loc (StructRegion nameInit ty)) = do ty' <- rewriteType ty
                                                                                 return (At loc (StructRegion nameInit ty'))
          rewrite (Area v namesAndInits ty align) =
              do ty' <- rewriteScheme [] ty
                 align' <- case align of
                             Nothing -> return Nothing
                             Just (At loc align) -> (Just . At loc) `fmap` rewriteScheme [] align
                 return (Area v namesAndInits ty' align')

          rewrite (Class id params constraints methods defaults) =
              liftM2 (Class id params constraints) (mapM rewriteSignature methods) (mapM rewrite defaults)
              where pnames = map (paramName . dislocate) params
                    rewriteSignature (Signature name tys) =
                        Signature name `fmap` rewriteKScheme pnames tys


          rewrite (Instance name className chain) = Instance name className `fmap` mapM rewriteClause chain
              where rewriteClause (hypotheses :=> conclusion@(At _ (PredFN className _ _ _)), methods) =
                        do p <- isPrimitive className
                           when p $ failWithS "Instance defined for primitive class"
                           (hypotheses', _) <- rewritePredicates hypotheses
                           (conclusion', hypsAndVars) <- runWriterT (rewritePredicate conclusion)
                           let hypotheses'' = map fst hypsAndVars
                           methods' <- mapM rewrite methods
                           return ((hypotheses' ++ hypotheses'') :=> conclusion', methods')

          rewrite (Require ps qs) =
              do (ps', _) <- rewritePredicates (map snd ps)
                 (qs', _) <- rewritePredicates qs
                 ns <- replicateM (length ps') (fresh "require")
                 return (Require (zip ns ps') qs')

instance HasTypeFunctions (Primitive PredFN Id) (Primitive Pred Id)
    where rewrite (PrimCon (Signature name tys) impl)         = do tys' <- rewriteKScheme [] tys
                                                                   return (PrimCon (Signature name tys') impl)
          rewrite (PrimType t k)                              = return (PrimType t k)
          rewrite (PrimClass name params constraints methods) = PrimClass name params constraints `fmap` mapM rewrite methods

instance HasTypeFunctions (Program PredFN Id (Either KId Id)) (Program Pred Id (Either KId Id))
    where rewrite (Program decls topDecls primitives) = liftM3 Program (rewrite decls) (mapM rewrite topDecls) (mapM rewrite primitives)

emptyFunctionalNotationState :: (TConEnv, PrimitiveClasses)
emptyFunctionalNotationState = (Map.empty, [])

rewriteFunctionalNotation :: Has s (TConEnv, PrimitiveClasses) => Pass s (Program PredFN Id (Either KId Id)) (Program Pred Id (Either KId Id))
rewriteFunctionalNotation = up (\p -> PassM (StateT (\env0 -> let env = build p env0
                                                              in do v <- runReaderT (runM (rewrite p)) env
                                                                    return (v, env))))
    where build p (arities0, primitives0) =
              ( Map.union arities0 (Map.fromList (catMaybes (map (arities . dislocate) (topDecls p) ++ map (primitiveArities . dislocate) (primitives p))))
              , [id | At _ (PrimClass id _ _ _) <- primitives p] ++ primitives0 )

          arities (Datatype name params _ _ _)        = Just (name, TypeArity (length params))
          arities (Bitdatatype name _ _ _)            = Just (name, TypeArity 0)
          arities (Struct name _ _ _ _)               = Just (name, TypeArity 0)
          arities (Area {})                           = Nothing
          arities (Class name params constraints _ _) = Just (name, ClassArity n isFunctional)
              where n            = length params
                    isFunctional = not (null [fd | At _ (Fundep fd) <- constraints, fd `determines` (n - 1)])
          arities (Instance {})                       = Nothing
          arities (Require {})                        = Nothing

          primitiveArities (PrimCon {})                          = Nothing
          primitiveArities (PrimType name k)                     = Just (name, TypeArity (countParams k))
              where countParams (KFun _ k) = 1 + countParams k
                    countParams k          = 0
          primitiveArities (PrimClass name params constraints _) = Just (name, ClassArity n isFunctional)
              where n            = length params
                    isFunctional = not (null [ fd | At _ fd <- constraints, fd `determines` (n - 1)])
