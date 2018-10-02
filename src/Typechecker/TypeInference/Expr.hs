{-# LANGUAGE FlexibleContexts #-}

module Typechecker.TypeInference.Expr where

import Prelude hiding ((<$>))

import Common
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Printer.Common hiding (empty)
import Syntax.Common
import Syntax.IMPEG
import Syntax.IMPEG.TSubst
import qualified Syntax.XMPEG as X
import qualified Syntax.XMPEG.TSubst as X
import Typechecker.TypeInference.Base

----------------------------------------------------------------------------------------------------

checkExpr :: Located Exp -> Ty -> M (X.Expr, Preds)

checkExpr (At loc (ELet ds body)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do (ds', ps, vals) <- checkDecls ds
       (body', qs) <- binds vals (checkExpr body expected)
       return (X.ELet ds' body', ps ++ qs)

checkExpr (At loc (ELam var body)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do argTy@(TyVar arg) <- newTyVar KStar
       resTy             <- newTyVar KStar
       unifies expected (argTy `to` resTy)
       (body', ps) <- bind var (LamBound argTy) (checkExpr body resTy)
       return (X.ELam var (X.TyVar arg) body', ps)

checkExpr (At loc (EVar name)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected <+> "for variable" <+> ppr name)) $
    do b <- bindingOf name
       case b of
         LamBound ty ->
             do unifies expected ty
                return (X.ELamVar name, [])
         LetBound tys ->
             do (kvars, kids, ps :=> At _ ty) <- instantiate tys
                unifies expected ty
                evNames <- freshFor "e" ps
                let preds = zip evNames [At loc p | At _ p <- ps]
                trace (show (hang 4 (text "At" <+> ppr loc <$>
                                     ppr name <+> text "gets type" <+> ppr ty <$>
                                     text "and introduces" <$>
                                     vcat [ppr id <::> ppr p | (id, p) <- preds])))
                      (return ( X.ELetVar (X.Inst name (map X.TyVar kids) (map X.EvVar evNames))
                              , preds ))

checkExpr (At loc (ECon name)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do b <- bindingOf name
       case b of
         LamBound _ -> error "Constructor name associated with lambda-bound type"
         LetBound tys ->
             do (kvars, kids, ps :=> At _ ty) <- instantiate tys
                unifies expected ty
                evNames <- freshFor "e" ps
                return ( X.ECon (X.Inst name (map X.TyVar kids) (map X.EvVar evNames))
                       , zip evNames [At loc p | At _ p <- ps])

checkExpr (At loc (EBitCon ctor fs)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do -- Check that there are no duplicates in the list of named fields:
       let fsNames = [ id | (id, _) <- fs ]
           dups    = duplicates fsNames
       when (not (null dups)) $
         failWithS ("Multiple values for " ++ commaSep dups)

       -- Lookup information about the fields for this constructor:
       (ty, fields) <- gets (fromMaybe (error ("Unknown bitdata ctor " ++ fromId ctor)) .
                             Map.lookup ctor .
                             bitdataCtors)
       unifies expected ty
       let notFields = fsNames \\ [ n | (n, _, _) <- fields ]
       when (not (null notFields)) $
         failWithS ("There are no fields called " ++ commaSep notFields ++ " for constructor " ++ fromId ctor)

       -- Compute full list of field values using default initial values where necessary:
       (es', pss) <- unzip `fmap` mapM fieldFor fields
       let cty  = [ t | (_, t, _) <- fields ] `allTo` (bitdataCaseTy @@ ty @@ TyLabel ctor)
           prim = X.ELetVar (X.Inst "constructBitdata" [convert cty] [])
           cons = X.ECon (X.Inst ctor [] []) -- constructor is monomorphic
       return (X.EBitCon ctor es', concat pss)

    where fieldFor :: (Id, Ty, Maybe Id) -> M ((Id, X.Expr), Preds)
          fieldFor (fieldName, fieldTy, defaultId) =
              case lookup fieldName fs of
                Just e ->
                    do (e', ps) <- checkExpr e fieldTy
                       return ((fieldName, e'), ps)
                       -- can only substitute for variables in ty'; this ensures
                       -- that the value is at least as polymorphic as the field
                       -- type.  The big need for this is in literal types,
                       -- which are still fairly polymorphic.
                Nothing ->
                    case defaultId of
                      Nothing -> failWithS ("Uninitialized field " ++ fromId fieldName)
                      Just id -> return ((fieldName, X.ELetVar (X.Inst id [] [])), [])

checkExpr (At loc (EBits value size)) expected =
    do unifies expected (bitTy @@ TyNat (fromIntegral size))
       return (X.EBits value size, [])

checkExpr (At loc (EMatch m)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do (m', ps) <- checkMatch m expected
       return (X.EMatch m', ps)

checkExpr (At loc (EApp f a)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do t <- newTyVar KStar
       (f', ps) <- checkExpr f (t `to` expected)
       (a', qs) <- checkExpr a t
       return (X.EApp f' a', ps ++ qs)

checkExpr (At loc (EBind v e rest)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do -- variables names are based on (>>=) :: m a -> (a -> m b) -> m b
       tya <- newTyVar KStar
       tyb <- newTyVar KStar
       tym <- newTyVar (KStar `KFun` KStar)
       unifies expected (tym @@ tyb)
       (e', ps) <- checkExpr e (tym @@ tya)
       (rest', qs) <- bind v (LamBound tya) (checkExpr rest expected)
       evar <- fresh "e"
       return ( X.EBind (convert tya) (convert tyb) (convert tym) (X.EvVar evar) v e' rest'
              , (evar, At loc (procPred (At loc tym))) : ps ++ qs )

checkExpr (At loc (EStructInit name inits)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do -- Check that there are no duplicates in the list of named fields:
       let initNames = [ id | (At _ id, _) <- inits ]
           dups      = duplicates initNames
       when (not (null dups)) $
         failWithS ("Multiple initializers for fields called " ++ commaSep dups)

       -- Lookup information about the regions for this structure:
       (ty, regions) <- gets (fromMaybe (error ("Unknown struct name " ++ fromId name)) .
                              Map.lookup name .
                              structRegions)
       unifies expected (TyApp (At loc initTy) (introduced ty))
       let notFields = initNames \\ [ n | (Just n, _, _) <- regions ]
       when (not (null notFields)) $
         failWithS ("There are no fields called " ++ commaSep notFields ++ " for structure " ++ fromId name)

       -- Compute a full list of initializers for this structure:
       (fs, pss) <- unzip `fmap` mapM initFor regions
       return (X.EStructInit name (catMaybes fs), concat pss)

    where initFor :: (Maybe Id, Ty, Maybe Id) -> M (Maybe (Id, X.Expr), Preds)
          initFor (mregName, regTy, mregInit)
            = case mregName of
                Nothing      ->  -- unnamed region, use default initializer
                  defaultInitializer
                Just regName ->  -- named field
                  case [ e | (At _ n, e) <- inits, n==regName ] of  -- look for used specified initializer
                    (e : _) ->
                      do (e', ps) <- checkExpr e initType -- confirm that initializer has correct type
                                                          -- TODO: is this correct?
                         return (Just (regName, e'), ps)
                    [] ->
                      case mregInit of -- look for an initializer in the structure definition
                        Just defInit -> return (Just (regName, X.ELetVar (X.Inst defInit [] [])), [])
                        Nothing      -> defaultInitializer
              where
                initType = TyApp (At loc initTy) (At loc regTy)
                defaultInitializer :: M (Maybe (Id, X.Expr), Preds)
                defaultInitializer  = do evar <- fresh "e"      -- evidence for Init ty
                                         return (Nothing, [(evar, At loc (initablePred (At loc regTy)))])

----------------------------------------------------------------------------------------------------

checkMatch :: Match Pred KId -> Ty -> M (X.Match, Preds)
checkMatch MFail expected =
    return (X.MFail, [])
checkMatch (MCommit e) expected =
    do (e', ps) <- checkExpr e expected
       return (X.MCommit e', ps)
checkMatch (MElse m n) expected =
    do (m', ps) <- checkMatch m expected
       (n', qs) <- checkMatch n expected
       return (X.MElse m' n', ps ++ qs)
checkMatch (MGuarded (GLet decls) m) expected =
    do (decls', ps, vals) <- checkDecls decls
       (m', qs) <- binds vals (checkMatch m expected)
       return (X.MGuarded (X.GLet decls') m', (ps ++ qs))
checkMatch (MGuarded (GFrom (At l p) e) m) expected =
    do t <- newTyVar KStar
       case p of
         PWild ->
             do (e', ps) <- checkExpr e t
                (m', qs) <- checkMatch m expected
                v <- fresh "v"
                let tys :: TyS
                    tys = Forall [] ([] :=> introduced t)
                return (X.MGuarded (X.GLet (X.Decls [(X.Defn v (convert tys) (Right (X.Gen [] [] e')))]))
                                   (X.MGuarded (X.GFrom X.PWild v) m'), ps ++ qs)
         PVar id ->
             do (e', ps) <- checkExpr e t
                (m', qs) <- bind id (LamBound t) (checkMatch m expected)
                let tys :: TyS
                    tys = Forall [] ([] :=> introduced t)
                return (X.MGuarded (X.GLet (X.Decls [(X.Defn id (convert tys) (Right (X.Gen [] [] e')))])) m', ps ++ qs)
         PCon ctor vs ->
             do (tys, n) <- ctorBinding ctor
                (kvars, tyvars, ps :=> At _ t) <- instantiate tys
                let (parameters, result) = flattenArrows t
                    arity                = length parameters
                    valEnv               = Map.fromList (zip vs (map (LamBound . dislocate) parameters))
                when (length vs /= arity) $
                  failWithS (fromId ctor ++ " requires " ++ multiple arity "argument" "arguments")

                (e', qs) <- checkExpr e result
                v <- fresh "v"
                let tys :: TyS
                    tys = Forall [] ([] :=> introduced result)

                evs <- freshFor "e" ps
                envvars <- freeEnvironmentVariables
                let ps'          = zip evs ps
                    transparents = tvs expected ++ tvs valEnv ++ envvars
--                     ps''         = [(id, convert (dislocate p)) | (id, p) <- ps']
                    extVars      = take n tyvars

                (m', rs) <- binds valEnv (checkMatch m expected)
                -- (evsubst, rs', cbindss) <-
                --     traceIf (not (null rs))
                --             (show ("Simplifying predicates from guarded match:" <+> pprList (map snd rs)))
                --             (entails transparents (tvs expected ++ tvs valEnv) ps' rs)
                return (X.MGuarded (X.GLet (X.Decls [X.Defn v (convert tys) (Right (X.Gen [] [] e'))])) $
                        X.MGuarded (X.GFrom (X.PCon (X.Inst ctor (map X.TyVar tyvars) (map X.EvVar evs)) vs) v) $
                        m',
                        ps' ++ qs ++ rs)
{-
                         (foldr (\cbinds m -> case cbinds of
                                                Left cs | all null (map snd cs) -> m
                                                        | otherwise             -> X.MGuarded (X.GLetTypes (Left cs)) m
                                                Right (args, results, f)        -> X.MGuarded (X.GLetTypes (Right (args, results, f))) m)
                                m')
                                cbindss)
                        ps' ++ qs ++ rs)
-}

             where flattenArrows (TyApp (At _ (TyApp (At _ arr) at)) (At _ rt))
                       | arr == arrTy = let (args', result) = flattenArrows rt
                                        in (at : args', result)
                   flattenArrows t    = ([], t)

         PTyped p tys ->
             do v <- fresh "x"
                checkMatch (MGuarded (GFrom p (introduced (ELet (Decls [Explicit (v, [], MCommit e) (ForallK [] tys)])
                                                                (introduced (EVar v)))))
                                     m)
                           expected
         PGuarded p g ->
             checkMatch (MGuarded (GFrom (At l p) e) (MGuarded g m)) expected

----------------------------------------------------------------------------------------------------
--

checkFunction :: [Id] -> Match Pred KId -> Ty -> M (X.Expr, Preds)
checkFunction params body expected =
    checkExpr (foldr elam (introduced (EMatch body)) params) expected
    where elam v e = introduced (ELam v e)

checkTypingGroup :: TypingGroup Pred KId -> M (X.Defns, Preds, TyEnv)

checkTypingGroup (Explicit (name, params, body) expectedTyS) =
    trace ("Inferring type for " ++ show (ppr name <::> ppr expectedTyS)) $
    do -- Instantiate declared type signatures
       (declaredKVars, declaredTyVars, declaredPredicates :=> At _ declaredType) <- instantiate expectedTyS
       evvars <- freshFor "e" declaredPredicates
       envvars <- freeEnvironmentVariables
       let declaredPreds  = zip evvars declaredPredicates
           transparents   = tvs declaredType ++ envvars

       -- Add error reporting once we know the instantiation of the expected signature; that way,
       -- type variables in the error will line up with the way we report the expected type.
       transformFailures (addErrorContext declaredKVars declaredTyVars declaredPredicates declaredType) $
           do trace (show ("Simplifying declared type" <+> ppr (declaredPredicates :=> introduced declaredType)))
                    (solve transparents (tvs declaredType) declaredPreds)
              expected <- substitute declaredType

              (body', evsubst, ps') <-
                  withGeneric (declaredTyVars, declaredKVars) $
                      do -- Check that body has declared type
                         (body', ps) <- checkFunction params body expected
                         -- Ensure that the expected type's predicates are sufficient to prove the inferred predicates
                         (evsubst, ps', cbindss) <-
                             traceIf (not (null ps)) "Discharging inferred from expected predicates" $
                                 entails transparents (tvs declaredType) declaredPreds ps
                         return (foldr (\cbinds e ->
                                            case cbinds of
                                              Left cs | all null (map snd cs) -> e
                                                      | otherwise             -> X.ELetTypes (Left cs) e
                                              Right (args, results, f)        -> X.ELetTypes (Right (args, results, f)) e)
                                       body'
                                       cbindss,
                                 evsubst, ps')

              (retained, deferred) <- splitPredicates ps'
              when (not (null retained)) $
                   do fds <- inducedDependencies (map snd (declaredPreds ++ ps'))
                      transformFailures (addAmbiguousVariables (tvs (map snd retained) \\ close (tvs expected) fds) (map snd retained)) $
                          contextTooWeak retained

              return ( [X.Defn name (convert expectedTyS)
                                    (Right (X.Gen declaredTyVars
                                             evvars
                                             (X.ESubst [] evsubst body')))]
                     , deferred
                     , Map.singleton name (LetBound expectedTyS))

    where addErrorContext kvs tvs ps t msg = iter tvs
              where iter (v:vs) = bindingTyVar v (const (iter vs))
                    iter []     = msg <$> indent 4 (hang 4 ("In the explicit binding for" <+>
                                                            ppr name <::> ppr (ForallK kvs (Forall tvs (ps :=> introduced t)))))

          -- In this code, we want to shorten type variables names, in parallel with the shortening
          -- that occurs in the wrapped error message.  However, the instance of Printable for
          -- variables can't shorten names---in particular, that instance doesn't know whether a
          -- variable is an expression, type, or evidence variable.  'tyvarName' is a lower-level
          -- IMPEG printer that provides type variable name shortening.
          addAmbiguousVariables avars ps msg =
              case nub avars of
                [] -> msg
                [v] -> msg <$> shorten ps (hang 4 ("Note: the type variable" <+> tyvarName v <+> "is ambiguous."))
                vs  -> msg <$> shorten ps (hang 4 ("Note: the type variables" <+> shorten ps (hsep (punctuate comma (map tyvarName vs))) <+> "are ambiguous."))


checkTypingGroup (Implicit fs) =
    appendFailureContext ("In the implicit bindings for" <+> hsep (punctuate comma [ppr name | (name, _, _) <- fs])) $
    do -- Generate new type variables for functions
       ts <- replicateM (length fs) (newTyVar KStar)
       -- Check function bodies in environment with aforementioned type variables
       (fs', pss) <- unzip `fmap`
                     binds (Map.fromList (zip ids (map LamBound ts)))
                           (sequence [checkFunction ps body t | ((ps, body), t) <- zip alts ts])

       -- Solve any solvable predicates; determine which of the remaining predicates can be deferred
       -- to the surrounding expression.

       envvars <- freeEnvironmentVariables
       let transparents = tvs ts ++ envvars

       (evsubst, ps, cbindss) <-
           traceIf (not (null (concat pss)))
                   (show ("Simplifying inferred predicates" <+> pprList (map snd (concat pss))))
                   (solve transparents (tvs ts) (concat pss))
       (retained, deferred) <- splitPredicates ps
       let (retainedVs, retainedPs) = unzip retained

       -- Compute type signatures for the implicit declarations, and check whether or not they're
       -- ambiguous.  For the ambiguity check, we'll need to know the functional dependencies for
       -- the retained predicates.

       -- The ambiguity check is different than that in Haskell: our ambiguity check extends to
       -- quantification in addition to qualification.  The following example is legal in Haskell:

       --   f xs = null xs || g True
       --   g y  = y || f []

       -- However, it is not legal in Habit, as there is no way to determine the type argument to f
       -- from the call in g.  This could be resolved with a suitable clever defaulting mechanism:
       -- for example, GHC inserts a dummy "Any" type when compiling these functions.

       ts' <- mapM substitute ts
       qs <- mapM (substitute . snd) ps
       fds <- inducedDependencies qs
       let -- 'qualify t' begins by computing the determined variables given the type t and the
           -- functional dependencies from retained.  If all the variables in retained are
           -- determined, it generates a type scheme by quantifying over all the variables in
           -- 'retained => t'; otherwise, it complains about ambiguous types.  Again, we've lost the
           -- information to give a good error location here.
           qualify t =
               let determined = close (tvs t ++ envvars) fds
                   qty = retainedPs :=> introduced t
                   quantifyingVs = nub (tvs qty) \\ envvars
                   ambiguities = filter (`notElem` determined) quantifyingVs
               in case ambiguities of
                    [] -> return (quantifyingVs, quantify quantifyingVs qty)
                    vs -> failWith (ambiguousTypeError vs qty)

       tyss <- mapM qualify ts'

       let replacements = [(id, X.ELetVar (X.Inst id (map X.TyVar quantifyingVs) (map X.EvVar retainedVs)))
                          | (id, (quantifyingVs, _)) <- zip ids tyss]

           functions    = [X.Defn id (convert tys)
                                     (Right (X.Gen vs
                                                   retainedVs
                                                   (foldr (\cbinds e ->
                                                               case cbinds of
                                                                 Left cs | all null (map snd cs) -> e
                                                                         | otherwise             -> X.ELetTypes (Left cs) e
                                                                 Right (args, results, f)        -> X.ELetTypes (Right (args, results, f)) e)
                                                          (X.ESubst replacements evsubst f)
                                                          cbindss)))
                          | (id, (vs, tys), f) <- zip3 ids tyss fs']

       trace (show (hang 4 ("Inferred types" <$>
                            vcat [ppr id <::> ppr tys <+> "(generalized from" <+> ppr t <> ")" | (id, (_, tys), t) <- zip3 ids tyss ts']) <$>
                    "With free environment variables" <+> cat (punctuate (comma <> space) (map ppr envvars))))
             (return ( functions
                     , deferred
                     , Map.fromList (zip ids (map (LetBound . snd) tyss)) ))

    where (ids, alts) = unzip [(name, (params, match)) | (name, params, match) <- fs]
          ambiguousTypeError avs qty = shorten qty message
              where message = case avs of
                                [v] -> "Ambiguous type variable" <+> ppr v <+> "in type" <+> ppr qty
                                _   -> "Ambiguous type variables" <+> hsep (punctuate comma (map ppr avs)) <+> "in type" <+> ppr qty

checkTypingGroup (Pattern (At l p) m signatures) =
    appendFailureContext ("In the pattern bindings for" <+> hsep (punctuate comma (map ppr (bound p)))) $
    do tupleVar <- fresh "v"
       rhsVar   <- fresh "rhs"
       vs'      <- mapM fresh vs
       let body       = MGuarded (GLet (Decls [Implicit [(rhsVar, [], m)]]))
                                 (MGuarded (GFrom (At l (rename (zip vs vs') p)) (At l (EVar rhsVar)))
                                           (MCommit (introduced (foldl eapp (ECon (fromString ("$Tuple" ++ show (length vs)))) (map EVar vs')))))
           components = [makeTypingGroup (v, [], MCommit (At l (eapp (EVar (fromString ("$t" ++ show n ++ '_' : show m))) (EVar tupleVar)))) | (v,m) <- zip vs [0..]]
       (tupleGroup, ps, tupleEnv) <- checkTypingGroup (Implicit [(tupleVar, [], body)])
       (componentGroups, pss, componentEnvs) <- unzip3 `fmap` binds tupleEnv (mapM checkTypingGroup components)
       return (concat (tupleGroup : componentGroups), ps ++ concat pss, Map.unions (tupleEnv : componentEnvs))
    where vs        = bound p
          n         = length vs
          eapp e e' = EApp (introduced e) (introduced e')

          lookupSignature id [] = Nothing
          lookupSignature id (Signature id' tys : rest)
              | id == id'       = Just tys
              | otherwise       = lookupSignature id rest

          makeTypingGroup f@(id, _, _) =
              case lookupSignature id signatures of
                Nothing -> Implicit [f]
                Just tys -> Explicit f tys

checkTypingGroup (PrimValue (Signature name expectedTyS) str) =
    do tys'@(ForallK _ (Forall _ (ps :=> _))) <- simplifyScheme expectedTyS
       if not (null ps)
       then failWith (hang 4 ("After simplification, primitive" <+> ppr name <+> "has illegal qualified type" <$> ppr expectedTyS))
       else return ( [X.Defn name (convert expectedTyS) (Left (str, []))]
                   , []
                   , Map.singleton name (LetBound expectedTyS))

----------------------------------------------------------------------------------------------------

checkDecls :: Decls Pred KId -> M (X.Decls, Preds, TyEnv)
checkDecls (Decls groups) =
    do (groups', preds, vals) <- binds (Map.fromList (signatures groups)) (checkGroups groups)
       return (X.Decls (concat groups'), preds, vals)
    where checkGroups [] = return ([], [], Map.empty)
          checkGroups (g:gs) =
              do (g', ps, vals) <- checkTypingGroup g
                 (gs', qs, vals') <- binds vals (checkGroups gs)
                 return (g':gs', ps ++ qs, Map.union vals' vals)

          -- flatten typing groups

          signatures []                                 = []
          signatures (Explicit (name, _, _) tys : rest) = (name, LetBound tys) : signatures rest
          signatures (Implicit _ : rest)                = signatures rest
          signatures (Pattern _ _ ss : rest)            = [(name, LetBound tys) | Signature name tys <- ss] ++ signatures rest
          signatures (PrimValue (Signature name tys) _ : rest) = (name, LetBound tys) : signatures rest
