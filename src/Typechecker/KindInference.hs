{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving
           , OverloadedStrings #-}
module Typechecker.KindInference (inferKinds, emptyKindInferenceState, KindEnv) where

import Common
import Control.Monad.State
import Data.Graph (SCC, flattenSCC, stronglyConnComp)
import Data.List ((\\), intercalate, nub)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Printer.Common hiding (empty)
import Syntax.Common
import Syntax.IMPEG
import Syntax.IMPEG.KSubst
import Syntax.IMPEG.TSubst (gen, inst, tvs)

import Debug.Trace

----------------------------------------------------------------------------------------------------
-- Kind inference takes a program with optional kind annotations (potentially appearing on type
-- parameters or as TyKinded nodes in the Type AST) and generates a program in which all type
-- constructors and type variables have (potentially polymorphic) kind annotations.  In the process,
-- it generates a global kind environment.
--
-- We perform kind inference independently on each group of mutually-recursive top-level
-- declarations, in dependency order.
--
-- After inferring kinds for and annotating the top-level declarations, we then perform a kind
-- checking and annotation pass over the value and primitive declarations.  These passes cannot
-- compute new kind information, but should catch kind errors in type expressions.

-- Each symbol is mapped to either a kind on the Left (for type declarations) or a list of kinds on
-- the Right (for class declarations).
type KindEnv = Map Id (Either Kind [Kind])
type KindScEnv = Map Id (KScheme (Either Kind [Kind]))

apply :: KSubst -> KindEnv -> KindEnv
apply ksubst = Map.map (either (Left . (ksubst #)) (Right . map (ksubst #)))

emptyKindInferenceState :: KindScEnv
emptyKindInferenceState = Map.empty

inferKinds :: Has s KindScEnv => Pass s (Program Pred Id (Either KId Id)) (Program Pred KId KId)
inferKinds = up (\p -> PassM (StateT (\globals ->
                                          do (p', (St (_, _, globals') _ _)) <-
                                                 runStateT (runM (kindInference p)) (St (Map.empty, Map.empty, globals) [] empty)
                                             return (p', globals'))))
    where kindInference p =
              do modify addPrimitives
                 declGroups' <- mapM inferDeclGroup declGroups
                 decls'      <- checkDecls (decls p)
                 primitives' <- mapM (mapLocated checkPrimitive) (primitives p)
                 return (Program decls' (concat declGroups') primitives')
              where declGroups            = scc (topDecls p)
                    addPrimitives (St (locals, current, globals) gvars ks) =
                        St (locals, current, Map.union globals (Map.fromList (catMaybes (map (kindFrom . dislocate) (primitives p)))))
                           gvars
                           ks

                    kindFrom (PrimCon {})                = Nothing
                    kindFrom (PrimType name k)           = Just (name, ForallK (vars k) (Left k))
                    kindFrom (PrimClass name params _ _) = Just (name, ForallK (concatMap vars ks) (Right ks))
                        where ks = map (kind . dislocate) params

----------------------------------------------------------------------------------------------------
-- Computing SCCs of top-level declarations.  We begin with a walk over the possible TL declarations
-- to collect the referents of each declaration.

class References t
    where references :: t -> [Id]

instance References t => References (Located t)
    where references (At _ t) = references t

instance References t => References (Maybe t)
    where references x = maybe [] references x

instance References t => References [t]
    where references xs = concatMap references xs

instance References (Type Id)
    where references (TyCon s)      = [s]
          references (TyVar _)      = []
          references (TyGen _)      = []
          references (TyApp t t')   = references t ++ references t'
          references (TyNat _)      = []
          references (TyKinded t _) = references t
          references (TyLabel _)    = []

instance References (PredType Pred Id)
    where references (Pred cl ts _) = cl : (concatMap references ts)

instance References (Qual (PredType Pred Id) (Type Id))
    where references (ps :=> t) = concatMap references ps ++ references t

instance References (Qual (PredType Pred Id) (PredType Pred Id))
    where references (ps :=> p) = concatMap references ps ++ references p

instance References (Scheme Pred Id)
    where references (Forall _ qt) = references qt

instance References t => References (KScheme t)
    where references (ForallK _ x) = references x

instance (References p, References t) => References (Ctor tyid p t)
    where references (Ctor _ _ ps ts) = concatMap references ps ++ concatMap references ts

instance References (BitdataField Id)
    where references (LabeledField _ ty _) = references ty
          references (ConstantField _)     = []

instance References (StructRegion Id)
    where references (StructRegion _ t) = references t

-- At that point, SCC computation is relatively straightforward.  The only source of complication is
-- that a single area declaration can introduce multiple names; this vaguely complicates the name to
-- index mapping.

scc :: TopDecls Pred Id (Either (Kinded Id) Id) -> [TopDecls Pred Id (Either (Kinded Id) Id)]
scc topDecls = map flattenSCC sccs
    where idNodes  = map nodeFrom topDecls
          idxMap   = concat (zipWith (\(_, names, _) i -> [(name, i) | name <- names]) idNodes [0..])
          idxNodes = [(d, fromJust (lookup name idxMap), catMaybes (map (flip lookup idxMap) referents)) | (d, (name:_), referents) <- idNodes]
          sccs     = stronglyConnComp idxNodes

          nodeFrom d@(At _ (Datatype name _ _ ctors _))     = (d, [name], concatMap references ctors)
          nodeFrom d@(At _ (Bitdatatype name size ctors _)) = (d, [name], references size ++ concatMap references ctors )
          nodeFrom d@(At _ (Struct name size ctor align _)) = (d, [name], references size ++ references ctor ++ references align)
          nodeFrom d@(At _ (Area _ namesAndInits ty align)) = (d, [name | (At _ name, _, _) <- namesAndInits], references ty ++ references align)
          nodeFrom d@(At _ (Class name _ _ methods _))      = (d, [name], concat [references t | Signature _ t <- methods])
          nodeFrom d@(At _ (Instance name _ chain))         = (d, [name], concat [references qp | (qp, _) <- chain])
          nodeFrom d@(At _ (Require ps qs))                 = (d, map fst ps, concatMap (references . snd) ps ++ references qs)

----------------------------------------------------------------------------------------------------
-- Kind inference for declaration groups.  There are three stages:
--
--  * First, we compute an initial kind environment for the declaration group, bindings kinds for
--    each top-level declaration in the declaration group.
--
--  * Second, we perform kind inference on each group of top-level declaration, in the context of
--    the initial kind environment.  This process computes a new kind substitution from the
--    top-level declaration and then applies it to the inital environment.
--
--  * Third, we generalize over any kind variables that remain in the "current" environment.
--
--  * Finally, we merge the (substituted) initial environment into the global kind environment.
--
--  inferDeclGroup drives this process; the first step is implemented in buildKindEnvironment, the
--  second in inferDecl, and the remainder in inferDeclGroup itself.

inferDeclGroup :: TopDecls Pred Id (Either (Kinded Id) Id) -> M (TopDecls Pred KId KId)
inferDeclGroup decls =
    do kes <- mapM (buildKindEnvironment . dislocate) decls
       let current = Map.unions kes
       decls' <- bindCurrent current
                    (mapM checkTopDecl decls)
       ks <- gets substitution
       let current' = apply ks current
       modify (\st -> st { environment = (Map.empty, Map.empty, Map.union (globals (environment st)) (Map.map generalize current'))
                         , substitution = empty })
       return (ks # decls')
    where generalize (Left k) = ForallK (vars k) (Left k)
          generalize (Right ks) = ForallK (concatMap vars ks) (Right ks)
          globals (_, _, gs) = gs

newKVar :: MonadBase m => m Kind
newKVar = KVar `fmap` fresh "k"

----------------------------------------------------------------------------------------------------
-- buildKindEnvironment computes the bindings each top-level declaration adds to the global
-- environment.  These bindings are initially populated with kind variables where kinds are not
-- user-specified.
buildKindEnvironment :: MonadBase m => TopDecl Pred Id (Either KId Id) -> m KindEnv
buildKindEnvironment (Datatype name params _ _ _) =
    do ks <- parameterKinds params'
       return (Map.singleton name (Left (foldr KFun KStar ks)))
    where params' = map dislocate params
buildKindEnvironment (Bitdatatype name _ _ _) =
    return (Map.singleton name (Left KStar))
buildKindEnvironment (Struct name _ _ _ _) =
    return (Map.singleton name (Left KArea))
buildKindEnvironment (Area {}) =
    return Map.empty
buildKindEnvironment (Class name params constraints _ _) =
    do ks <- parameterKinds params'
       return (Map.singleton name (Right ks))
    where params' = map dislocate params
          ps = map paramName params'
buildKindEnvironment (Instance {}) =
    return Map.empty
buildKindEnvironment (Require {}) =
    return Map.empty

----------------------------------------------------------------------------------------------------
-- Throughout kind inference, we maintain three separate kind environments: the "global" environment
-- (that never changes), the "current" environment (that we update during kind inference) and the
-- "local" environment for each top-level declaration.  For ease of writing type signatures, we
-- introduce an alias to a tuple of the three environments:
type EnvTriple = (KindEnv, KindEnv, KindScEnv) -- (locals, current, globals)
data KiState   = St { environment :: EnvTriple
                    , generics :: [Id]
                    , substitution :: KSubst }

-- We define a new monad to track the kind substitution and the current environment.
newtype M t = M { runM :: StateT KiState Base t }
    deriving (Functor, Applicative, Monad, MonadBase, MonadState KiState)

local :: (EnvTriple -> EnvTriple) -> M t -> M t
local f c = M (StateT (\(St kenv gvars ks) ->
                           do (v, St _ gvars' ks') <- runStateT (runM c) (St (f kenv) gvars ks)
                              return (v, St kenv gvars' ks')))

withGeneric :: [Id] -> M t -> M t
withGeneric ids c =
    M (StateT (\(St kenv gvars ks) ->
                   do (v, St kenv' _ ks') <- runStateT (runM c) (St kenv (ids ++ gvars) ks)
                      return (v, St kenv' gvars ks')))

-- Operations on current environment
bindLocals :: Map Id (Either Kind [Kind]) -> M t -> M t
bindLocals bs = local addBindings
    where addBindings (locals, current, globals) =
              (Map.union locals bs, current, globals)

bindCurrent :: Map Id (Either Kind [Kind]) -> M t -> M t
bindCurrent bs = local addBindings
    where addBindings (locals, current, globals) =
              (locals, Map.union current bs, globals)

lookupType :: Id -> M (Either Kind [Kind])
lookupType name = lookup' . environment =<< get
    where lookup' (locals, current, globals) =
              case Map.lookup name locals `orElse` Map.lookup name current of
                Just k  -> return k
                Nothing ->
                    case Map.lookup name globals of
                      Just ksc -> instK ksc
                      Nothing  -> failWithS ("Unbound type " ++ fromId name)

          orElse :: Maybe t -> Maybe t -> Maybe t
          Just t `orElse` _  = Just t
          Nothing `orElse` t = t

-- Kind schemes

instK :: HasKinds t => KScheme t -> M t
instK (ForallK ids x) =
    do ks <- replicateM (length ids) newKVar
       return (new (zip ids ks) # x)

-- assertType and assertClass are utility operations to deconstruct the result of a lookup.
assertType :: Either Kind [Kind] -> M Kind
assertType (Left k)  = return k
assertType (Right _) = failWithS "Expected type constructor but found class name"

assertClass :: Either Kind [Kind] -> M [Kind]
assertClass (Left _)   = failWithS "Expected class name but found type constructor"
assertClass (Right ks) = return ks

-- unifies wraps the generic unify from KSubst into a kind substitution monad; it also lifts
-- unification errors into errors in the base monad, and annotates them with the original
-- unification targets.  This is the only operation that actually touches the underlying
-- substitution.
unifies :: Kind -> Kind -> M ()
unifies k0 k1 =
    do St kenv gvars ksubst <- get
       let k0' = ksubst # k0
           k1' = ksubst # k1
       appendFailureContext (text "While unifying the kinds" <+> ppr k0'  <+> text "and" <+> ppr k1') $
           case unify gvars k0' k1' of
             Left err      -> failWithS err
             Right ksubst' -> put (St kenv gvars (ksubst' `compose` ksubst))

----------------------------------------------------------------------------------------------------
-- Kind inference for types, predicates, qualified types, and type schemes.
--
-- When a syntactic construct X can have multiple types (like types or schemes, but not like
-- predicates), the corresponding checkX function takes the desired type as its first argument.
-- This allows for earlier detection of kind errors, which should, in turn, provide better error
-- messages.

checkPred :: Located (PredType Pred Id) -> M (Located (PredType Pred KId))
checkPred (At loc (Pred cl ts flag)) =
    failAt loc $
    do ks <- assertClass =<< lookupType cl
       when (length ks /= length ts) $ failWithS ("Incorrect number of arguments to class '" ++ fromId cl ++ "'")
       ts' <- zipWithM checkType ks ts
       return (At loc (Pred cl ts' flag))

-- The result of checkType should never include TyKinded nodes.
checkType :: Kind -> Located (Type Id) -> M (Located (Type KId))
checkType k (At loc t) = failAt loc (At loc `fmap` check t)
    where check (TyCon name) =
              do unifies k =<< assertType =<< lookupType name
                 return (TyCon (Kinded name k))
          check (TyVar name) =
              do unifies k =<< assertType =<< lookupType name
                 return (TyVar (Kinded name k))
          check (TyApp t1 t2) =
              do karg <- newKVar
                 t1' <- checkType (KFun karg k) t1
                 t2' <- checkType karg t2
                 return (TyApp t1' t2')
          check (TyNat n) =
              do unifies k KNat
                 return (TyNat n)
          check (TyKinded t k') =
              do unifies k (dislocate k')
                 dislocate `fmap` checkType k t
          check (TyLabel l) =
              do unifies k KLabel
                 return (TyLabel l)

checkQualType :: Kind -> Qual (PredType Pred Id) (Type Id) -> M (Qual (PredType Pred KId) (Type KId))
checkQualType k (ps :=> t) =
    liftM2 (:=>) (mapM checkPred ps) (checkType k t)

-- checkScheme begins by inventing names for the quantified type variables, binding them to the
-- kinds in the Forall constructor, and then performs kind inference in that local environment.  The
-- scheme is regeneralized before it is returned.
checkScheme :: Kind -> Scheme Pred Id -> M (Scheme Pred KId)
checkScheme k (Forall qvars qty) =
    do knames <- replicateM (length qvars) (fresh "k")
       bindLocals (Map.fromList (zip qvars (map (Left . KVar) knames))) $
           do qty' <- checkQualType k (inst (map TyVar qvars) qty)
              ksubst <- gets substitution
              let kids = zipWith Kinded qvars (map KVar knames)
              return (ksubst # Forall kids (gen 0 kids qty'))

checkKScheme :: Kind -> KScheme (Scheme Pred Id) -> M (KScheme (Scheme Pred KId))
checkKScheme k (ForallK kvars tys) =
    do tys' <- withGeneric kvars (checkScheme k tys)
       return (ForallK kvars tys')

-- checkSignature is in the substitution monad because the signatures within a class declaration can
-- drive the assignment of kinds to the class parameters.
checkSignature :: Kind -> Signature Pred Id -> M (Signature Pred KId)
checkSignature k (Signature name tys) =
    do tys' <- checkKScheme k tys
       return (Signature name tys')

----------------------------------------------------------------------------------------------------
-- Kind inference for top-level declarations

-- parameterKinds generates kinds for a list of type parameters; new kind variables are generated
-- for unkinded parameters.
parameterKinds :: MonadBase m => [Either (Kinded Id) Id] -> m [Kind]
parameterKinds = mapM parameterKind
    where parameterKind (Left (Kinded _ k)) = return k
          parameterKind (Right _) = newKVar

rebuildParameters :: [Located t] -> [Id] -> [Kind] -> [Located KId]
rebuildParameters ls ids ks = zipWith at ls (zipWith Kinded ids ks)

-- checkTopDecl performs kind inference for top-level declarations; each branch begins by adding any
-- local bindings introduced by that declaration (such as the parameters of a datatype or class
-- declaration).  The Bitdatatype and Struct cases do not have to worry about type parameters yet.
checkTopDecl :: Located (TopDecl Pred Id (Either KId Id)) -> M (Located (TopDecl Pred KId KId))
checkTopDecl (At loc tdecl) =
    failAt loc $
    case tdecl of
      Datatype name params constraints ctors drv ->
          withGeneric gkvars $
          do k  <- assertType =<< lookupType name
             ks <- parameterKinds params'
             unifies (foldr KFun KStar ks) k
             bindLocals (Map.fromList (zip pnames (map Left ks))) $
                 do constraints' <- mapM checkPred constraints
                    ctors' <- mapM (checkCtor (checkType KStar)) ctors
                    return (At loc (Datatype (Kinded name k) (rebuildParameters params pnames ks) constraints' ctors' drv))
          where gkvars  = vars params
                params' = map dislocate params
                pnames  = map paramName params'
      Bitdatatype name size ctors drv ->
          do size' <- checkSize size
             ctors' <- mapM (checkCtor checkField) ctors
             return (At loc (Bitdatatype name size' ctors' drv))
          where checkField (At loc (LabeledField fname ty init)) =
                    failAt loc $
                    do ty' <- checkType KStar ty
                       return (At loc (LabeledField fname ty' init))
                checkField (At loc (ConstantField lit)) =
                    return (At loc (ConstantField lit))
      Struct name size ctor align drv ->
          do size' <- checkSize size
             ctor' <- checkCtor checkRegion ctor
             align' <- checkAlign align
             return (At loc (Struct name size' ctor' align' drv))
          where checkRegion (At loc (StructRegion field ty)) =
                    failAt loc $ (At loc . StructRegion field) `fmap` checkType KArea ty
      Area v ps tys align ->
          failAt loc $
          do tys' <- checkScheme KStar tys
             align' <- checkAlign align
             return (At loc (Area v ps tys' align'))
      Class name params constraints methods defaults ->
          failAt loc $
          withGeneric gkvars $
          do ks  <- assertClass =<< lookupType name
             ks' <- parameterKinds params'
             zipWithM_ unifies ks ks'
             bindLocals (Map.fromList (zip pnames (map Left ks'))) $
                 do methods'     <- mapM (checkSignature KStar) methods
                    defaults'    <- mapM checkFunction defaults
                    return (At loc (Class name (rebuildParameters params pnames ks') constraints methods' defaults'))
          where gkvars  = vars params
                params' = map dislocate params
                pnames  = map paramName params'
      Instance iname className chain ->
          do chain' <- mapM checkClause chain
             return (At loc (Instance iname className chain'))
          where -- checkClause is somewhat unusual, as instance clauses are not quantified.  I don't
                -- really know why; they probably ought to be.  In the meantime, we treat all
                -- variables that appear in the instance declaration as if they were quantified.
                checkClause (qp@(hypotheses :=> conclusion), impls) =
                    do kvs <- replicateM (length vs) newKVar
                       bindLocals (Map.fromList (zip vs (map Left kvs))) $
                           do hypotheses' <- mapM checkPred hypotheses
                              conclusion' <- checkPred conclusion
                              impls'      <- mapM checkFunction impls
                              return (hypotheses' :=> conclusion', impls')
                    where vs = tvs qp
      Require ps qs ->
          do kvs <- replicateM (length vs) newKVar
             bindLocals (Map.fromList (zip vs (map Left kvs))) $
                 do ps' <- mapM (\(id, p) -> do p' <- checkPred p; return (id, p')) ps
                    qs' <- mapM checkPred qs
                    return (At loc (Require ps' qs'))
          where vs = tvs (map snd ps ++ qs)
    where checkSize Nothing     = return Nothing
          checkSize (Just size) = Just `fmap` checkScheme KNat size

          checkAlign Nothing = return Nothing
          checkAlign (Just (At loc align)) = (Just . At loc) `fmap` checkScheme KNat align

          checkCtor f (Ctor name qvars preds xs) =
              do knames <- freshFor "k" qvars
                 bindLocals (Map.fromList (zip qvars (map (Left . KVar) knames))) $
                     do let qvars' = map TyVar qvars
                        preds' <- mapM (checkPred . inst qvars') preds
                        xs'    <- mapM (f . inst qvars') xs
                        let kids = zipWith Kinded qvars (map KVar knames)
                        return (Ctor name kids (map (gen 0 kids) preds') (map (gen 0 kids) xs'))

----------------------------------------------------------------------------------------------------
-- Kind annotation for expressions and local declarations.

checkExpr :: Located (Expr Pred Id) -> M (Located (Expr Pred KId))
checkExpr (At loc e) =
    do e' <- failAt loc (check e)
       return (At loc e')
    where check (ELet ds body)            = liftM2 ELet (checkDecls ds) (checkExpr body)
          check (ELam v body)             = liftM (ELam v) (checkExpr body)
          check (EVar id)                 = return (EVar id)
          check (ECon id)                 = return (ECon id)
          check (EBitCon id fs)           =
              do es' <- mapM checkExpr es
                 return (EBitCon id (zip vs es'))
              where (vs, es) = unzip fs
          check (EBits value size)        = return (EBits value size)
          check (EMatch m)                = liftM EMatch (checkMatch m)
          check (EApp e e')               = liftM2 EApp (checkExpr e) (checkExpr e')
          check (EBind v e rest)          = liftM2 (EBind v) (checkExpr e) (checkExpr rest)
          check (EStructInit name fields) = liftM (EStructInit name) (mapSndM checkExpr fields)

checkMatch :: Match Pred Id -> M (Match Pred KId)
checkMatch MFail          = return MFail
checkMatch (MCommit e)    = liftM MCommit (checkExpr e)
checkMatch (MElse m m')   = liftM2 MElse (checkMatch m) (checkMatch m')
checkMatch (MGuarded g m) = liftM2 MGuarded (checkGuard g) (checkMatch m)

checkGuard :: Guard Pred Id -> M (Guard Pred KId)
checkGuard (GFrom p e) = liftM2 GFrom (mapLocated checkPattern p) (checkExpr e)
checkGuard (GLet ds)   = liftM GLet (checkDecls ds)

checkPattern :: Pattern Pred Id -> M (Pattern Pred KId)
checkPattern (PVar v)       = return (PVar v)
checkPattern PWild          = return PWild
checkPattern (PCon name vs) = return (PCon name vs)
checkPattern (PTyped p tys) =
    do p' <- mapLocated checkPattern p
       tys' <- checkScheme KStar tys
       return (PTyped p' tys')
checkPattern (PGuarded p g) = liftM2 PGuarded (checkPattern p) (checkGuard g)

checkFunction :: (Id, [Id], Match Pred Id) -> M (Id, [Id], Match Pred KId)
checkFunction (name, params, body) =
    do body' <- checkMatch body
       return (name, params, body')

checkTypingGroup :: TypingGroup Pred Id -> M (TypingGroup Pred KId)
checkTypingGroup (Explicit f tys) = liftM2 Explicit (checkFunction f) (checkKScheme KStar tys)
checkTypingGroup (Implicit fs)    = Implicit `fmap` mapM checkFunction fs
checkTypingGroup (Pattern p b ss) = liftM3 Pattern (mapLocated checkPattern p)
                                                   (checkMatch b)
                                                   (mapM (checkSignature KStar) ss)
checkTypingGroup (PrimValue tys name) = liftM2 PrimValue (checkSignature KStar tys) (return name)

checkDecls :: Decls Pred Id -> M (Decls Pred KId)
checkDecls (Decls gs) = Decls `fmap` mapM checkTypingGroup gs

----------------------------------------------------------------------------------------------------

checkPrimitive :: Primitive Pred Id -> M (Primitive Pred KId)
checkPrimitive (PrimCon s impl) =
    do s' <- checkSignature KStar s
       return (PrimCon s' impl)
checkPrimitive (PrimType name k) =
    return (PrimType (Kinded name k) k)
checkPrimitive (PrimClass name params constraints methods) =
    PrimClass name params constraints `fmap` mapM (checkSignature KStar) methods
