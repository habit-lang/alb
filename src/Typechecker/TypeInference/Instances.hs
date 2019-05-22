{-# LANGUAGE FlexibleContexts #-}

module Typechecker.TypeInference.Instances(deriveInstances) where

import Common
import Control.Monad.State
import Data.Graph
import Data.List (intercalate, mapAccumL, partition)
import Data.Maybe (isJust)
import Printer.Common
import Printer.IMPEG
import Syntax.IMPEG
import Syntax.IMPEG.TSubst
import Typechecker.TypeInference.Base

import Prelude hiding ((<$>))
import qualified Debug.Trace as Trace
type TDecl    = TopDecl Pred KId KId  -- Abbreviation for top level declarations in this module.
type Deriving = ([TDecl], [Id])       -- Pairs a list of generated instances (TDecls) with a
                                      -- list of requested classes.

----------------------------------------------------------------------------------------------------
-- Handle derived instance clauses on data, bitdata, and struct declarations:

deriveInstances :: Program Pred KId KId -> M [Located TDecl]
deriveInstances p = do ds <- concatMapM deriveL (topDecls p)
                       ds' <- concatMapM deriveP (primitives p)
                       return (ds ++ ds')
    where deriveL (At loc td) = failAt loc (fmap (At loc `fmap`) (derive td))

derive                                   :: TDecl -> M [TDecl]
derive (Datatype name params ps ctors drv) = deriveDatatype name params ps ctors drv
derive (Bitdatatype name msize ctors drv) = deriveBitdatatype name msize ctors drv
derive (Struct name msize ctor align drv) = deriveStruct name msize ctor align drv
derive _                                  = return []

makeInstances      :: (Deriving -> M Deriving) -> [Id] -> M [TDecl]
makeInstances f drv = do (insts, drv') <- f ([], drv)
                         when (not (null drv')) $
                           failWith ("No support for deriving an instance of"
                                     <+> hsep (punctuate comma (map ppr drv'))
                                     <+> "for this type")
                         return insts

-- Use this function when an instance of the specified cls should always be derived,
-- but with different methods depending on whether the derived class was requested
-- or notRequested.
always :: Id -> (Id -> M [TDecl]) -> (Id -> M [TDecl]) -> Deriving -> M Deriving
always cls requested notRequested (insts, drv)
 = case partition (cls==) drv of
     ([], _)     -> do newinsts <- notRequested cls
                       return (newinsts ++ insts, drv)
     ([_], drv') -> do newinsts <- requested cls
                       return (newinsts ++ insts, drv')
     (_, drv')   -> do failWith (ppr cls <+> "is mentioned multiple times in deriving list")

-- Use this function when an instance of the specified cls should be derived only
-- if requested by an entry in the deriving list.
ifRequested              :: (Id -> M [TDecl]) -> Id -> Deriving -> M Deriving
derinst `ifRequested` cls = always cls derinst (\cls -> return [])

-- Use this function as the requested argument to always in cases where the user should not
-- (have to) request a derived instance:
shouldNotList      :: Id -> M [TDecl]
shouldNotList cls   = failWith (ppr cls <+> "is derived automatically and should not be listed")

-- Use this function as a stub for cases that are not yet implemented:
notImplemented     :: Id -> M [TDecl]
notImplemented cls  = failWith ("Support for deriving" <+> ppr cls <+> "is not yet implemented")

-- Construct a match of the form:  (pat <- e) => m
mkGuard        :: Pattern p tyid -> Expr p tyid -> Match p tyid -> Match p tyid
mkGuard pat e m = MGuarded (GFrom (introduced pat) (introduced e)) m

-- Construct an application, introducing locations for both arguments:
iEApp          :: Expr p tyid -> Expr p tyid -> Expr p tyid
x `iEApp` y     = introduced x `EApp` introduced y

-- Construct an expression for a label value of the form #id:

labelVal  :: Id -> Expr Pred KId
labelVal x = ELet decls (introduced (EVar "$p"))
 where decls    = Decls [Explicit ("$p", [], MCommit (introduced (ECon "Proxy"))) kscheme]
       kscheme  = ForallK [] (Forall [] ([] :=> introduced ty))
       ty       = TyApp (introduced (TyCon (Kinded "Proxy" (KFun KLabel KStar)))) (introduced (TyLabel x))

-- Instantiate a list of ctor parameters to obtain a list of fresh type variables:
freshParams     :: [KId] -> M [Type KId]
freshParams kids = do let (vs, ks) = unzipKinded kids
                      vs' <- mapM fresh vs
                      return (map TyVar (zipWith Kinded vs' ks))

----------------------------------------------------------------------------------------------------
-- Construct predicates for computing sizes in bitdata and struct types:

nary :: (Located Ty -> Located Ty -> Located Ty -> PredType Pred KId)
     -> [Located Ty] -> Located Ty -> M [Located (PredType Pred KId)]
nary bin [n1, n2] size =
    return [introduced (bin n1 n2 size)]
nary bin (n1 : n2 : rest) size =
    do n <- introduced `fmap` newTyVar KNat
       ps <- nary bin (n : rest) size
       return (introduced (bin n1 n2 n) : ps)

-- natConstraints takes a list of types and generates a set of constraints that
-- computes the size of each type and requires that their sum be the size from
-- the bitdata declaration.
natConstraints :: (Located Ty -> Located Ty -> PredType Pred KId) -- construct a predicate from type & size params
               -> Located Ty                                      -- Declared "total"
               -> (Located Ty -> Located Ty -> Located Ty -> PredType Pred KId) -- "Binary" predicate to combine values
               -> [Located Ty]                                    -- field types
               -> (Located Ty -> Located Ty -> PredType Pred KId) -- Relationship between declared "total" and actual "total"
               -> M ([Located Ty], [Located (PredType Pred KId)]) -- size variables, predicates
natConstraints _ _ _ [] _ =
    return ([], [])
natConstraints sizePred size _ [t] rel =
    do v <- (introduced . TyVar . flip Kinded KNat) `fmap` fresh "size"
       return ([size], [introduced (sizePred t v), introduced (rel v size)])
natConstraints sizePred size bin ts rel =
    do vs <- freshFor "n" ts
       let sizes = [introduced (TyVar (Kinded v KNat)) | v <- vs]
       v <- (introduced . TyVar . flip Kinded KNat) `fmap` fresh "size"
       ps <- nary bin sizes v
       return (sizes, introduced (rel v size) : map introduced (zipWith sizePred ts sizes) ++ ps)

-- Generate a simple type from a bitdata/struct size annotation:
natType                :: Id -> Maybe TyS -> M ([Located (PredType Pred KId)], Located Ty)
natType _ (Just tys)    = do (_, kids, sizePreds :=> size) <- instantiate (ForallK [] tys)
                             return (sizePreds, size)
natType name Nothing    = do v <- fresh name
                             return ([], introduced (TyVar (Kinded v KNat)))

sizeType = natType "size"
alignType = natType "align"

----------------------------------------------------------------------------------------------------
-- Deriving for types introduced in data declarations:

deriveDatatype :: KId
               -> [Located KId]
               -> [Located (PredType Pred KId)]
               -> [Ctor KId (PredType Pred KId) (Type KId)] -> [Id] -> M [TDecl]
deriveDatatype name params ps ctors
 = makeInstances (
  always "@" shouldNotList deriveAt
    >=> deriveEq       `ifRequested` "Eq"
    >=> deriveOrd      `ifRequested` "Ord"
    >=> deriveBounded  `ifRequested` "Bounded"
    >=> deriveNum      `ifRequested` "Num"
    >=> deriveBoolean  `ifRequested` "Boolean"
    >=> deriveShift    `ifRequested` "Shift"
    >=> deriveMonad    `ifRequested` "Monad")

  where
    -- The type for which these instances are being defined:
    namedType           = foldl (\f x -> TyApp (at x f) x) (TyCon name) (map (TyVar `fmap`) params)

    deriveAt :: Id -> M [TDecl]
    deriveAt _
        | null params = return []
        | otherwise = do insts <- deriveInstances
                         reqs <- deriveRequirements
                         return (insts ++ reqs)
        where (_, steps) = mapAccumL (\t u -> let next = tyapp t u in (next, next)) (TyCon name) (map (fmap TyVar) params)
              tyapp t u@(At l _) = TyApp (At l t) u
              impliedAts = concat [ atConstraints t
                                  | Ctor _ kparams qs ts <- ctors
                                  , t <- ts
                                  , all (`notElem` kparams)
                                        (tvs (inst (fmap TyVar kparams) (map dislocate ts)))
                                  ]
              allPreds = ps ++ impliedAts
              predsFor t = filter (\p -> all (`elem` vs) (tvs p)) allPreds
                  where vs = tvs t
              matches p q = case match ([], []) p q of
                              Left _ -> False
                              Right _ -> True

              deriveInstances =
                  do instanceNames <- freshFor "derived" steps
                     return [ Instance instName "@" ((ps :=> at, []) :
                                                      if null ps then [] else [([] :=> introduced (predf "@" [u, u']), [])])
                            | (instName, t@(TyApp u u')) <- zip instanceNames steps,
                              let at = introduced (predh "@" [u, u'])
                                  notMe (At _ p) = not (matches p (predh "@" [u, u']))
                                  ps = filter notMe (predsFor t) ]

              deriveRequirements =
                  for steps $
                  \t@(TyApp u u') ->
                      let at = introduced (predh "@" [u, u'])
                          notMe (At _ p) = not (matches p (predh "@" [u, u']))
                          ps = filter notMe (predsFor t) in
                      if null ps
                      then return []
                      else do requirementNames <- freshFor "derived" ps
                              return [Require (zip requirementNames ps) [at]]
                  where for xs f = fmap concat (mapM f xs)
                        pprList ps = cat (punctuate (comma <> space) (map ppr ps))

    ---------------------------------
    -- Derived instances for Eq, Ord: these can potentially be used with any datatype
    -- syntax and require instances of the derived class for each component type.
    ---------------------------------

    -- Build an instance for a class using the given implementations of its members with
    -- a single clause that requires instances of the derived class for each component type.
    -- Instantiates the ctorParams and adds ctorQualifiers for each constructor, as necessary.
    allComponentsInst :: Id -> [Function Pred KId] -> M [TDecl]
    allComponentsInst cls impl
     = do instName   <- fresh "derived"
          hypotheses <- concatMapM for ctors
          return [Instance instName cls [(hypotheses :=> pred (introduced namedType), impl)]]
       where for ctor = do ts <- freshParams (ctorParams ctor)
                           let comps = ctorFields ctor
                           return (map (inst ts) (ctorQualifiers ctor ++ map pred comps))
             pred t   = introduced (predh cls [t])

    -- Derive an instance of the Eq class:
    deriveEq           :: Id -> M [TDecl]
    deriveEq cls        = allComponentsInst cls eqImpl
     where
      eqImpl = [("==", ["$u", "$v"], case map eqMatch ctors of
                                       [m] -> m
                                       ms  -> foldr MElse falseMatch ms)]

      -- For each constructor C of arity n, eqMatch builds a Match of the form:
      --
      --    (C a1 ... an <- $u) =>
      --      (C b1 ... bn <- $v) =>
      --        (True <- a1 == b1) =>
      --          ...
      --            (True <- a(n-1) == b(n-1)) =>
      --              (an == bn)
      --
      eqMatch     :: Ctor tyid (PredType p tyid) (Type tyid) -> Match p tyid
      eqMatch ctor = mkGuard (con (map fst args)) (EVar "$u")
                   $ mkGuard (con (map snd args)) (EVar "$v")
                   $ case [ (EVar "==" `iEApp` EVar a) `iEApp` EVar b | (a,b) <- args ] of
                       []  -> MCommit (introduced (EBitCon "True" []))
                       eqs -> foldr (mkGuard (PCon "True" []))
                                    (MCommit (introduced (last eqs)))
                                    (init eqs)
                     where con  = PCon (dislocate (ctorName ctor))
                           args = zipWith (\n _ -> (toId ("a$"++n), toId ("b$"++n)))
                                          (map show [0..])
                                          (ctorFields ctor)
      -- If none of the individual constructor matches succeed, then args are not equal.
      falseMatch  :: Match p tyid
      falseMatch   = MCommit (introduced (EBitCon "False" []))

    -- Derive an instance of the Ord class:
    deriveOrd          :: Id -> M [TDecl]
    deriveOrd cls       = allComponentsInst cls cmpImpl
     where
      cmpImpl = [("compare", ["$u", "$v"], case ctors of
                                             [] -> MCommit (introduced (ECon "EQ"))
                                             _  -> foldr1 MElse (map cmpMatch (splits ctors)))]

      -- The general structure of a derived Ord instance is a match of the following form:
      --
      --    (C1 a1 ...) <- $u => m1
      --  | (C2 a1 ...) <- $u => m2
      --  | ...
      --  | (Cn a1 ...) <- $u => mn
      --
      -- where C1, C2, ..., Cn are the constructors of the datatype in order and "a1 ..."
      -- represents the appropriate list of parameters in each case.  Each of m1, m2, ..., mn
      -- is a match that examines the structure of $v to make an appropriate comparison with
      -- the already matched value of $u.  In particular, in match mi, we know that $u is a
      -- value of the form (Ci a1 ...), so if $v matches (Cj b1 ...), then:
      --  - if Cj comes before Ci (i.e., i < j), then mi should return GT because $u > $v
      --  - if Cj comes after Ci (i.e., i > j), then mi should return LT because $u < $v
      --  - if Cj == Ci, then we need to compare the individual elements for each constructor.

      -- splits is a generic combinatorial function that finds all the ways of splitting a list
      -- by picking out a particular element that separates all the elements that come before it
      -- from all the elements that come after.
      splits       :: [a] -> [([a], a, [a])]
      splits []     = []
      splits (x:xs) = ([], x, xs) : [ (x:ys, z, zs) | (ys, z, zs) <- splits xs ]

      -- cmpMatch constructs matches of the form (Ci a1 ...) <- $u => mi, as seen in the code
      -- above.  The input is one of the results produced by splits, specifying a particular
      -- constructor, ctor; the list, bef, of all constructors that come before ctor; and the
      -- list, aft, of all constructors that come after it.
      cmpMatch (bef, ctor, aft) = mkGuard (con (map fst args)) (EVar "$u")
                                $ foldr1 MElse (map cmpBef bef ++ [ctorCmp] ++ map cmpAft aft)
        where ctorCmp        = mkGuard (con (map snd args)) (EVar "$v")
                             $ case [ (EVar "compare" `iEApp` EVar a) `iEApp` EVar b | (a, b) <- args ] of
                                 []   -> MCommit (introduced (ECon "EQ"))
                                 cmps -> foldr combine (MCommit (introduced (last cmps))) (zip [0..] (init cmps))
              combine (i,cmp) m  = let rvar = toId ("$r" ++ show i)
                                   in mkGuard (PVar rvar) cmp
                                    $ MElse (mkGuard (PCon "EQ" []) (EVar rvar) m)
                                            (MCommit (introduced (EVar rvar)))
              con            = PCon (dislocate (ctorName ctor))
              args           = zipWith (\n _ -> (toId ("a$"++n), toId ("b$"++n)))
                                       (map show [0..])
                                       (ctorFields ctor)

      -- For constructors that come before the constructor that matched $u, we can return GT:
      cmpBef befctor = mkGuard (dummyCon befctor) (EVar "$v") (MCommit (introduced (ECon "GT")))

      -- For constructors that come after the constructor that matched $u, we can return LT:
      cmpAft aftctor = mkGuard (dummyCon aftctor) (EVar "$v") (MCommit (introduced (ECon "LT")))

      -- This function just constructs a dummy pattern that will match any values that have been
      -- obtained using the specified constructor:
      dummyCon ctor  = PCon (dislocate (ctorName ctor))
                            (zipWith (\n _ -> toId ("b$"++show n)) [0..] (ctorFields ctor))

    ---------------------------------
    -- Derived instances for Bounded: these require either an enumeration (all
    -- constructors have arity zero) or a single constructor.
    ---------------------------------

    -- Test for an enumeration:
    isEnumeration      :: Bool
    isEnumeration       = all (null . ctorFields) ctors

    -- Test for a single constructor:
    singleConstructor  :: Bool
    singleConstructor   = case ctors of [_] -> True; _ -> False

    -- (Lazy) Pattern matches for the first constructor and its name:
    ctor0  = head ctors        -- the first constructor
    cname0 = ctorName ctor0    -- the name of the first constructor

    -- Derive an instance of the Bounded class:
    deriveBounded      :: Id -> M [TDecl]
    deriveBounded cls   = if isEnumeration then
                            allComponentsInst cls [ enumBound "minBound" ctor0, enumBound "maxBound" (last ctors) ]
                          else if singleConstructor then
                            allComponentsInst cls [ singleBound "minBound", singleBound "maxBound" ]
                          else
                            failWith ("A single constructor or enumeration is required for deriving" <+> ppr cls)
                          where
                            enumBound nm ctor = (nm, [], MCommit (ECon `fmap` ctorName ctor))
                            singleBound nm    = (nm, [], MCommit (ctorApp nm))
                            ctorApp nm        = foldl (\f arg -> introduced (f `EApp` introduced arg))
                                                       (ECon `fmap` cname0)
                                                       [ EVar nm | f <- ctorFields ctor0 ]

    ---------------------------------
    -- Derived instances for Num, Boolean, and Shift: these require a single
    -- constructor with a single component:
    ---------------------------------

    -- Test for a single single argument in the first constructor:
    singleArgument     :: Bool
    singleArgument      = case ctor0 of Ctor{ctorFields=[_]} -> True; _ -> False

    singleConAndArg    :: Id -> M ()
    singleConAndArg cls = when (not (singleConstructor && singleArgument)) $
                            failWith ("A single constructor, single argument type is required for deriving" <+> ppr cls)

    -- Given a class C and a single constructor, single argument datatype of the form
    -- data T args = K t, generate:  instance C (T args) if C t where funs
    inst0            :: Id -> [Function Pred KId] -> M [TDecl]
    inst0 cls funs    = do instName <- fresh "derived"
                           ts       <- freshParams (ctorParams ctor0)
                           let arg0@(At l _) = head (ctorFields ctor0) -- the type of the first constructor's only argument
                               hypotheses    = At l (predh cls [arg0]) : ctorQualifiers ctor0
                               conclusion    = At l (predh cls [At l namedType])
                           return [Instance instName cls [(inst ts (hypotheses :=> conclusion), funs)]]

    -- Lifting for arity 1 function:  f u@(C x) = C (f x)
    lift1            :: Id -> Function p tyid
    lift1 id          = (id, ["$u"], guard (MCommit (introduced result)))
     where guard  = mkGuard0 "$x" "$u"
           result = (ECon `fmap` cname0) `EApp` introduced (EVar id `iEApp` EVar "$x")

    -- Lifting for arity 2 function:  f u@(C x) v@(C y) = C (f x y)
    lift2            :: Id -> Function p tyid
    lift2 id          = (id, ["$u", "$v"], uguard (vguard (MCommit (introduced result))))
     where uguard = mkGuard0 "$x" "$u"
           vguard = mkGuard0 "$y" "$v"
           result = (ECon `fmap` cname0) `EApp` introduced ((EVar id `iEApp` EVar "$x") `iEApp` EVar "$y")

    -- Lifting for arity 2 function, left arg only:  f u@(C x) v = C (f x v)
    liftleft2        :: Id -> Function p tyid
    liftleft2 id      = (id, ["$u", "$v"], uguard (MCommit (introduced result)))
     where uguard = mkGuard0 "$x" "$u"
           result = (ECon `fmap` cname0) `EApp` introduced ((EVar id `iEApp` EVar "$x") `iEApp` EVar "$v")

    -- Construct a match of the form:  (Name0 x <- v) => m   (Name0 is the first/only constructor, arity 1)
    mkGuard0         :: Id -> Id -> Match p tyid -> Match p tyid
    mkGuard0 x v m    = mkGuard (PCon (dislocate cname0) [x]) (EVar v) m

    -- Derive an instance of the Num class:
    deriveNum        :: Id -> M [TDecl]
    deriveNum cls     = do singleConAndArg cls
                           inst0 cls [lift2 "+", lift2 "-", lift2 "*", lift1 "negate"]

    -- Derive an instance of the Boolean class:
    deriveBoolean    :: Id -> M [TDecl]
    deriveBoolean cls = do singleConAndArg cls
                           inst0 cls [lift2 ".&.", lift2 ".|.", lift2 ".^.", lift1 "not"]

    -- Derive an instance of the Shift class:
    deriveShift      :: Id -> M [TDecl]
    deriveShift cls   = do singleConAndArg cls
                           inst0 cls [liftleft2 "shiftL", liftleft2 "shiftR"]

    ---------------------------------
    -- Derived instances for Monad:
    ---------------------------------

    deriveMonad      :: Id -> M [TDecl]
    deriveMonad cls   = do singleConAndArg cls
                           notImplemented cls

----------------------------------------------------------------------------------------------------
-- Deriving for types introduced in bitdata declarations:

deriveBitdatatype :: Id -> Maybe (Scheme Pred KId) -> [Ctor KId (PredType Pred KId) (BitdataField KId)] -> [Id] -> M [TDecl]
deriveBitdatatype name msize ctors drv
 = do selupds     <- mapM ctorSelectUpdate ctors
      (sel1,upd1) <- singleCtorSelectUpdate ctors
      let sels = concat (map fst selupds) ++ sel1
          upds = concat (map snd selupds) ++ upd1
      makeInstances (always "BitSize" shouldNotList deriveBitSize
                 >=> always "Select" shouldNotList (const (return sels))
                 >=> always "Update" shouldNotList (const (return upds))
                 >=> deriveToBits   `ifRequested` "ToBits"
                 >=> deriveFromBits `ifRequested` "FromBits"
                 >=> deriveEq       `ifRequested` "Eq"
                 >=> deriveOrd      `ifRequested` "Ord"
                 >=> deriveBounded  `ifRequested` "Bounded"
                 >=> deriveNum      `ifRequested` "Num"
                 >=> deriveBoolean  `ifRequested` "Boolean"
                 >=> deriveBitManip `ifRequested` "BitManip"
                 >=> deriveShift    `ifRequested` "Shift") drv
   where

    -- The type for which these instances are being defined:
    namedType           = TyCon (Kinded name KStar)

    -- Build a simple implementation that defines a member function using a primitive:
    primImpl           :: Id -> Id -> Functions Pred KId
    primImpl name prim  = [(name, [], MCommit (introduced (EVar prim)))]

    -- Functions for deriving BitSize instances:
    deriveBitSize      :: Id -> M [TDecl]
    deriveBitSize cls   = do instName    <- fresh "bitsize"
                             (qs, width) <- sizeType msize
                             ps          <- concatMapM (ctorWidths width) ctors
                             let concHolds = introduced (bitSize (introduced namedType) width)
                                 concFails = introduced (predf cls [introduced namedType, introduced (TyVar (Kinded "$n" KNat))])
                             return [Instance instName cls [((introduced (widthPred width) : ps ++ qs) :=> concHolds, []),
                                                            ([]                                        :=> concFails, [])]]
     where
      ctorWidths :: Located Ty ->                                      -- total width
                    Ctor KId (PredType Pred KId) (BitdataField KId) -> -- constructor
                    M [Located (PredType Pred KId)]                    -- (field widths, size-determining predicates)
      ctorWidths totalWidth (Ctor _ kids ps fields) =
          do ts         <- freshParams kids
             fieldTypes <- mapM fieldType [ f | At _ f <- fields ]
             let (determined, undetermined) = partition sizeDetermined fieldTypes
             (_, qs) <- case length undetermined of
                          0 -> natConstraints bitSize totalWidth sumP (map (inst ts) fieldTypes) equ
                          1 -> natConstraints bitSize totalWidth sumP (map (inst ts) determined) lte
                          _ -> failWith "Too many variable-width fields in constructor"
             return (map (inst ts) ps ++ qs)

    -- Functions for deriving Select and Update instances:

    -- Generate constructor-level instances of Select and update for this bitdatatype.
    -- Given type T, constructor C, with fields x1 :: t1, ..., the appropriate instance
    -- decls are:
    --
    --   instance Select (BitdataCase T #"C") #x1 t1
    --     where select = bitdataSelect
    --   else ...
    --
    --   instance Update (BitdataCase T #"C") #x1
    --     where update = bitdataUpdate
    --   else ...
    --
    ctorSelectUpdate (Ctor (At l cname) kids ps fields)
      = do selInstName <- fresh "selInst"
           updInstName <- fresh "updInst"
           ts          <- freshParams kids
           return ([Instance selInstName "Select" cs | let cs = selChain ts, not (null cs)],
                   [Instance updInstName "Update" cs | let cs = updChain ts, not (null cs)])
        where
          loc          = At l                                                -- locate at same place as the constructor
          ltycon       = loc namedType                                       -- locate the main type constructor
          compVar      = loc (TyVar (Kinded "t" KStar))                      -- type variable for component type
          compType     = loc (TyApp (loc (TyApp (loc bitdataCaseTy) ltycon)) -- BitdataCase T #"C"
                                                (loc (TyLabel cname)))
          selImpl      = primImpl "select" "bitdataSelect"
          selChain ts  = [(inst ts (ps :=> loc (Pred "Select" [compType, loc (TyLabel fieldName), fieldTy] Holds)), selImpl)
                         | At _ (LabeledField fieldName fieldTy _) <- fields ]
          updImpl      = primImpl "update" "bitdataUpdate"
          updChain ts  = [(inst ts (ps :=> loc (Pred "Update" [compType, loc (TyLabel fieldName)] Holds)), updImpl)
                         | At _ (LabeledField fieldName _ _) <- fields ]

    -- Generate type-level instances of Select and Update for this bitdatatype, if
    -- it only has one constructor.  The pattern for these instances is as follows:
    --
    --   instance Select T #"x1" v if Select (BitdataCase T C) #"x1"
    --     where select r f = {(C v <- r) => ^(select v f)}
    --   else ...
    --
    --   instance Update T #.x1 if Update (BitdataCase T C) #x1
    --     where update r f t = {(C v <- r) => ^(C (update v f t))}
    --   else ...
    --
    -- Note that we generate individual Select and Update clases for each allowed
    -- label (even though we have the same textual body in each case); this makes
    -- it possible to define a "synthesized" field selector on a single constructor
    -- bitdata type without creating the overlapping instance that would occur if
    -- we used the following, single instance to do all the lifting:
    --
    --   instance Select T f v if Select (BitdataCase T C) f v
    --     where select r f = {(C v <- r) => ^(select v f)}
    --
    -- Note that we couldn't do a similar generic instance for the Update class
    -- anyway, even if we wanted to, because there isn't enough information in the
    -- system to infer that:  forall f, t. Select T f t ==> Select (BitdataCase T C) f t.
    --
    singleCtorSelectUpdate [Ctor (At l cname) _ _ fields]
      = do selInstName <- fresh "selInst"
           updInstName <- fresh "updInst"
           return ([Instance selInstName "Select" selChain | not (null selChain)],
                   [Instance updInstName "Update" updChain | not (null updChain)])
        where loc        = At l
              ltycon     = loc namedType
              compVar    = loc (TyVar (Kinded "t" KStar))
              compType   = loc (TyApp (loc (TyApp (loc bitdataCaseTy) ltycon)) (loc (TyLabel cname)))
              guard m    = mkGuard (PCon cname ["$v"]) (EVar "$r") (MCommit (loc m))

              fieldNames = [fieldName | At _ (LabeledField fieldName _ _) <- fields]

              selImpl    = [("select", ["$r", "$f"], guard selBody)]
              selBody    = (EVar "select" `iEApp` EVar "$v") `iEApp` EVar "$f"
              selChain   = [([loc (predh "Select" [compType, loc (TyLabel fieldName), compVar])]
                               :=> loc (predh "Select" [ltycon, loc (TyLabel fieldName), compVar]), selImpl)
                           | fieldName <- fieldNames]

              updImpl    = [("update", ["$r", "$f", "$t"], guard updBody)]
              updBody    = ECon cname `iEApp` (((EVar "update" `iEApp` EVar "$v") `iEApp` EVar "$f") `iEApp` EVar "$t")
              updChain   = [([loc (predh "Update" [compType, loc (TyLabel fieldName)])]
                               :=> loc (predh "Update" [ltycon, loc (TyLabel fieldName)]), updImpl)
                           | fieldName <- fieldNames]
    singleCtorSelectUpdate _
      = return ([], [])

    -- Variant of the datatype allComponentsInst adapted for bitdata types.
    -- TODO: is it useful to express both as instances of a more general pattern?
    allComponentsInst :: Id -> [Function Pred KId] -> M [TDecl]
    allComponentsInst cls impl
     = do instName   <- fresh "derived"
          hypotheses <- concatMapM for ctors
          return [Instance instName cls [(hypotheses :=> pred (introduced namedType), impl)]]
       where for ctor = do ts <- freshParams (ctorParams ctor)
                           let comps = [ t | At _ (LabeledField _ t _) <- ctorFields ctor ]
                           return (map (inst ts) (ctorQualifiers ctor ++ map pred comps))
             pred t   = introduced (predh cls [t])

    -- Functions for deriving instances of ToBits and FromBits:
    deriveToBits       :: Id -> M [TDecl]
    deriveToBits cls    = allComponentsInst cls (primImpl "toBits" "primToBits")

    deriveFromBits     :: Id -> M [TDecl]
    deriveFromBits cls  = allComponentsInst cls (primImpl "fromBits" "primFromBits"
                                              ++ primImpl "isJunk" "primIsJunk")   -- TODO: needs proper implementation

    -- Derive an instance of the Eq class:
    deriveEq           :: Id -> M [TDecl]
    deriveEq cls        = allComponentsInst cls (primImpl "==" "primBitdataEquals")

    -- Test for an enumeration:
    isEnumeration      :: Bool
    isEnumeration       = null [ t | ctor <- ctors, At _ (LabeledField _ t _) <- ctorFields ctor ]

    -- Test for a single constructor:
    singleConstructor  :: Bool
    singleConstructor   = case ctors of [_] -> True; _ -> False

    -- (Lazy) Pattern matches for the first constructor and its name:
    ctor0  = head ctors        -- the first constructor
    cname0 = ctorName ctor0    -- the name of the first constructor
    name0  = dislocate cname0  -- the dislocated name of the first constructor

    -- Derive an instance of the Bounded class:
    deriveBounded      :: Id -> M [TDecl]
    deriveBounded cls   = if isEnumeration then
                            allComponentsInst cls [ enumBound "minBound" ctor0, enumBound "maxBound" (last ctors) ]
                          else if singleConstructor then
                            allComponentsInst cls [ singleBound "minBound", singleBound "maxBound" ]
                          else
                            failWith ("A single constructor or enumeration is required for deriving" <+> ppr cls)
                          where
                            enumBound nm ctor = (nm, [], MCommit (at cname (EBitCon (dislocate cname) [])))
                                                where cname = ctorName ctor
                            singleBound nm    = (nm, [], MCommit (at cname0 (EBitCon name0 (fields nm))))
                            fields nm         = [ (lab, At l (EVar nm)) | At l (LabeledField lab _ _) <- ctorFields ctor0 ]

    -- Test for a single single argument in the first constructor:
    singleField        :: Maybe (Id, Located Ty)
    singleField         = case ctor0 of
                            Ctor{ctorFields=[At _ (LabeledField lab0 lty0 _)]}
                              -> Just (lab0, lty0)
                            _ -> Nothing

    singleConAndField  :: Id -> M ()
    singleConAndField cls
                        = when (not (singleConstructor && singleField/=Nothing)) $
                            failWith ("A single constructor, single field bitdata type is required for deriving" <+> ppr cls)

    -- (Lazy) Pattern matches for label and type of the (only) field:
    Just (lab0, lty0)   = singleField
    proxy0              = labelVal lab0
    sel0 src            = (EVar "select" `iEApp` src) `iEApp` proxy0
    make0 val           = at cname0 (EBitCon name0 [(lab0, at cname0 val)])

    -- Given a class C and a single constructor, single field bitdata type of the
    -- form bitdata T = K[x::t], generate:  instance C T if C t where funs
    inst0            :: Id -> [Function Pred KId] -> M [TDecl]
    inst0 cls funs    = do instName <- fresh "derived"
                           ts       <- freshParams (ctorParams ctor0)
                           let hypotheses    = at cname0 (predh cls [lty0]) : ctorQualifiers ctor0
                               conclusion    = at cname0 (predh cls [at cname0 namedType])
                           return [Instance instName cls [(inst ts (hypotheses :=> conclusion), funs)]]

    -- Lifting for arity 1 function:  f u@(C x) = C [lab=f x.lab]
    lift1              :: Id -> Function Pred KId
    lift1 id            = (id, ["$u"], mkGuard0 "$x" "$u" (MCommit result))
     where result = make0 (EVar id `iEApp` sel0 (EVar "$x"))

    -- Lifting for arity 1 function, constructor on rhs only:  f u = C [lab=f u]
    liftrhs1           :: Id -> Function Pred KId
    liftrhs1 id         = (id, ["$u"], MCommit result)
     where result = make0 (EVar id `iEApp` EVar "$u")

    -- Lifting for arity 1 function, constructor on rhs only:  f u@(C x) = f x
    liftlhs1           :: Id -> Function Pred KId
    liftlhs1 id         = (id, ["$u"], mkGuard0 "$x" "$u" (MCommit result))
     where result = at cname0 (EVar id `iEApp` sel0 (EVar "$x"))

    -- Lifting for arity 2 function:  f u@(C x) v@(C y) = C [lab=f x.lab y.lab]
    lift2              :: Id -> Function Pred KId
    lift2 id            = (id, ["$u", "$v"], mkGuard0 "$x" "$u" (mkGuard0 "$y" "$v" (MCommit result)))
     where result = make0 ((EVar id `iEApp` sel0 (EVar "$x")) `iEApp` sel0 (EVar "$y"))

    -- Lifting for arity 2 function, constructor on lhs only:  f u@(C x) v@(C y) = f x.lab y.lab
    liftlhs2           :: Id -> Function Pred KId
    liftlhs2 id         = (id, ["$u", "$v"], mkGuard0 "$x" "$u" (mkGuard0 "$y" "$v" (MCommit result)))
     where result = at cname0 ((EVar id `iEApp` sel0 (EVar "$x")) `iEApp` sel0 (EVar "$y"))

    -- Lifting for arity 2 function, left arg only:  f u@(C x) v = C [lab=f x.lab v]
    liftleft2          :: Id -> Function Pred KId
    liftleft2 id        = (id, ["$u", "$v"], mkGuard0 "$x" "$u" (MCommit result))
     where result = make0 ((EVar id `iEApp` sel0 (EVar "$x")) `iEApp` EVar "$v")

    -- Lifting for arity 2 function, left arg only, constructor on lhs only:  f u@(C x) v = f x.lab v
    liftleftlhs2       :: Id -> Function Pred KId
    liftleftlhs2 id     = (id, ["$u", "$v"], mkGuard0 "$x" "$u" (MCommit result))
     where result = at cname0 ((EVar id `iEApp` sel0 (EVar "$x")) `iEApp` EVar "$v")

    -- Construct a match of the form:  (Name0 x <- v) => m   (Name0 is the first/only constructor, arity 1)
    mkGuard0           :: Id -> Id -> Match p tyid -> Match p tyid
    mkGuard0 x v m      = mkGuard (PCon name0 [x]) (EVar v) m

    -- Derive an instance of the Ord class:
    deriveOrd          :: Id -> M [TDecl]
    deriveOrd cls       = do singleConAndField cls
                             inst0 cls [liftlhs2 "compare", liftlhs2 "<", liftlhs2 "<=",
                                                            liftlhs2 ">", liftlhs2 ">="]

    -- Derive an instance of the Num class:
    deriveNum        :: Id -> M [TDecl]
    deriveNum cls     = do singleConAndField cls
                           inst0 cls [lift2 "+", lift2 "-", lift2 "*", lift1 "negate"]

    -- Derive an instance of the Boolean class:
    deriveBoolean    :: Id -> M [TDecl]
    deriveBoolean cls = do singleConAndField cls
                           inst0 cls [lift2 ".&.", lift2 ".|.", lift2 ".^.", lift1 "not"]

    -- Derive an instance of the BitManip class:
    deriveBitManip    :: Id -> M [TDecl]
    deriveBitManip cls = do singleConAndField cls
                            inst0 cls [liftrhs1  "bit",     liftleft2 "setBit",  liftleft2    "clearBit",
                                       liftleft2 "flipBit", liftlhs1  "bitSize", liftleftlhs2 "testBit" ]

    -- Derive an instance of the Shift class:
    deriveShift      :: Id -> M [TDecl]
    deriveShift cls   = do singleConAndField cls
                           inst0 cls [liftleft2 "shiftL", liftleft2 "shiftR"]

----------------------------------------------------------------------------------------------------
-- Deriving for types introduced in struct declarations:

deriveStruct :: Id -> Maybe (Scheme Pred KId) -> Ctor KId (PredType Pred KId) (StructRegion KId)
             -> Maybe (Located (Scheme Pred KId)) -> [Id] -> M [TDecl]
deriveStruct name msize (Ctor _ kids ps regions) mLocatedAlign drv
    | any (`notElem` ["NoInit", "NullInit"]) drv = failWith ("No support for deriving instances of" <+>
                                                             hsep (punctuate comma (map ppr (filter (`notElem` ["NoInit", "NullInit"]) drv))))
    | otherwise =
        do vs' <- mapM fresh vs
           let ts          = map TyVar (zipWith Kinded vs' ks)
               regionTypes = map (inst ts) regionGenTypes
               regionPreds = map (inst ts) ps
           byteSizeInst <- deriveByteSize regionPreds regionTypes
           alignmentInst <- deriveAlignment regionPreds regionTypes
           selUpdInsts <- deriveSelUpd regionPreds regionTypes -- sizeTypes sizePreds
           noInitInst <- deriveInit "NoInit" "noInit" fields
           nullInitInst <- deriveInit "NullInit" "nullInit" fields
           return ([byteSizeInst, alignmentInst, noInitInst, nullInitInst] ++ selUpdInsts)

    where namedType = TyCon (Kinded name KArea)
          (mfields, regionGenTypes) = unzip [(f, ty) | At _ (StructRegion f ty) <- regions]
          fields = [f | Just f <- mfields]
          (vs, ks) = unzipKinded kids

          deriveByteSize regionPreds regionTypes =
              do (qs, size) <- sizeType msize
                 (sizeTypes, sizePreds) <- natConstraints byteSize size sumP regionTypes equ
                 sizeInstName <- fresh "i"
                 let concHolds = introduced (byteSize (introduced namedType) size)
                     concFails = introduced (predf "ByteSize" [introduced namedType, introduced (TyVar (Kinded "$n" KNat))])
                 return (Instance sizeInstName "ByteSize"
                            [((regionPreds ++ sizePreds ++ qs) :=> concHolds, []),
                             ([] :=> concFails, [])])

          deriveAlignment regionPreds regionTypes =
              do (qs, align) <- alignType malign
                 (alignTypes, alignPreds) <- natConstraints alignment align lcmp regionTypes rel
                 regionAlignmentPreds <- map introduced `fmap` regionAlignments align regionTypes
                 sizeInstName <- fresh "i"
                 let concHolds = loc (alignment (loc namedType) align)
                     concFails = loc (predf "Alignment" [introduced namedType, introduced (TyVar (Kinded "$n" KNat))])
                 return (Instance sizeInstName "Alignment"
                            [((regionPreds ++ qs ++ alignPreds ++ regionAlignmentPreds) :=> concHolds, []),
                             ([] :=> concFails, [])])
              where rel | isJust malign = divp
                        | otherwise     = equ

                    (malign, loc) = case mLocatedAlign of
                                      Nothing -> (Nothing, introduced)
                                      Just (At l s) -> (Just s, At l)

                    regionAlignments _ [] =
                        error "Instances.hs:701:empty list of regions?"
                    regionAlignments v [t] =
                        do a <- introduced `fmap` newTyVar KNat
                           return [alignment t a, divp a v]
                    regionAlignments v (t:ts) =
                        do a <- introduced `fmap` newTyVar KNat
                           s <- introduced `fmap` newTyVar KNat
                           w <- introduced `fmap` newTyVar KNat
                           ps <- regionAlignments w ts
                           return (alignment t a : divp a v : byteSize t s : sumP v s w : ps)

          deriveSelUpd regionPreds regionTypes =
              do selInstName <- fresh "i"
                 updInstName <- fresh "i"

                 let srcAlign    = TyVar (Kinded "m" KNat)
                     src         = refTy @@ namedType
                     impl        = [("select", [], MCommit (introduced (EVar "structSelect")))]
                     natTypes vs = [TyVar (Kinded v KNat) | v <- vs]

                     chain       = [ (regionPreds :=> introduced (select src fieldName (introduced (refTy @@ dislocate (head regionTypes)))), impl)
                                     | At _ (StructRegion (Just (StructField (At _ fieldName) _)) _) <- [head regions] ] ++
                                   [ (regionPreds :=> introduced (select src fieldName (introduced (refTy @@ dislocate rgnType))), impl)
                                     | (At _ (StructRegion (Just (StructField (At _ fieldName) _)) _), rgnType) <-
                                           zip (tail regions) (tail regionTypes) ]

                 return ([ Instance selInstName "Select" chain | not (null chain) ] ++
                         [ Instance updInstName "Update" [([] :=> introduced (updateFails src (TyVar (Kinded "f" KLabel))), [])] ])

          -- TODO: replaces uses of "introduced" with more appropriate source positions.
          deriveInit predName methName fields
              = do instName <- fresh "inst"
                   if predName `elem` drv
                     then do instName <- fresh "inst"
                             let initializer = MCommit (introduced (EStructInit name [ (f, At loc (EVar methName))
                                                                                     | StructField f@(At loc _) _ <- fields ]))
                             return  (Instance instName predName [([] :=> introduced (p namedType Holds),
                                                                   [(methName, [], initializer)])])
                     else do instName <- fresh "inst"
                             return (Instance instName predName [([] :=> introduced (p namedType Fails), [])])
              where p t = Pred predName [introduced t]

----------------------------------------------------------------------------------------------------

deriveP :: Located (Primitive Pred KId) -> M [Located TDecl]
deriveP prim@(At loc (PrimType (Kinded name _) k)) = loop (introduced (TyCon (Kinded name k))) k
    where loop t (KFun k k') =
              do u <- (introduced . TyVar . flip Kinded k) `fmap` fresh "u"
                 ds <- loop (introduced (TyApp t u)) k'
                 instName <- fresh "derived"
                 let inst = At loc (Instance instName "@" [(atConstraints t :=> introduced (predh "@" [t, u]), [])])
                 return (inst : ds)
          loop t _ =
              return []
deriveP _ = return []
