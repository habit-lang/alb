{-# LANGUAGE FlexibleContexts, PatternGuards #-}
module Typechecker.TypeInference.TopDecl where

import Prelude hiding ((<$>))

import Common
import Control.Monad
import Control.Monad.State
import Data.List hiding (group)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Printer.Common hiding (empty)
import qualified Solver as Solver
import Syntax.Common
import Syntax.IMPEG
import qualified Syntax.IMPEG.KSubst as K
import Syntax.IMPEG.TSubst
import qualified Syntax.XMPEG as X
import qualified Syntax.XMPEG.TSubst as X
import Typechecker.TypeInference.Base
import Typechecker.TypeInference.Expr
import Typechecker.TypeInference.Instances
import qualified Utils.BDD as BDD

withoutConditionalBindings :: M (EvSubst, Preds, [ConditionalBindings]) -> M (EvSubst, Preds)
withoutConditionalBindings c =
    do (evs, ps, cbindss) <- c
       if all emptyBindings cbindss
          then return (evs, ps)
          else failWith ("Unexpected conditional type bindings")
    where emptyBindings (Left cs) = all null (map snd cs)
          emptyBindings (Right _) = False

----------------------------------------------------------------------------------------------------

parameterNames   :: [KId] -> [Id]
parameterNames ps = [id | Kinded id _ <- ps]

addEvidence :: EvSubst -> X.Decls -> X.Decls
addEvidence [] ds = ds
addEvidence evsubst (X.Decls groups) = X.Decls (map addEvidence' groups)
    where addEvidence' (X.Defn name tys (X.Gen typarams evparams body)) =
              X.Defn name tys (X.Gen typarams evparams (buildSubst body))
          addEvidence' other = other -- TODO: check that this is correct; seems to be used for
                                     -- functions introduced in primitive declarations

          buildSubst e = X.ESubst [] s e
              where vs = X.fevs e
                    s  = filter (\(v, _) -> v `elem` vs) evsubst

-- TODO: make sure checkTopDecl is called in dependency order---I think that topdecls come out of
-- kind inference in such an order...

simplifyCtor :: (K.HasKinds t, HasTypeVariables t KId) => [KId] -> Ctor KId (PredType Pred KId) t -> M (Ctor KId (PredType Pred KId) t)
simplifyCtor univs (Ctor id@(At l _) kids ps0 t) =
    failAt l $
    do evvars <- freshFor "e" ps2
       (s, _, ps3, _) <- entails' (tvs t) (tvs t) [] (zip evvars ps2)
       let ps4 = s ## (map snd ps3 ++ qs)
           t'' = s ## t'
           kids' = kids `intersect` (concatMap tvs ps4 ++ tvs t'')
       fds <- inducedDependencies ps4
       when (not (null (kids' \\ close univs fds)))
            (failWithS "Unsupported existential type in constructor")
       return (Ctor id kids' (gen 0 kids' ps4) (gen 0 kids' t''))
    where ts = map TyVar kids
          ps1 = inst ts ps0
          t' = inst ts t
          (ps2, qs) = partition (all (`elem` kids) . tvs) ps1

solveForNat :: (Located Ty -> PredType Pred KId) -> M Int
solveForNat pcon =
    do v <- fresh "x"
       let ty = TyVar (Kinded v KNat)
       (_, remaining) <- trace ("solveForNat: Solving " ++ show (ppr (pcon (introduced ty)))) $
                         withoutConditionalBindings (solve [] [] [("e", introduced (pcon (introduced ty)))])
       trace ("Remaining predicates: " ++ show (hsep (punctuate comma (map (ppr . snd) remaining)))) $
           when (not (null remaining)) (contextTooWeak [] remaining)
       ty' <- substitute ty
       case ty' of
         TyNat n -> return (fromIntegral n)
         _       -> failWith ("Insufficient improvement; solving" <+> ppr (pcon (introduced ty)) <+> "led to" <+> ppr ty <+> equals <+> ppr ty')

mustBeSatisfied     :: PredType Pred KId -> M ()
mustBeSatisfied pred =
    do (_, remaining) <- trace ("isSatisfied: Solving " ++ show (ppr pred)) $
                         withoutConditionalBindings (solve [] [] [("e", introduced pred)])
       trace ("Remaining predicates: " ++ show (hsep (punctuate comma (map (ppr . snd) remaining)))) $
           when (not (null remaining)) (contextTooWeak [] remaining)

checkTopDecl :: TopDecl Pred KId KId -> M (X.TopDecl KId, CtorEnv)

checkTopDecl (Datatype (Kinded name k) params ctors _) =
    -- Nothing much to do here; all the hard part of checking that datatype declarations are well
    -- formed was done during kind inference.
    do ctors' <- mapM (simplifyCtor params') ctors
       xctors <- mapM convertCtor ctors'
       ctorEnv <- mapM ctorTypeBinding ctors'
       trace (show ("Binding constructors:" <+> vcat [ ppr id <::> ppr ksc | (id, (ksc, _)) <- ctorEnv ])) $
           return ( X.Datatype name params' xctors
                  , Map.fromList ctorEnv )
    where convertCtor (Ctor (At _ name) kids params ts) =
              return (name, kids, map (convert . dislocate) params, map (convert . dislocate) ts)

          params'   = map dislocate params
          t         = foldl (@@) (TyCon (Kinded name k)) (map TyVar params')

          buildArrow _ [] t =
              return ([], [], t)
          buildArrow ts (u:us) t =
              do (vs, qs, t') <- buildArrow (u:ts) us t
                 ((_, At _ funp), f@(TyVar v)) <- newArrowVar
                 let t'' = f @@ u @@ t'
                     qs' = map ((`moreUnrestricted` (introduced f)) . introduced) ts
                 return (v:vs, funp : qs' ++ qs, t'')

          ctorTypeBinding (Ctor (At _ ctorName) kids qs ts) =
              do (vs, ps, t') <- buildArrow [] (map dislocate ts) t
                 return (ctorName, (kindQuantify (Forall (kids ++ params' ++ vs)
                                                          (gen (length kids) (params' ++ vs) ((map introduced ps ++ qs) :=> introduced t'))),
                                    length kids))

checkTopDecl (Bitdatatype name mtys ctors derives) =
    -- Checking a bitdata type has three steps: for each constructor, we generate the XMPEG
    -- constructor and a set of predicates; we concatenate the predicates from all the constructors
    -- and attempt to solve them; finally, we have to generate instances of the Select and Update
    -- instances for the bitdata type and its fields.

    -- At the moment, we probably generate really poor error messages; in particular, sizes not
    -- matching or being insufficiently specified will be reported with the generic "Context too
    -- weak" message.

    -- Another assumption in the present code is that all the constraints being solved are bitsize
    -- or sum constraints, the evidence substitution basically contains nothing of value.

    appendFailureContextS ("In the definition of a bitdata type " ++ fromId name) $
    do -- Figure out declared width:
       widthN <- solveForNat (bitSize (introduced tycon))

       -- Compute XMPEG versions of constructor specs:
       ctors' <- mapM (simplifyCtor []) ctors
       xctors <- mapM (convertCtor widthN) ctors'

       -- Perform junk and confusion tests for this bitdata definition:
       let bddpat    = BDD.pOrs widthN [ pat | (_, _, pat) <- xctors ]
           junk      = BDD.pNot bddpat
           confusion = [ (cname, dname, common) |
                         ((cname, cfields, cpat), others) <- zip xctors (tail (tails xctors)),
                         (dname, dfields, dpat) <- others,
                         let common = BDD.pAnd cpat dpat,
                         not (BDD.isNone common) ]

       -- Generate junk and confusion warnings, as necessary:
       when (not (BDD.isNone junk)) $
         warn ("Type" <+> ppr name <+> "has junk:" <+> ppr junk)

       when (not (null confusion)) $ do
         sequence_ [ warn ("Overlapping bit patterns for" <+> ppr cname <+> "and" <+> ppr dname
                           <+> ":" <+> ppr pat) | (cname, dname, pat) <- confusion ]
         warn ("(Note: An instance of FromBits" <+> ppr tycon <+> "will be required.)")
         mustBeSatisfied (predh "FromBits" [introduced tycon]) -- TODO: will give lousy error message!

       -- Save the BDD representing all possible values for this type in the bitdataBDDs environment:
       modify (\st -> st{bitdataBDDs = Map.insert name bddpat (bitdataBDDs st)})

       -- Return XMPEG version of this bitdatatype decl:
       return ( X.Bitdatatype name bddpat xctors
              , Map.fromList [(cname, (ForallK [] (Forall [] ([] :=> introduced (ctorType cname))), 0))
                             | Ctor (At _ cname) _ _ _ <- ctors'] )

    where tycon          :: Ty
          tycon           = TyCon (Kinded name KStar)

          ctorType       :: Id -> Ty
          ctorType cname  = bitdataCase name cname `unrTo` tycon

          -- Construct the XMPEG representation for a bitdata constructor, including dictionaries for
          -- associated select and update instances:
          convertCtor :: Int ->
                         Ctor KId (PredType Pred KId) (BitdataField KId) -> -- original constructor spec
                         M X.BitdataCtor                                    -- XMPEG fields
          convertCtor totalSize (Ctor (At l cname) [] [] fields)
            = failAt l $
              do fieldTypes <- mapM (fieldType . dislocate) fields
                 determinedSizes <- mapM (solveForNat . bitSize) (filter sizeDetermined fieldTypes)
                 let totalDeterminedSize = sum determinedSizes
                     iter [] [] = []
                     iter (ft:fts) ss'@(~(s:ss))
                         | sizeDetermined ft = s : iter fts ss
                         | otherwise         = totalSize - totalDeterminedSize : iter fts ss'
                     iter _ _ = error "TypeInference.TopDecl:185"
                     fieldSizes = iter fieldTypes determinedSizes
                 modify (\st -> st { bitdataCtors = Map.insert cname (tycon, fieldInfo) (bitdataCtors st) })
                 (fields',pats) <- unzip `fmap` sequence (zipWith4 convertBitdataField
                                                                   (map dislocate fields)
                                                                   fieldTypes
                                                                   fieldSizes
                                                                   (tail (scanr (+) 0 fieldSizes)))
                 return (cname, fields', BDD.pSplits pats)

              where -- Build Description of the fields for this constructor:
                    fieldInfo    = [(name, ty, minit) | At _ (LabeledField name (At _ ty) minit) <- fields]

          convertCtor _ _ = failWith "Unsupported constructor form"

          -- Convert bitdata field description from IMPEG to XMPEG format:
          convertBitdataField :: BitdataField KId -> Located Ty -> Int -> Int -> M (X.BitdataField, BDD.Pat)
          convertBitdataField (LabeledField id _ _) (At _ t) w o
            = do t' <- substitute t
                 pat <- gets bitdataBDDs >>= findBDDPat t'
                 return (X.LabeledField id (convert t) pat o, pat)
              where
               findBDDPat (TyApp (At _ (TyCon (Kinded (Ident "Bit" _ _) _))) (At _ (TyNat w'))) bddenv
                 = return (BDD.pAll (fromIntegral w'))

               findBDDPat (TyApp (At _ (TyCon (Kinded (Ident "Ix" _ _) _))) (At _ (TyNat n))) bddenv
                 = return (BDD.pLess w n)

               findBDDPat (TyApp (At _ (TyApp (At _ (TyCon (Kinded (Ident "APtr" _ _) _))) _)) _) bddenv
                 = return (BDD.pAll w)

               findBDDPat (TyApp (At _ (TyApp (At _ (TyCon (Kinded (Ident "ARef" _ _) _))) _)) _) bddenv
                 = return (BDD.pGreater w 0)

               findBDDPat (TyCon (Kinded id _)) bddenv
                 | Just pat <- id `Map.lookup` bddenv = return pat

               findBDDPat t' env
                 = do warn (("Unable to find BDD for type" <+> ppr t' <> ";") </>
                            hang 4 ("assuming arbitrary bit pattern of width" <+> int w))
                      return (BDD.pAll w)

          convertBitdataField (ConstantField (At l lit)) (At _ t) w o
            = failAt l
            $ do n <- case lit of       -- check that we have a numeric literal ...
                        BitVector n w' -> return n
                        Numeric n      -> return n
                 when (n<0 || n>=2^w) $ -- ... that is in range for given # bits
                   failWithS ("Literal " ++ show n
                             ++ " does not fit in " ++ show w ++ " bits")
                 let pat = BDD.pIntMod w n
                 return (X.ConstantField n pat o, pat)

checkTopDecl (Struct name mtys ctor derives) =
    -- Checking a structure declaration is parallel to checking a bitdata declaration: generate and
    -- solve size constraints, generate XMPEG structure declaration, and generate Select and Updated
    -- instances for (references to) the structure type.  As with bitdata declarations, the error
    -- messages are probably awful and the evidence substitution is ignored.

    appendFailureContextS ("In the definition of a structure type " ++ fromId name) $
    do -- Simplify region and object to existentials
       Ctor _ ks ps locatedRegions <- simplifyCtor [] ctor
       when (not (null ks) || not (null ps))
            (failWithS "Unsupported structure declaration")
       let regions = map dislocate locatedRegions

       -- Extract declared types for each region:
       regionTypes <- mapM regionType regions
       n <- solveForNat (byteSize (introduced tycon))
       sizes <- mapM (solveForNat . byteSize) regionTypes

       -- Add structure details to to the StructRegionEnv:
       let regionInfo = zipWith reg regions (map dislocate regionTypes)
               where reg (StructRegion (Just (StructField (At _ id) minit)) _) ty = (Just id, ty, minit)
                     reg (StructRegion Nothing                              _) ty = (Nothing, ty, Nothing)
           dups       = duplicates [ id | (Just id, _, _) <- regionInfo ]
       when (not (null dups)) $
         failWithS ("Structure defines multiple field names called " ++ commaSep dups)

       modify (\st -> st { structRegions = Map.insert name (tycon, regionInfo) (structRegions st) })

       -- Compute XMPEG version of the struct decl, including width and offset information:
       let regions' = zipWith3 (\(lab, ty, _) -> X.StructField lab (convert ty)) regionInfo sizes (scanl (+) 0 sizes)
       return ( X.Struct name (fromIntegral n) regions'
              , Map.empty)
    where
      tycon = TyCon (Kinded name KArea)

      regionType :: StructRegion KId -> M (Located Ty)
      regionType (StructRegion _ ty) = return ty

checkTopDecl (Area v inits tys) =
    appendFailureContextS ("In the definition for the areas " ++ intercalate ", " (map (fromId . dislocate . fst) inits)) $
    do tys'   <- simplifyScheme (ForallK [] tys)
       inits' <- mapM checkInit inits
       case tys' of
         ForallK [] (Forall [] ([] :=> ty)) ->
             do a <- newTyVar KArea  -- area type
                s <- newTyVar KNat   -- size
                l <- newTyVar KNat   -- alignment
                (_, remaining) <- withoutConditionalBindings $
                                  solve [] [] [("$e", introduced (areaOf ty (introduced a))),
                                               ("$f", introduced (byteSize (introduced a) (introduced s))),
                                               ("$g", introduced (alignOf ty (introduced l)))]
                when (not (null remaining)) $ contextTooWeak [] remaining
                when v (do (_, remaining) <- withoutConditionalBindings (solve [] [] [("$e", introduced (noInit a))])
                           when (not (null remaining))
                                (do a' <- substitute a
                                    failWith (text "Volatile area type" <+> ppr a' <+> text "must be in class NoInit")))
                size  <- getNat "size" s
                align <- getNat "alignment" l
                return ( X.Area v inits' (convert (dislocate ty)) size align
                       , Map.fromList [(name, (tys', 0)) | (name, _) <- inits'] )
         _ ->
             failWithS ("Unsupported area declaration; declared type " ++ show (ppr tys)
                       ++ ", simplified type " ++ show (ppr tys'))
    where checkInit :: (Located Id, Id) -> M (Id, X.Inst)
          checkInit (At _ name, init)
            = appendFailureContextS ("In the initializer for area " ++ fromId name) $
              do b <- bindingOf init
                 case b of
                   LamBound _   -> failWithS ("no let bound definition for initializer " ++ fromId name)
                   LetBound tys ->
                     do (_, kids, ps :=> At _ t) <- instantiate tys
                        evs <- freshFor "e" ps
                        let preds = zip evs ps
                        (evsubst, remaining)  <- withoutConditionalBindings (solve (tvs t) (tvs t) preds)
                        when (not (null remaining)) $
                          contextTooWeak [] remaining
                        let typarams = [convert (TyVar kid)                 | kid <- kids]
                            evparams = [fromMaybe (X.EvVar ev) (lookup ev evsubst) | (ev, At _ (Pred _ _ Holds)) <- preds]
                        return (name, X.Inst init typarams evparams)

          getNat what t = do t' <- substitute t
                             case t' of
                               TyNat n -> return (fromIntegral n)
                               _       -> failWithS (what ++ " cannot be determined")

checkTopDecl _ = error "Typechecker.TypeInference:checkTopDecl"

assertClass :: TopDecl Pred KId KId -> M (TyEnv, X.Defns, [TypingGroup Pred KId])

assertClass (Class name params constraints methods defaults) =
    do mapM_ assertFunDep fds
       mapM_ assertOpacity ops
       (sigs, impls) <- unzip `fmap` sequence (zipWith selectorSigImpl methods [0..])
       (mappings, defImpls) <- unzip `fmap` mapM (defaultImpl sigs) defaults
       modify (updateClassEnv methods (Map.fromList mappings)) -- add fundeps and defaults to environment
       return (Map.fromList [ (name, LetBound tys) | (name, tys) <- sigs ], impls, defImpls)

    where classPred = Pred name (map (fmap TyVar) params) Holds
          params'   = map dislocate params

          partitionConstraints []     = ([], [])
          partitionConstraints (c:cs) =
              case dislocate c of
                f@(Fundep _)        -> (f:fds, ops)
                o@(Opaque i)        -> (fds, o:ops)
              where (fds, ops) = partitionConstraints cs

          (fds, ops) = partitionConstraints constraints

          assertFunDep (Fundep fd) =
              assert (Solver.newFunDep name fd)

          assertOpacity (Opaque i) =
              assert (Solver.newOpacity name i)

          defaultImpl sigs (mname@(Ident mname' _ _), ps, m) =
            do implName <- fresh (fromString (mname' ++ "_def"))
               tys      <- case lookup mname sigs of
                             Just tys -> return tys
                             Nothing  -> error "defaultImpl fails to find matching signature"
               return (((name, mname), implName), Explicit (implName, ps, m) tys)

          updateClassEnv methods defs st =
              st { classEnvironment = cenv { functionalDependencies = Map.insert name fds' allFDs
                                           , methodSignatures       = Map.insert name (map dislocate params, methodPairs) allMethods
                                           , defaultMethods         = Map.union denv defs  } }
              where cenv        = classEnvironment st
                    allFDs      = functionalDependencies cenv
                    allMethods  = methodSignatures cenv
                    methodPairs = [(name, tys) | Signature name tys <- methods]
                    denv        = defaultMethods cenv
                    fds'        = [fd | Fundep fd <- fds]

          -- Construct a type and an implementation for a type class method.  The class from which
          -- the method will be extracted is always the first predicate.

          selectorSigImpl (Signature name (ForallK kvars (Forall kids (ps :=> t)))) n
           = do let ps'   = introduced classPred : ps  -- full list of predicates
                    kids' = kids ++ params'            -- full list of kinds
                ds' <- freshFor "d" ps'                -- names for dictionary parameters
                let scheme = ForallK (K.vars params' ++ kvars) (Forall kids' (gen (length kids) params' (ps' :=> t)))
                    body   = X.EMethod (X.EvVar (head ds'))                  -- first evidence parameter
                                       n                                     -- dictionary slot
                                       (map X.TyVar kids)                    -- extra type parameters
                                       (map X.EvVar (tail ds'))              -- extra dict parameters
                return ((name, scheme), X.Defn name (convert scheme) (X.Gen kids' ds' body))

assertClass _ = error "TypeChecking.TypeInference:823"

assertInstances :: [Id] -> [Located (TopDecl Pred KId KId)] -> M ([(Id, X.EvDecl)], [TypingGroup Pred KId])
assertInstances derived insts =
    do (simplAxs, ws) <- assert (Solver.newAxioms axs)
       mapM_ (warn . text) ws
       let simplInsts = zipWith reconstitute insts simplAxs
       ps <- mapM (mapLocated translateInstance) simplInsts
       let (xevdecls, tgs) = unzip ps
       return (concat xevdecls, concat tgs)

    where axs = [(name, map fst chain, name `elem` derived) | At l (Instance name _ chain) <- insts]
          reconstitute (At loc (Instance iname clname clauses)) qps = At loc (Instance iname clname (zip qps impls))
              where (_, impls) = unzip clauses

          mapLocated f (At l t) = failAt l $ f t

translateInstance :: TopDecl Pred KId KId -> M ([(Id, X.EvDecl)], [TypingGroup Pred KId])

translateInstance (Instance name className chain) =
    trace (show ("Translating" <+> ppr name <+> ": " <+> cat (punctuate "; " (map (ppr . fst) chain)))) $
    do cenv <- gets classEnvironment
       let (params, methods) = fromMaybe (error ("Instance refers to non-existant class " ++ fromId className))
                               (Map.lookup className (methodSignatures cenv))
       (evdecls, methodImpls) <- unzip `fmap` mapM (clauseImpl params methods (defaultMethods cenv)) namedClauses
       return (concat evdecls, concat methodImpls)

    where -- This naming mechanism lines up with the solver's idea of evidence names.
          namedClauses =
              case chain of
                [(qp, methods)] -> [(name, qp, methods)]
                _               -> [(fromString (fromId name ++ '_' : show i), qp, methods) | ((qp, methods), i) <- zip chain [0..]]

          clauseImpl :: [KId]                                                 -- Class parameters
                     -> [(Id, KScheme TyS)]                                   -- Method type signatures
                     -> Map (Id, Id) Id                                       -- Names of default method implementations
                     -> (Id, Qual (PredType Pred KId) (PredType Pred KId), Functions Pred KId)  -- Current clause
                     -> M ([(Id, X.EvDecl)], [TypingGroup Pred KId])
          clauseImpl classParams _ _ (iname, hypotheses :=> At _ conclusion@(Pred _ classArgs Fails), _) =
              do instEvVars <- freshFor "h" hypotheses'
                 return ([(iname, (evScheme, (X.Gen qvars instEvVars [])))], [])
              where hypotheses'             = map (X.convert . dislocate) hypotheses
                    conclusion'             = X.convert conclusion
                    qvars                   = nub (X.tvs hypotheses' ++ X.tvs conclusion')  -- Ordering of type variables?
                    evScheme                = X.Forall qvars (X.gen 0 qvars hypotheses') (X.gen 0 qvars conclusion')
          clauseImpl classParams methodSignatures defaultImpls (iname, hypotheses :=> At _ conclusion, methodDecls) =
              do fds <- inducedDependencies hypotheses
                 let hypvs = nub (tvs hypotheses)
                     convs = nub (tvs conclusion)
                     determined = close convs fds
                 when (any (`notElem` determined) hypvs) $
                      failWith
                          (vcat ["Ambiguous type variables" <+> hsep (punctuate comma [ppr name | Kinded name _ <- hypvs \\ determined]),
                                 "in instance clause" <+> (ppr (hypotheses :=> introduced conclusion))])
                 instEvVars <- freshFor "h" hypotheses'
                 (names, methodImpls) <- unzip `fmap` mapM (liftMethodImplementation instEvVars) methodSignatures
                 return ( [(iname, (evScheme, (X.Gen qvars instEvVars names)))]
                        , methodImpls)

              where liftMethodImplementation :: [Id] -> (Id, KScheme TyS) -> M (X.Gen X.Inst, TypingGroup Pred KId)
                    liftMethodImplementation instEvVars (mname, ForallK kvars (Forall kids qty)) =
                        do implName <- fresh mname
                           methodBinding <- case findDecl methodDecls of
                                              Just (_, args, body) ->
                                                  return (Explicit (implName, args, body) tys)
                                              Nothing ->
                                                  case Map.lookup (className, mname) defaultImpls of
                                                    Just defImplName ->
                                                        return (Explicit (implName, [], MCommit (introduced (EVar defImplName))) tys)
                                                    Nothing ->
                                                        failWithS ("No implementation for class method " ++ fromId mname
                                                                  ++ " in instance of class " ++ fromId className)
                           methodEvVars <- freshFor "e" ps
                           return ( X.Gen kids
                                          methodEvVars
                                          (X.Inst implName
                                                  (map X.TyVar (kids ++ qvars))
                                                  (thisInstance : map X.EvVar (instEvVars ++ methodEvVars)))
                                  , methodBinding )

                        where ps :=> t     = s # qty
                              tys          = ForallK (K.vars qvars ++ kvars) (Forall (kids ++ qvars) (gen (length kids) qvars ((introduced conclusion : hypotheses ++ ps) :=> t)))
                              thisInstance = X.EvCons (X.Inst iname (map X.TyVar qvars) (map X.EvVar instEvVars))

                              findDecl :: Functions Pred KId -> Maybe (Function Pred KId)
                              findDecl [] = Nothing
                              findDecl (f@(name, _, _) : rest)
                                  | mname == name = Just f
                                  | otherwise     = findDecl rest


                    split [] = []
                    split xs = [(n, x, xs' ++ xs'') | n <- [0..length xs - 1], let (xs', x : xs'') = splitAt n xs]

                    Pred _ classArgs Holds = conclusion
                    s = new (zip classParams (map dislocate classArgs))

                    hypotheses'             = map (X.convert . dislocate) hypotheses
                    conclusion'             = X.convert conclusion
                    qvars                   = nub (X.tvs hypotheses' ++ X.tvs conclusion')  -- Ordering of type variables?
                    evScheme                = X.Forall qvars (X.gen 0 qvars hypotheses') (X.gen 0 qvars conclusion')

translateInstance _ = error "Typechecker.TypeInference:893"

assertRequirement :: TopDecl Pred KId KId -> M ()
assertRequirement (Require ps qs) =
    trace (show ("Requiring" <+> cat (punctuate ", " (map (ppr . snd) ps)) <+> "if" <+> cat (punctuate ", " (map ppr qs)))) $
    assert (Solver.newRequirement qs ps)

assertPrimitive :: Primitive Pred KId -> M (X.Defns, CtorEnv)
assertPrimitive (PrimCon (Signature name tys) impl) =
    do tys' <- simplifyScheme tys
       return ([X.PrimDefn name (X.convert tys') (impl, [])],
               Map.singleton name (tys, 0))
assertPrimitive (PrimClass name _ fundeps _) =
    do mapM_ (assert . Solver.newFunDep name) fundeps'
       modify updateClassEnv
       return ([], Map.empty)
    where fundeps' = map dislocate fundeps
          updateClassEnv st =
              st { classEnvironment = cenv { functionalDependencies = Map.insert name fundeps' (functionalDependencies cenv) } }
              where cenv = classEnvironment st
assertPrimitive _ = return ([], Map.empty)

 ----------------------------------------------------------------------------------------------------

checkProgram :: String -> Program Pred KId KId -> M (X.Program KId, Map Id (X.Scheme X.Type, Int), TyEnv)
checkProgram fn p =
    appendFailureContext (text "In" <+> text fn) $
    do (primDecls, primCtors) <- unzip `fmap` mapM (mapLocated assertPrimitive) (primitives p)
       (methodTypeEnvironments, selectorImpls, defaultMethodImpls) <- unzip3 `fmap` mapM (mapLocated assertClass) classDecls
       mapM (mapLocated assertRequirement) requirementDecls
       derived <- deriveInstances p
       trace ("Derived instances:\n" ++ show (vcat (map ppr derived))) (return ())
       let instanceDecls' = instanceDecls ++ derived
       (evDecls, methodImpls) <- assertInstances (map instanceName derived) instanceDecls'
       areaTypes' <- mapM (\(n, tys) -> do ty <- simplifyAreaType tys
                                           return (n, LamBound ty)) areaTypes
       let globals = Map.unions (Map.fromList areaTypes' : methodTypeEnvironments)
       declare globals $
            do (typeDecls', ctorEnvironments) <- unzip `fmap` mapM (mapLocated checkTopDecl) typeDecls
               let ctorEnvironment = Map.unions (primCtors ++ ctorEnvironments)
                   ctorTypes       = tyEnvFromCtorEnv ctorEnvironment
               bindCtors ctorEnvironment
               declare ctorTypes $
                    do rDecls <- checkDecls (concatDecls [decls p, Decls (concat defaultMethodImpls), Decls methodImpls]) -- (decls', ps, valueTypes)
                       let (decls', valueTypes) = payload rDecls
                       (evsubst, remaining) <- traceIf (not (null (goals rDecls))) (show ("Solving remaining top-level constraints:" <+>
                                                                                          pprList' (map snd (assumed rDecls)) <+> "=>" <+>
                                                                                          pprList (map snd (goals rDecls)))) $
                                               withoutConditionalBindings (entails [] [] (assumed rDecls) (goals rDecls))
                       when (not (null remaining)) $ contextTooWeak (assumed rDecls) remaining
                       declare valueTypes $
                            do (areaDecls', _) <- unzip `fmap` mapM (mapLocated checkTopDecl) areaDecls
                               s <- gets (convert . currentSubstitution)
                               return ( X.Program (X.consDecls (concat (selectorImpls ++ primDecls))
                                                               (s X.# addEvidence evsubst decls'))
                                                  (s X.# typeDecls' ++ s X.# areaDecls')
                                                  (Map.fromList (evDecls))
                                      , Map.map (\(tys, n) -> (convert tys, n)) ctorEnvironment
                                      , Map.unions [globals, ctorTypes, valueTypes] )

    where (typeDecls, areaDecls, classDecls, instanceDecls, requirementDecls) = partitionDecls (topDecls p)
              where partitionDecls [] = ([], [], [], [], [])
                    partitionDecls (d:ds) = addDecl d (partitionDecls ds)
                        where addDecl d@(At _ (Class {})) (types, areas, classes, instances, requirements)
                                = (types, areas, d : classes, instances, requirements)
                              addDecl d@(At _ (Instance {})) (types, areas, classes, instances, requirements)
                                = (types, areas, classes, d : instances, requirements)
                              addDecl d@(At _ (Area {})) (types, areas, classes, instances, requirements)
                                = (types, d : areas, classes, instances, requirements)
                              addDecl d@(At _ (Require {})) (types, areas, classes, instances, requirements)
                                = (types, areas, classes, instances, d:requirements)
                              addDecl d (types, areas, classes, instances, requirements)
                                = (d : types, areas, classes, instances, requirements)

          areaTypes = [(name, At loc tys) | At loc (Area _ inits tys) <- areaDecls,
                                            name <- [name | (At _ name, _) <- inits]]

          simplifyAreaType (At loc tys) =
              failAt loc $
              do ksc <- simplifyScheme (ForallK [] tys)
                 case ksc of
                   ForallK [] (Forall [] ([] :=> At _ ty)) ->
                       return ty
                   _ ->
                       failWith (group (hang 4 ("Unsupported area type" <+> ppr tys <$> parens ("simplifies to" <+> ppr ksc))))

          mapLocated :: (t -> M u) -> Located t -> M u
          mapLocated f (At l t) = failAt l $ f t

          instanceName (At _ (Instance name _ _)) = name
          instanceName _                          = error "instanceName"
