{-# LANGUAGE OverloadedStrings #-}
module Typechecker.LambdaCase where

import Common
import Control.Monad.State
import Syntax.LambdaCase
import Syntax.Common
import Printer.Common (text, vcat)
import Printer.LambdaCase
import Typechecker.LambdaCasePrims
import Typechecker.LambdaCaseTyping hiding (type_from_tcon)

import Control.Monad

checkLCProgram :: Pass () Program Program
checkLCProgram p = case checkProgram p of
                     Ok _       -> return p
                     Errs errss -> failWith (vcat (map (vcat . map text) errss))

{-- Specific Types -------------------------------------------------------

some functions for constructing instances of parametric types

-}

bitsT       :: Int -> Type
bitsT n      = tapply1 bitsCon (TyLit (fromIntegral (n)))
    where bitsCon = TyCon (Kinded "Bit" (KNat `KFun` KStar))  -- not sure about the kind here!

funCon :: Type
funCon = TyCon (Kinded "->" (KStar `KFun` (KStar `KFun` KStar)))


-- Build fully-saturated type from type constructor name and parameter instances
-- ripped fair and square from APT's middle-end work, LambdaCaseTyping.hs
type_from_tcon :: Id -> [Type] -> Type
type_from_tcon d ts =
     tapplyn (TyCon (Kinded d (foldr ( \t k -> kindOf t `KFun` k) KStar ts))) ts


-- get this from Syntax.Common? nope. look at the type
kindOf :: Type -> Kind
kindOf _ = KStar


{-- random helpers ------------------------------------------------------

-}


typeError :: Type -> Type -> String -> [String]
typeError e g x = [ "Expected: ", showType e
                  , "Got: ", showType g
                  , "In: ", x]

-- strip of the outer applications to compare two inner types on the
-- right side. This is used in Area declarations to confirm that for
-- types Ref Foo and Init Foo, the Foos match. Not very robust since
-- the left argument to TyApp could incorrect...
tyAppRightCompare                          :: Type -> Type -> Bool
tyAppRightCompare (TyApp _ t) (TyApp _ t') = t == t'
tyAppRightCompare  _ _                     = False

{- THE MONAD!!! -}
data TM a = Ok a | Errs [[String]]

instance Functor TM
    where fmap f (Ok a) = Ok (f a)
          fmap _ (Errs ss) = Errs ss

instance Applicative TM
    where pure = return
          (<*>) = liftM2 ($)

instance Monad TM where
    Ok x    >>= f = f x
    Errs es >>= _ = Errs es
    return        = Ok

orTypeFail             :: TM a -> [String] -> TM a
orTypeFail (Ok x) _    = Ok x
orTypeFail (Errs es) e = Errs (e : es)

infixl 1 `orTypeFail`

typeFail :: [String] -> TM a
typeFail s = Errs [s]

typeFailIn :: String -> [String] -> TM a
typeFailIn e es = Errs [e:es]

{-- Context ------------------------------------------------------------

a typing context is a function from a ContextEntry to (String + Type). The
string is some error message relating to a failure to look up a type
in the context or failure to properly construct the context

A ContextEntry is either some partially or fully applied Term, or it
is a special constructor entry, CaseAlt, to use in case alternatives
for verifying the left hand side. In the case of a Term, there are two
cases, either the term is a constructor or it is a binding. If it is a
constructor, then it will be specialized and will be looked up using
both the Id and its instantiating types. If it is a bound term, then
the list of instantiating types will be empty and ignored. In the case
of a CaseAlt, the lookup matches both the Id and the list of Types
representing the particular instantiation of that constructor. This
will return the return type of the constructor, that is, the type of
the constructor if fully applied. This allows matching the left side
of a case alternative against the discriminant

-}

type Context = ContextEntry -> TM Type

data ContextEntry = Term Id [Type]
                  | CaseAlt Id [Type]
                    deriving (Show, Eq)

empty :: Context
empty i = typeFail ["Term " ++ show i ++ " not in context"]


-- the context is updated by wrapping another function around the supplied context.
--
-- there are several helpers here for updating for the more complex expressions
--

update       :: Context -> ContextEntry -> Type -> Context
update g i t = \i' -> if i == i'
                      then return t
                      else g i'

-- specifically excluded recursion here...
updateDefn                       :: Context -> Defn -> TM Context
updateDefn gamma d@(Defn i ty e) = do
  case e of
    Left _ -> return ()
    Right e' -> do ty' <- checkExpr gamma e'
                   unless (ty == ty') (
                     typeFailIn "Type mismatch in Defn\n" $ typeError ty ty' (show d))
  return (update gamma (Term i []) ty)

updateDecl                      :: Context -> Decl -> TM Context
updateDecl gamma (Mutual defns) = updateMutuals gamma defns
updateDecl gamma (Nonrec defn)  = updateDefn gamma defn


-- special top-level only handling of decls ensures functions only at
-- top level
updateDecls_top :: Decls -> Context -> TM Context
updateDecls_top (Decls ds) gamma = foldM updateDecl_top gamma ds

updateDecl_top :: Context -> Decl -> TM Context
updateDecl_top g d@(Mutual _) = updateDecl g d
updateDecl_top g d@(Nonrec def) | isLambda def = updateDecl g d
updateDecl_top _ d = typeFail ["Non-functional top-level decl found: ", show d]

-- explicitly add the  recursive occurence...
updateMutuals :: Context -> [Defn] -> TM Context
updateMutuals gamma defns
    | all isLambda defns = foldM updateDefn gamma' defns
    | otherwise          = typeFail ["Non-functional mutual declaration in declaration group: ", show defns]
    where gamma' = foldl (\g (Defn i ty _) -> update g (Term i []) ty) gamma defns


-- updateMutuals :: Context -> Defn -> TM Context
-- updateMutuals g d@(Defn i ty _) | isLambda d = updateDefn (update g (Term i []) ty) d
-- updateMutuals _ d = typeFail ["Non-functional Mutual Decl. Found: " , show d]

-- only manifest lambdas or machine monad types...
isLambda :: Defn -> Bool
isLambda (Defn _ _ (Left _)) = True -- TODO: until we get it right
isLambda (Defn _ _ (Right (ELam _ _ _))) = True
isLambda (Defn _ (TyApp (TyCon (Kinded "M" _)) _) (Right (EBind _ _ _ _))) = True
isLambda (Defn _ (TyApp (TyCon (Kinded "I" _)) _) (Right (EBind _ _ _ _))) = True
isLambda _ = False

updateDecls :: Decls -> Context -> TM Context
updateDecls (Decls ds) gamma = foldM updateDecl gamma ds


{-- Type Checking --------------------------------------------------

the fundamental operation is to typecheck an expression. Most of these
are just the generation of base types, or confirming that references
to types match in the context

-}

checkExpr                          :: Context -> Expr -> TM Type
checkExpr gamma t@(EVar i ty)      = do ty' <- gamma (Term i [])
                                               `orTypeFail` ["Failed to type variable ", show t]
                                        if ty' == ty
                                          then return ty'
                                          else typeFailIn "Type mismatch in variable annotation" $ typeError ty ty' (show t)
checkExpr gamma t@(ECon i tys ty)  = do ty' <- gamma (Term i tys)
                                               `orTypeFail` ["Failed to type constructor: ", show t]
                                        if ty' == ty
                                           then return ty'
                                           else typeFailIn "Type mismatch in constructor annotation" $ typeError ty ty' (show t)
checkExpr _       (EBits _ s)      = return $ bitsT s
checkExpr _       (ENat n)         = return $ natT n
checkExpr gamma t@(ELam i ty e)    = do ty' <- checkExpr (update gamma (Term i []) ty) e
                                                 `orTypeFail` ["Failed to type lambda: ", show t]
                                        return $ ty `fun` ty'
checkExpr gamma t@(ELet ds e)      = do g' <- updateDecls ds gamma
                                        checkExpr g' e
                                          `orTypeFail` ["Failed to type let: ", show t]
-- first we get the type of the discriminant, then check the
-- alternatives. need to fix the monad here (and everywhere), Either
-- doesn't pass through out messages the way I'd like...
checkExpr gamma t@(ECase e (a:as)) =  do dty <- checkExpr gamma e
                                                  `orTypeFail` [ "Case failed to type discriminant: ", show e
                                                               , "In: ", show t]
                                         t' <- checkAlt dty gamma a
                                         checkAlts dty t' gamma as
checkExpr _     t@(ECase _ [])     = typeFail ["Invalid case. Missing alternatives: ", show t]

checkExpr gamma t@(EApp e1 e2)     = do t1 <- checkExpr gamma e1
                                        t2 <- checkExpr gamma e2
                                        app t1 t2 t `orTypeFail` ["Failed to type App of: ", show e1
                                                                 ,"To: ", show e2]
checkExpr gamma t@(EFatbar e1 e2)  = do t1 <- checkExpr gamma e1
                                        t2 <- checkExpr gamma e2
                                        if t1 == t2
                                           then return t1
                                           else typeFail ["Fatbar type mis-match in " , show t]
checkExpr gamma t@(EBind i ty e1 e2) = do ty1 <- checkExpr gamma e1
                                          m   <- extractMonad t ty ty1
                                          ty2 <- checkExpr (update gamma (Term i []) ty) e2
                                          case ty2 of
                                            (TyApp m' _) | m == m'   -> return ty2
                                                         | otherwise -> typeFailIn "Monad type mis-match in EBind, " $ typeError m m' (show t)
                                            _                        -> typeFail ["Invalid type in EBind ", show t]

extractMonad                              :: Expr -> Type -> Type -> TM Type
extractMonad _ ty (TyApp m ty') | ty == ty' = return m
extractMonad t ty ty'                       = typeFail ["Bind type mis-match extracting monad", show t, show ty, show ty']

-- confirm the selector type matches discriminant type, bind the vars
-- and then return the type of the righthand side to get the type of
-- the entire case statement
checkAlt :: Type -> Context -> Alt -> TM Type
checkAlt dty gamma a@(Alt i tys is e)
    = do rty <- gamma (CaseAlt i tys)
         t' <- gamma (Term i tys)
         if dty == rty
             then let argTs = argTypes t'
                      g' = foldr (\(i',t) g -> update g (Term i' []) t) gamma $ zipWith (,) is argTs
                  in checkExpr g' e
             else typeFailIn "Selector type mis-match:  " $ typeError dty rty (show a)

checkAlts :: Type -> Type -> Context -> [Alt] -> TM Type
checkAlts _ ty _ [] = return ty
checkAlts dty ty gamma (a:as) = do ty' <- checkAlt dty gamma a
                                   if ty == ty'
                                      then checkAlts dty ty gamma as
                                      else typeFailIn "Alternative type mis-match: " $ typeError ty ty' (show a)

-- extract the argument types from a constructor type. this probably
-- makes the distinction betwee CaseAlt and Term irrelevant
argTypes :: Type -> [Type]
argTypes (TyApp (TyApp (TyCon (Kinded "->" _)) t) ts) = t : (argTypes ts)
argTypes _ = []

-- here we put in two versions of each constructor. One to be used
-- when applying the constructor, one to match the discriminee in a
-- case statement Alt
build_ctor :: Type -> [Type] -> Context -> (Id, [Type]) -> Context
build_ctor t its gamma (i, tys) = update (update gamma (Term i its) t') (CaseAlt i its) t
    where
      t' = foldr fun t tys

bitdata :: Type -> Id -> Type
bitdata tcon dcon = tapply2 (TyCon (Kinded "BitdataCase" (KFun KStar (KFun KLabel KStar))))
                    tcon
                    (TyLabel dcon)

build_bit_ctor :: Type -> [Type] -> Context -> (Id, [BitdataField]) -> Context
build_bit_ctor t its gamma (i, _) = update (update gamma (CaseAlt i its) t) (Term i []) conTy
    where conTy = bitdata t i `fun` t

buildTopDecl                              :: Context -> TopDecl -> TM Context
buildTopDecl gamma (Datatype i tys ctors) = let ty = type_from_tcon i tys
                                                ctxt = foldl (build_ctor ty tys) gamma ctors
                                            in return ctxt
buildTopDecl gamma (Bitdatatype i _ ps)   = let ty = (TyCon (Kinded i KStar))
                                                ctxt = foldl (build_bit_ctor ty []) gamma ps
                                            in return  ctxt
buildTopDecl gamma (Area i _ _ ty _ _)    =  return $ update gamma (Term i []) ty

buildTopDecl gamma t@(Struct _ _ _)       = return gamma -- typeFail ["Unimplemented top level declaration:", show t]

buildTopDecls :: TopDecls -> Context -> TM Context
buildTopDecls tds gamma = foldM buildTopDecl gamma tds

-- when we check an initializer, we need to already have the
-- environment built up. then we just confirm that the initializer
-- expression accepts the proper ref type as an argument (and returns
-- some monadic unit type as well, I suppose, TODO).
checkInitializer :: Context -> TopDecl -> TM Context
checkInitializer gamma t@(Area i _ e ty s a) =
    do ty' <- checkExpr gamma e `orTypeFail` ["typing initializer: ", show t]
       case ty' of
         (TyApp (TyApp (TyCon (Kinded "->" _)) arg)
          (TyApp (TyCon (Kinded "I" _)) (TyCon (Kinded "Unit" _)))) ->
           if arg == ty
           then return gamma
           else typeFail ["Initializer type mis-match in: ", show t, show arg, show ty]
         (TyApp (TyApp (TyCon (Kinded "->" _)) arg)
           (TyApp (TyApp (TyCon (Kinded "->" _)) (TyCon (Kinded "Unit" _)))
             (TyCon (Kinded "Unit" _)))) ->
           if arg == ty
           then return gamma
           else typeFail ["Thunkified initializer type mis-match in: ", show t, show arg, show ty]
         _ -> typeFail ["Ill typed initializer in: ", show t]
checkInitializer gamma _ = return gamma

checkInitializers :: TopDecls -> Context -> TM Context
checkInitializers tds gamma = foldM checkInitializer gamma tds

checkProgram :: Program -> TM Context
checkProgram p = do g <- buildTopDecls (topDecls p) empty
                    g' <- updateDecls_top (decls p) g
                    checkInitializers (topDecls p) g'

check :: Program -> String
check p = case checkProgram p of
            Ok _ -> "Success"
            Errs s  -> unlines $ map unlines s

-- this function decomposes the types in an EApp and checks for type matching.
app                             :: Type -> Type -> Expr -> TM Type
app (TyApp (TyApp arr t1) t2) t3 e
    | arr == funCon && t1 == t3 = return t2
    | arr == funCon             = typeFail $ typeError t1 t3 (show e)
app l r _                       = typeFail ["Cannot apply ", showType l, "To ", showType r]



{-- Instances ----------------------------------------------------------

it helps to be able to show things...

-}

instance Show Expr where
    show = show . ppr

instance Show Defn where
    show = show . ppr

instance Show TopDecl where
    show = show . ppr

instance Show Alt where
    show = show . ppr

instance Show Decl where
    show = show . ppr

showType :: Type -> String
showType = show . ppr
