{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Syntax.XMPEG (module Syntax.Common, module Syntax.XMPEG) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Syntax.Common
import qualified Syntax.IMPEG as I
import qualified Utils.BDD as BDD

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Type = TyCon (Kinded Id)
          | TyVar (Kinded Id)
          | TyGen Int
          | TyApp Type Type
          | TyNat Integer
          | TyLabel Id
            deriving (Eq, Show)

flattenType :: Type -> (Type, [Type])
flattenType (TyApp lhs rhs) = (op, ts ++ [rhs])
    where (op, ts) = flattenType lhs
flattenType t               = (t, [])

kindOf :: Type -> Kind
kindOf (TyCon (Kinded _ k))  = k
kindOf (TyVar (Kinded _ k))  = k
kindOf (TyGen _)             = error "Syntax.XMPEG:30"
kindOf (TyApp t _) =
    case kindOf t of
      KFun _ result -> result
      _             -> error "Syntax.XMPEG:34"
kindOf (TyNat _)             = KNat
kindOf (TyLabel _)           = KLabel

instance Convertable s t => Convertable (KScheme s) t
    where convert (ForallK _ x) = convert x

instance Convertable (I.Type KId) Type
    where convert (I.TyCon id)                 = TyCon id
          convert (I.TyVar id)                 = TyVar id
          convert (I.TyGen i)                  = TyGen i
          convert (I.TyApp (At _ t) (At _ t')) = TyApp (convert t) (convert t')
          convert (I.TyNat i)                  = TyNat i
          convert (I.TyKinded {})              = error "TyKinded in convert :: IMPEG.Type KId -> XMPEG.Type"
          convert (I.TyLabel id)               = TyLabel id

instance Convertable (Pred (Located (I.Type KId))) (Pred Type)
    where convert (Pred cl ts f) = Pred cl (map (convert . dislocate) ts) f
instance Convertable (KId, I.Type KId) (KId, Type)
    where convert (v, t) = (v, convert t)
instance Convertable ([(KId, I.Type KId)], [(KId, I.Type KId)]) ([(KId, Type)], [(KId, Type)])
    where convert (cond, impr) = (convert cond, convert impr)

data Scheme t = Forall [KId] [Pred Type] t

instance Convertable (I.Scheme I.Pred KId) (Scheme Type)
    where convert (I.Forall ks (ps I.:=> At _ t)) = Forall ks (map (convert . dislocate) ps) (convert t)

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

data Expr      = ELamVar Id
               | ELetVar Inst
               | EBits Integer Int
               | ECon Inst
               | ELam Id Type Expr
               | EMethod Ev Int [Type] [Ev]  -- dictionary method typarams evparams
               | ELet Decls Expr
               | ELetTypes TypeBinding Expr
               | ESubst ExprSubst EvSubst Expr
               | EMatch Match
               | EApp Expr Expr
               | EBind Type Type Type Ev Id Expr Expr -- {ta,tb,tm}{me :: Proc tm} (id :: ta) <- e ; (e' :: tm tb)

type TypeBinding = Either [([(KId, Type)], [(KId, Type)])] ([KId], [KId], [Type] -> [Type])
type ExprSubst = [(Id, Expr)]
type EvSubst   = [(Id, Ev)]

instance HasVariables Expr
    where freeVariables (ELamVar id)            = [id]
          freeVariables (ELetVar (Inst id _ _)) = [id]
          freeVariables (EBits {})              = []
          freeVariables (ECon {})               = []
          freeVariables (ELam id _ body)        = filter (id /=) (freeVariables body)
          freeVariables (ELet ds body)          = freeVariables ds ++ withoutBound ds (freeVariables body)
          freeVariables (ESubst ps _ body  )    = concatMap freeVariables exprs ++ filter (`notElem` ids) (freeVariables body)
              where (ids, exprs) = unzip ps
          freeVariables (EMatch m)              = freeVariables m
          freeVariables (EApp e e')             = freeVariables e ++ freeVariables e'
          freeVariables (EBind _ _ _ _ id e e') = freeVariables e ++ filter (id /=) (freeVariables e')
          rename _ = id

flattenApp :: Expr -> (Expr, [Expr])
flattenApp (EApp lhs rhs) = (op, args ++ [rhs])
    where (op, args) = flattenApp lhs
flattenApp e = (e, [])

flattenLambda :: Expr -> ([(Id, Type)], Expr)
flattenLambda (ELam v t e) = ((v, t) : params, body)
    where (params, body) = flattenLambda e
flattenLambda e = ([], e)

flattenDo :: Expr -> ([(Type, Type, Type, Ev, Id, Expr)], Expr)
flattenDo (EBind ta tb tm me id e e') = ((ta, tb, tm, me, id, e) : binds, result)
    where (binds, result) = flattenDo e'
flattenDo e = ([], e)

data Ev = EvVar Id
        | EvCons Inst
        | EvRequired Id [Ev]
        | EvCases [([(KId, Type)], Ev)]
        | EvComputed [KId] ([Type] -> Ev)
        | EvFrom EvPat Ev Ev

evVars :: Ev -> [Id]
evVars (EvVar id) = [id]
evVars (EvCons _) = []
evVars (EvRequired _ evs) = concatMap evVars evs
evVars (EvCases bs) = concatMap (evVars . snd) bs
evVars (EvComputed _ _) = []
evVars (EvFrom EvWild e e') = evVars e ++ evVars e'
evVars (EvFrom (EvPat _ _ vs) e e') = evVars e ++ filter (`notElem` vs) (evVars e')

data EvPat = EvPat Id [Type] [Id] | EvWild

type RequirementImpls = Map Id [([EvPat], Ev)]

data Gen t = Gen [Kinded Id] [Id] t
data Inst  = Inst Id [Type] [Ev]

--------------------------------------------------------------------------------
-- Matches
--------------------------------------------------------------------------------

data Match = MFail                    -- "fail"            match failure
           | MCommit Expr             -- "^ e"             commit result
           | MElse Match Match        -- "m1 | m2"         alternative
           | MGuarded Guard Match     -- "g => m"          guarded matches

instance HasVariables Match
    where freeVariables MFail          = []
          freeVariables (MCommit e)    = freeVariables e
          freeVariables (MElse m m')   = freeVariables m ++ freeVariables m'
          freeVariables (MGuarded g m) = freeVariables g ++ withoutBound g (freeVariables m)
          rename _ = id

flattenElses :: Match -> [Match]
flattenElses (MElse m m') = ms ++ ms'
    where ms = flattenElses m
          ms' = flattenElses m'
flattenElses m = [m]

flattenGuards :: Match -> ([Guard], Match)
flattenGuards (MGuarded g m) = (g:guards, result)
    where (guards, result) = flattenGuards m
flattenGuards m = ([], m)

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

data Pattern = PWild
             | PVar Id Type     -- TODO: Why is there a type annotation here?
             | PCon Inst [Id]

instance HasVariables Pattern
    where freeVariables PWild          = []
          freeVariables (PVar {})      = []
          freeVariables (PCon {})      = []
          rename _ = id

instance Binder Pattern
    where bound PWild           = []
          bound (PVar v _)      = [v]
          bound (PCon _ vs)     = vs

--------------------------------------------------------------------------------
-- Guards
--------------------------------------------------------------------------------

data Guard = GFrom Pattern Id
           | GLet Decls
           | GSubst EvSubst
           | GLetTypes TypeBinding

instance Binder Guard
    where bound (GFrom p _)   = bound p
          bound (GLet ds)     = bound ds
          bound (GSubst _)    = []
          bound (GLetTypes _) = []

instance HasVariables Guard
    where freeVariables (GFrom p id)  = id : freeVariables p
          freeVariables (GLet ds)     = freeVariables ds
          freeVariables (GSubst _)    = []
          freeVariables (GLetTypes _) = []
          rename _ = id

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

-- Equivalent to:
--   name :: scheme
--   name{typarams}{evparams} = e
data Defn = Defn Id (Scheme Type) (Either (String, [Type]) (Gen Expr)) -- Left => primitive
type Defns = [Defn]

instance HasVariables Defn
    where freeVariables (Defn name _ (Right (Gen _ _ body))) =
            filter (name /=) (freeVariables body)
          freeVariables (Defn name _ (Left _)) = []
          rename _ = id

instance Binder Defn
    where bound (Defn name _ _) = [name]

data Decls = Decls [Defn]

emptyDecls           :: Decls -> Bool
emptyDecls (Decls []) = True
emptyDecls _          = False

consDecls               :: Defns -> Decls -> Decls
consDecls ds (Decls ds') = Decls (ds ++ ds')

appendDecls             :: Decls -> Decls -> Decls
appendDecls (Decls ds) (Decls ds')
                         = Decls (ds ++ ds')

concatDecls             :: [Decls] -> Decls
concatDecls ds           = Decls (concat [defns | Decls defns <- ds])

instance HasVariables Decls
    where freeVariables (Decls []) = []
          freeVariables (Decls (d:ds)) = freeVariables d ++ withoutBound d (freeVariables (Decls ds))
          rename _ = id

instance Binder Decls
    where bound (Decls ds) = concatMap bound ds

--------------------------------------------------------------------------------
-- Top-level declarations
--------------------------------------------------------------------------------

type TopDecls typaram = [TopDecl typaram]

data TopDecl typaram
             = Datatype Id                             -- type name
                        [typaram]                      -- params
                        [(Id, [KId], [Pred Type], [Type])] -- ctors

             | Bitdatatype Id                          -- type name
                           BDD.Pat                     -- BDD for full type
                           [BitdataCtor]               -- ctors

             | Struct Id                               -- type name
                      Int                              -- size in bytes
                      [StructField]                    -- fields

             | Area Bool [(Id, Inst)] Type Int Int     -- (name, init) type size alignment

type BitdataCtor  = (Id, [BitdataField], BDD.Pat)      -- (name, list of fields, coverage)
data BitdataField = LabeledField Id Type BDD.Pat Int   -- name, type, coverage, offset in bits
                  | ConstantField Integer BDD.Pat Int  -- value, coverage, offset
data StructField = StructField (Maybe Id) Type Int Int -- name, type, width, offset in bytes

-- Dictionary constructors:

-- class Fractional a => RealFrac a
--     where floor :: Integral b => a -> b
--
-- instance Fractional Float
-- instance RealFrac Float
--     where floor = floatFloor
--
-- floatFloor :: Integral b => Float -> b
-- floatFloor x = primitive
--
--    becomes a mapping from "RealFrac_Float" to ...
--
--    (Forall {}. {} => RealFrac Float,
--     ({} {} -> ([{b}{d} -> floatFloor{b}{d}])))
--
-- floatFloor :: Forall {b}. {Integral b} => Float -> b
-- floatFloor{b}{dictIntegralB} = primitive
--
--    where we could (but don't need to) generate the definition:
--
-- floor :: Forall {a,b}. {RealFrac a, Integral b} => a -> b
-- floor{a,b}{rfDict,integralDict} = \x::a -> EMethod rfDict 0 {b} {integralDict}

type EvDecls          = Map Id EvDecl
type EvDecl           = ( Scheme (Pred Type)          -- evidence type scheme
                        , Gen ([Gen Inst]) )          -- methods

--------------------------------------------------------------------------------

data Program typaram
             = Program { decls    :: Decls
                       , topDecls :: TopDecls typaram
                       , evidence :: EvDecls }

emptyProgram :: Program typaram
emptyProgram  = Program { decls    = Decls []
                        , topDecls = []
                        , evidence = Map.empty }

appendPrograms :: Program typaram -> Program typaram -> Program typaram
appendPrograms (Program ds tds evs) (Program ds' tds' evs') =
    Program (appendDecls ds ds') (tds ++ tds') (Map.union evs evs')

concatPrograms       :: [Program typaram] -> Program typaram
concatPrograms []     = emptyProgram
concatPrograms [p]    = p   -- special (common?) case
concatPrograms (p:ps) = appendPrograms p (concatPrograms ps)

-- "I might spend some time this coming week sleeping"
-- "I wouldn't want to be without my midterm grading this weekend..."
