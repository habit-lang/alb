{-# LANGUAGE DeriveDataTypeable #-}
module Syntax.Surface (module Syntax.Surface, module Syntax.Common)  where

import Data.Generics hiding (Fixity)
import Data.Map (Map)
import qualified Data.Map as Map
import Syntax.Common hiding (Pred(..))

--------------------------------------------------------------------------------
-- Kinds and types
--------------------------------------------------------------------------------

data Type = TyCon Id
          | TyVar Id
          | TyWild
          | TyApp (Located Type) (Located Type)
          | TyNat Integer
          | TyTuple [Located Type]
          | TyTupleCon Int
          | TyKinded (Located Type) (Located Kind)
          | TyLabel Id
          | TySelect (Located Type) (Located Id)
          | TyInfix (Located Type) [(Located Id, Located Type)]
            deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------
-- Predicates and qualifiers
--------------------------------------------------------------------------------

data Pred = Pred (Located Type) (Maybe (Located Type)) Flag
            deriving (Eq, Show, Typeable, Data)

data Qual t = [Located Pred] :=> Located t
              deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------
-- Expressions and statements
--------------------------------------------------------------------------------

data Expr = ELet Decls (Located Expr)
          | EIf Scrutinee (Located Expr) (Located Expr) -- Parser will inject magical "return ()" in if statements
          | ECase Scrutinee [Alt]
          | ELam [Located Pattern] (Located Expr)
          | EVar Id
          | ECon Id
          | ELit Literal
          | ETuple [Located Expr]
          | ETupleCon Int
          | EApp (Located Expr) (Located Expr)
          | EBind (Maybe Id) (Located Expr) (Located Expr)
          | ESelect (Located Expr) (Located Id)
          | EUpdate (Located Expr) [(Located Id, Located Expr)]
          | ELeftSection (Located Expr) (Located Id)
          | ERightSection (Located Id) (Located Expr)
          | EStructInit (Located Id) [(Located Id, Located Expr)]
          | ETyped (Located Expr) (Qual Type)
          | EInfix (Located Expr) [(Located Id, Located Expr)]
            deriving (Eq, Show, Typeable, Data)

data Scrutinee = ScExpr (Located Expr)
               | ScFrom (Maybe Id) (Located Expr)
               deriving (Eq, Show, Typeable, Data)

data Alt = Located Pattern :-> Rhs deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

data Pattern = PVar Id
             | PLit Literal
             | PWild
             | PAs Id (Located Pattern)
             | PTyped (Located Pattern) (Qual Type)
             | PCon Id
             | PTuple [Located Pattern]
             | PTupleCon Int
             | PApp (Located Pattern) (Located Pattern)
             | PLabeled Id [Located FieldPattern]
             | PInfix (Located Pattern) [(Located Id, Located Pattern)]
               deriving (Eq, Show, Typeable, Data)

flattenPattern :: Located Pattern -> (Located Pattern, [Located Pattern])
flattenPattern (At _ (PApp lhs rhs)) = (op, ps ++ [rhs])
    where (op, ps) = flattenPattern lhs
flattenPattern p = (p, [])

instance Binder Pattern
    where bound (PVar id)           = [id]
          bound (PAs id p)          = id : bound p
          bound (PTyped p _)        = bound p
          bound (PTuple ps)         = concatMap bound ps
          bound (PApp p p')         = bound p ++ bound p'
          bound (PLabeled _ ps)     = concatMap bound ps
          bound (PInfix first rest) = bound first ++ filter (not . isConId) (map dislocate operators) ++ bound operands
              where (operators, operands) = unzip rest
          bound p                   = []

data FieldPattern = FieldPattern Id (Located Pattern)
                    deriving (Eq, Show, Typeable, Data)

instance Binder FieldPattern
    where bound (FieldPattern _ p) = bound p

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

data Equation = Located Pattern := Rhs
              deriving (Eq, Show, Typeable, Data)

instance Binder Equation
    where bound (p := _) = bound p

data Rhs = Unguarded (Located Expr) (Maybe Decls)
         | Guarded [(Located Expr, Located Expr)] (Maybe Decls) -- List of (guard, body)
           deriving (Eq, Show, Typeable, Data)

--

data Fixities = Fixities { valFixities :: Map Id (Located Fixity)
                         , typeFixities :: Map Id (Located Fixity) }
                deriving (Eq, Show, Typeable, Data)


mergeFixities :: Fixities -> Fixities -> Fixities
mergeFixities old new = Fixities (Map.unionWith second (valFixities old) (valFixities new))
                                 (Map.unionWith second (typeFixities old) (typeFixities new))
    where second _ x = x

emptyFixities = Fixities Map.empty Map.empty

--

data Signature = Signature Id (Qual Type)
                 deriving (Eq, Show, Typeable, Data)

--

data Decls = Decls { equations  :: [Equation]
                   , signatures :: [Signature]
                   , fixities   :: Fixities }
             deriving (Eq, Show, Typeable, Data)

emptyDecls = Decls [] [] (Fixities Map.empty Map.empty)

instance Binder Decls
    where bound ds = concatMap bound (equations ds)

--------------------------------------------------------------------------------
-- Classes and instances
--------------------------------------------------------------------------------

-- Introduce TypeLhs?

data Class = Class (Located Type) (Maybe (Located Type)) [Located ClassConstraint] (Maybe Decls)
                 deriving (Eq, Show, Typeable, Data)
data ClassConstraint = Superclass Pred | Fundep (Fundep Id) | Opaque Id
                       deriving (Eq, Show, Typeable, Data)

data Instance = Instance [(Qual Pred, Maybe Decls)]
                  deriving (Eq, Show, Typeable, Data)

data Requirement = Require [Located Pred] [Located Pred]
                 deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------
-- Type synonyms and data declarations
--------------------------------------------------------------------------------

data Synonym = Synonym (Located Type) (Qual Type) (Maybe Decls)
               deriving (Eq, Show, Typeable, Data)

data DataField = DataField (Maybe Id) (Located Type)
                 deriving (Eq, Show, Typeable, Data)

data Datatype = Datatype (Located Type)                 -- name and params
                         [Ctor Id Pred DataField]
                         [Id]                           -- deriving list
                         (Maybe Decls)                  -- opaque interface (should be sorted out)
                deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------
-- Bitdata and areas
--------------------------------------------------------------------------------

data Bitdatatype = Bitdatatype Id
                               (Maybe (Qual Type))
                               [Ctor Id Pred BitdataField]
                               [Id] -- deriving list
                 deriving (Eq, Show, Typeable, Data)

data BitdataField = LabeledField Id (Located Type) (Maybe (Located Expr))
                  | ConstantField (Located Literal)
                  deriving (Eq, Show, Typeable, Data)

data Struct = Struct Id (Maybe (Qual Type)) (Ctor Id Pred StructRegion) [Id]
              deriving (Eq, Show, Typeable, Data)
data StructRegion = StructRegion (Maybe StructField) (Located Type)
                  deriving (Eq, Show, Typeable, Data)
data StructField = StructField (Located Id) (Maybe (Located Expr))
                 deriving (Eq, Show, Typeable, Data)

data Area = Area Bool [(Located Id, Maybe (Located Expr))] (Qual Type) (Maybe Decls)
            deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------

data Primitive = PrimValue Signature String Bool -- String = external name, Bool = False iff private
               | PrimCon Signature String Bool
               | PrimType (Located Type)
               | PrimClass (Located Type) (Maybe (Located Type)) [Located (Fundep Id)] (Maybe Decls)
                 deriving (Eq, Show, Typeable, Data)

--------------------------------------------------------------------------------

data Program = Program { decls        :: Decls
                       , requires     :: [Located [String]]
                       , classes      :: [Located Class]
                       , instances    :: [Located Instance]
                       , requirements :: [Located Requirement]
                       , synonyms     :: [Located Synonym]
                       , datatypes    :: [Located Datatype]
                       , bitdatatypes :: [Located Bitdatatype]
                       , structures   :: [Located Struct]
                       , areas        :: [Located Area]
                       , primitives   :: [Located Primitive] }
               deriving (Eq, Show, Typeable, Data)

emptyProgram = Program { decls        = emptyDecls
                       , requires     = []
                       , classes      = []
                       , instances    = []
                       , requirements = []
                       , synonyms     = []
                       , datatypes    = []
                       , bitdatatypes = []
                       , structures   = []
                       , areas        = []
                       , primitives   = [] }
