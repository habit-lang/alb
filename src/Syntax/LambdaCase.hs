{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, DeriveDataTypeable #-}
module Syntax.LambdaCase (module Syntax.LambdaCase) where

import Data.Generics
import Syntax.Common hiding (Literal(..))
import qualified Syntax.XMPEG as X

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Type = TyCon (Kinded Id)
          | TyApp Type Type
          | TyLit Integer
          | TyLabel Id
            deriving (Eq, Ord, Show, Typeable, Data)

instance Convertable X.Type Type where
  convert (X.TyCon kid)                                      = TyCon kid
  convert (X.TyApp (X.TyCon (Kinded "Lab" _)) (X.TyLabel _)) = TyCon (Kinded "Unit" KStar)
  convert (X.TyApp l r)                                      = TyApp (convert l) (convert r)
  convert (X.TyNat n)                                        = TyLit n
  convert (X.TyLabel l)                                      = TyLabel l
  convert _                                                  = error "Can't convert XMPEG type variable"

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

data Expr = EVar Id Type
          | EBits Integer Int -- EBits n s :: Bit s
          | ENat Integer      -- ENat n    :: Nat n
          | ECon Id [Type] Type -- constructor name, type arguments, result type
          | EBitCon Id [(Id, Expr)]
          | EStructInit Id [(Id, Expr)]
          | ELam Id Type Expr
          | ELet Decls Expr
          | ECase Expr [Alt]  -- [Alt] never empty
          | EApp Expr Expr
          | EBitSelect Expr Id
          | EBitUpdate Expr Id Expr
          | EFatbar Expr Expr
          | EBind Id Type Expr Expr -- (id :: t) <- e ; e
          | EReturn Expr
  deriving (Eq, Typeable, Data)

data Alt  = Alt Id [Type] [Id] Expr  -- (C::t) vs -> e
  deriving (Eq, Typeable, Data)

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

data Defn  = Defn Id Type (Either (String, [Type]) Expr) -- Left = primitive
  deriving (Eq, Typeable, Data)
data Decl  = Mutual [Defn]        -- Exprs must all be ELam ...
           | Nonrec Defn          -- Defined Id can't appear in Expr
  deriving (Eq, Typeable, Data)
data Decls = Decls [Decl]         -- Maintained in topological order
  deriving (Eq, Typeable, Data)

--------------------------------------------------------------------------------
-- Top-level declarations
--------------------------------------------------------------------------------

-- bitdata T = S [B010 | x :: Ix 32] | Q [ y :: Bit 8 ]

data TopDecl = Datatype Id                         -- (source) name
                        [Type]                     -- specialized arguments
                        [(Id, [Type])]             -- ctors
             -- When do we convert bitdata operations to word operations?
             | Bitdatatype Id                      -- name
                           Int                     -- width in bits
                           [(Id, [BitdataField])]  -- params
             | Struct Id                           -- structure name
                      Int                          -- width in bytes
                      [StructField]                -- fields
             | Area Id                             -- area name
                    Bool                           -- volatility
                    Expr                           -- initializer
                    Type                           -- type
                    Int                            -- size (in bytes)
                    Int                            -- alignment
               -- Area-local definitions lifted to top level
  deriving (Eq, Typeable, Data)

data BitdataField = LabeledField Id Type Int Int   -- name, type, width, offset in bits
                  | ConstantField Integer Int Int  -- value, width, offset
  deriving (Eq, Show, Typeable, Data)
data StructField = StructField (Maybe Id) Type Int Int -- name, type, width, offset in bytes
  deriving (Eq, Show, Typeable, Data)

type TopDecls = [TopDecl]

--------------------------------------------------------------------------------

data Program = Program { decls        :: Decls
                       , topDecls     :: TopDecls }
  deriving (Eq, Typeable, Data)

--------------------------------------------------------------------------------
