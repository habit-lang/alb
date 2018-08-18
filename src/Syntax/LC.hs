{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, DeriveDataTypeable #-}
module Syntax.LC (module Syntax.LC) where

import Data.Generics
import Syntax.Common hiding (Literal(..))
import qualified Syntax.LambdaCase as C

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Type = TyCon (Kinded Id)
          | TyApp Type Type
          | TyLit Integer
          | TyLabel Id
            deriving (Eq, Ord, Show, Typeable, Data)

instance Convertable C.Type Type where
  convert (C.TyCon kid)   = TyCon kid
  convert (C.TyApp t1 t2) = TyApp (convert t1) (convert t2)
  convert (C.TyLit n)     = TyLit n
  convert (C.TyLabel i)   = TyLabel i

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
          | EDo Expr                -- do (sequence of binds)
          | EReturn Expr
  deriving (Eq, Typeable, Data)

--data Expr = WrappedExpr C.Expr
--            deriving (Eq, Typeable, Data)

data Alt  = Alt Id [Type] [Id] Expr  -- (C::t) vs -> e
  deriving (Eq, Typeable, Data)

--data Alt = WrappedAlt C.Alt
--           deriving (Eq, Typeable, Data)

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

data Defn  = Defn Id Type (Either (String, [Type]) Expr) -- Left = external
  deriving (Eq, Typeable, Data)
data Decl  = Decl Defn        -- Exprs must all be ELam ...
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

--data TopDecl = WrappedTopDecl C.TopDecl
--               deriving (Eq, Typeable, Data)

data BitdataField = LabeledField Id Type Int Int   -- name, type, width, offset in bits
                  | ConstantField Integer Int Int  -- value, width, offset
  deriving (Eq, Show, Typeable, Data)

data StructField = StructField (Maybe Id) Type Int Int -- name, type, width, offset in bytes
  deriving (Eq, Show, Typeable, Data)

type TopDecls = [TopDecl]

--------------------------------------------------------------------------------

data Entrypoints = Entrypoints {fromEntrypoints :: [(Id, Bool)]}
                   deriving (Eq, Typeable, Data)

data Program = Program { entrypoints  :: Entrypoints
                       , decls        :: Decls
                       , topDecls     :: TopDecls }
  deriving (Eq, Typeable, Data)

--------------------------------------------------------------------------------
