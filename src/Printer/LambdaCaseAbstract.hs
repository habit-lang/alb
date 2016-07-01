{-# LANGUAGE FlexibleInstances #-}

module Printer.LambdaCaseAbstract(Abstract, abstract) where
{-

This module provides a function:  abstract :: Program -> Abstract Program,
together with a pretty printer for Abstract Program values.  The abstracted
form of a LambdaCase program is the same as the original except that all of
the distinct type constructor constants, primitive functions, and value
constructors are abstracted out and named.  (For type constructors, we use
the same names as in the original program because there are no local type
definitions, and hence no possibility of clashing variable names.)

Usage: ppr (abstract program)

This code was created in the hopes of making it easier to digest the output
that is produced by the LambdaCase pretty printer.  If this abstracted form
of LambdaCase is considered useful for other purposes, for example as an
input to compilation, then we should consider relocating parts of the code
in this file to places outside the Printer.* portion of the hierarchy.

-}

import Syntax.Common hiding (Literal(..))
import Syntax.LambdaCase
import Printer.Common
import Printer.LambdaCase
import Control.Monad(liftM, liftM2, liftM3)

--------------------------------------------------------------------------------

type Tycons = [Kinded Id]
type Prims  = [(Id, Id, [Type])]

-- The following function could be generalized to type Collect p => p -> Abstract p,
-- but then we'd probably have to export the type class to make it useful.

abstract  :: Program -> Abstract Program
abstract p = runM (collect p)

data Abstract a = Abstract { tycons :: Tycons, prims :: Prims, val :: a } 

-- Right now, the only thing that a client of this module can do with a
-- value of type (Abstract a) is to pretty print it via the following
-- instance:

instance Printable a => Printable (Abstract a) where
  ppr d = text "Type constructors"
     <$$> indent 4 (vcat [ ppr tc | tc <- tycons d ])
     <>   linebreak
     <$$> text "Primitive functions"
     <$$> indent 4 (vcat [ text j <+> text " = " <+> ppr (EPrim i ts)
                             | (j, i, ts) <- prims d ])
     <>   linebreak
     <$$> text "--------------"
     <$$> indent 4 (ppr (val d))

--------------------------------------------------------------------------------
-- A monad for collecting primitive type and value references:

newtype M a = M (Abstract Int -> (Int, Abstract a))

rotate    :: a -> Abstract b -> (b, Abstract a)
rotate n d = (val d, d{val = n})

instance Monad M where
  return    = M . rotate
  M c >>= f = M (\d -> let (n', d') = c d
                           (x, d'') = rotate n' d'
                           M f'     = f x
                        in f' d'')

runM            :: M a -> Abstract a
runM (M c)       = snd (c (Abstract [] [] 0))

replaceTycon    :: Kinded Id -> M Type
replaceTycon kid = M $ \d ->
                   let ts                 = tycons d
                       d' | kid `elem` ts = d
                          | otherwise     = d{tycons = kid : ts}
                       Kinded id k        = kid
                    in rotate (TyVar id) d'

replacePrim     :: Id -> [Type] -> M Expr
replacePrim i ts = M $ \d ->
                   case [ j | (j, i', ts') <- prims d, i==i', ts==ts' ] of
                     (j:_) -> rotate (EVar j) d
                     []    -> let n = val d + 1
                                  j = "prim" ++ show n
                                  p = (j, i, ts)
                              in (n, d{prims = p:prims d, val=EVar j})
 
--------------------------------------------------------------------------------
-- Traverse an AST collecting references to primitives type constructors and
-- primitive values/functions:

class Collect a where
  collect :: a -> M a

instance Collect a => Collect [a] where
  collect = mapM collect

instance Collect a => Collect (Maybe a) where
  collect Nothing  = return Nothing
  collect (Just a) = liftM Just (collect a)

instance Collect Type where
  collect (TyCon kid) = replaceTycon kid
  collect (TyApp f x) = liftM2 TyApp (collect f) (collect x)
  collect t           = return t

instance Collect Expr where
  collect (EPrim i ts)    = collect ts >>= replacePrim i
  collect (ECon i ts)     = collect ts >>= replacePrim i
  collect (ELam i t e)    = liftM2 (ELam i) (collect t)  (collect e)
  collect (ELet ds e)     = liftM2 ELet (collect ds) (collect e)
  collect (ECase e as)    = liftM2 ECase (collect e) (collect as)
  collect (EApp f x)      = liftM2 EApp (collect f) (collect x)
  collect (EFatbar l r)   = liftM2 EApp (collect l) (collect r)
  collect (EBind i t p q) = liftM3 (EBind i) (collect t) (collect p) (collect q)
  collect other           = return other   -- EVar, EBits, ENat

instance Collect Alt where
  collect (Alt i ts is e) = liftM3 (Alt i) (collect ts) (return is) (collect e)

instance Collect Decls where
  collect (Decls ds) = liftM Decls (collect ds)

instance Collect a => Collect (Id, a) where
  collect (i, x) = liftM (\x -> (i, x)) (collect x)

instance (Collect a, Collect b) => Collect (Id, a, b) where
  collect (i, x, y) = liftM2 (\x y -> (i, x, y)) (collect x) (collect y)

instance Collect TopDecl where
  collect (Datatype i is ctors)  = liftM (Datatype i is) (collect ctors)
  collect (Bitdatatype i n ps)   = liftM (Bitdatatype i n) (collect ps)
  collect (Struct i n rs)        = liftM (Struct i n) (collect rs)
  collect (Area nis t)           = liftM2 Area (collect nis) (collect t)

instance Collect BitdataField where
  collect (LabeledField i t d) = liftM2 (LabeledField i) (collect t) (collect d)
  collect other                = return other -- ConstantField

instance Collect StructRegion where
  collect (StructRegion msf t) = liftM2 StructRegion (collect msf) (collect t)

instance Collect StructField where
  collect (StructField i me) = liftM (StructField i) (collect me)

instance Collect Program where
  collect (Program ds ts) = liftM2 Program (collect ds) (collect ts)

--------------------------------------------------------------------------------
