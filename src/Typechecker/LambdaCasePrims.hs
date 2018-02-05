{-# LANGUAGE OverloadedStrings #-}
module Typechecker.LambdaCasePrims where

import Prelude hiding (init)
import Syntax.Common
import Syntax.LambdaCase

-- Define types of primitives, and define "built-in" datatypes.
-- Start with handy machinery for building LambdaCase types.

word_size  :: Integer
word_size = 32

-- Type level primitives: -----------------------------------------------

tapply1   :: Type -> Type -> Type
tapply1    = TyApp

tapply2   :: Type -> Type -> Type -> Type
tapply2 c  = TyApp . tapply1 c

tapplyn   :: Type -> [Type] -> Type
tapplyn    = foldl TyApp

-------------------------------------------------------------------------
-- BUILT-IN PRIMITIVE TYPES
-------------------------------------------------------------------------
-- Function types (built-in):

fun       :: Type -> Type -> Type
fun        = tapply2 funCon
 where funCon = TyCon (Kinded "->" (KStar `KFun` (KStar `KFun` KStar)))

-------------------------------------------------------------------------
-- Natural number types (built-in):

natT       :: Integer -> Type
natT n      = tapply1 natCon (TyLit n)
 where natCon = TyCon (Kinded "Nat" (KNat `KFun` KStar))

-------------------------------------------------------------------------
-- Reference types (built-in):

ref        :: Type -> Type
ref         = tapply2 refCon (TyLit 1)
  where refCon = TyCon (Kinded "ARef" (KNat `KFun` (KArea `KFun` KStar)))

-------------------------------------------------------------------------
-- Initializers (built-in):

--init       :: Type -> Type
--init        = tapply1 initCon
-- where initCon = TyCon (Kinded "Init" (KArea `KFun` KStar))

-------------------------------------------------------------------------
-- The unsigned type (built-in): NOT ANY MORE

-- unsigned  :: Type
-- unsigned   = TyCon (Kinded "Unsigned" KStar)

-------------------------------------------------------------------------
-- Index types (built-in):

ix         :: Type -> Type
ix          = tapply1 ixCon
 where ixCon = TyCon (Kinded "Ix" (KNat `KFun` KStar))

-------------------------------------------------------------------------
-- Array types (built-in):

array      :: Type -> Type -> Type
array       = tapply2 arrayCon
 where arrayCon = TyCon (Kinded "Array" (KNat `KFun` (KArea `KFun` KArea)))

-------------------------------------------------------------------------
-- Base Monad (built-in):

monadM    :: Type -> Type
monadM    = tapply1 monadCon
 where monadCon = TyCon (Kinded "M" (KStar `KFun` KStar))

-------------------------------------------------------------------------
-- Initialization Monad (built-in):

monadI    :: Type -> Type
monadI    = tapply1 monadCon
 where monadCon = TyCon (Kinded "I" (KStar `KFun` KStar))

-------------------------------------------------------------------------
-- Stored areas (built in):

stored :: Type -> Type
stored = tapply1 storedCon
 where storedCon = TyCon (Kinded "Stored" (KStar `KFun` KArea))

-------------------------------------------------------------------------
-- Bits (???):

bits :: Type -> Type
bits = tapply1 bitsCon
 where bitsCon = TyCon (Kinded "Bit" (KNat `KFun` KStar))

-------------------------------------------------------------------------
-- BUILT-IN DATATYPES (with definitions)
-- These datatypes should be declared in the normal way (appropriately
-- instantiated in the case of Maybe) in any LambdaCase program in which
-- they are used.  But because they are mentioned in the signatures of
-- primitives, the declarations *must* match those specified below.
-------------------------------------------------------------------------
-- The unit type:

unit       :: Type
unit        = TyCon (Kinded "Unit" KStar)

-- declaration should always match:
-- unitDecl  = Datatype "Unit" [] [("Unit", [])]

-------------------------------------------------------------------------
-- Maybe type:

maybeT :: Type -> Type
maybeT = tapply1 maybeCon
    where maybeCon = TyCon (Kinded "Maybe" (KStar `KFun` KStar))

-- declarations should always match
-- maybeDecl t = Datatype "Maybe" [t]
--               [("Nothing", []),
--                ("Just", [t])]

------------------------------------------------------------------------
-- Booleans:

bool :: Type
bool = TyCon (Kinded "Bool" KStar)

-- declaration should always match
-- boolDecl  = Bitdatatype "Bool" 1 [ ("False", [ConstantField 0 1]),
--                                    ("True",  [ConstantField 1 1]) ]


------------------------------------------------------------------------
-- Bitdata aids:

bitdatacase :: Id -> Id -> Type
bitdatacase tcon dcon = bitdatacase'
                        (TyCon (Kinded tcon KStar))
                        (TyLabel dcon)

bitdatacase' :: Type -> Type -> Type
bitdatacase' = tapply2 (TyCon (Kinded "BitdataCase" (KFun KStar (KFun KLabel KStar))))
