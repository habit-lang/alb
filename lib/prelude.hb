
-- Basic Types (4.1) --------------------------------------------

data Zero

primitive type (->) :: * -> * -> *
infixr type 5 ->

infixr 0 $
($)  :: (a -> b) -> a -> b
f $ x = f x

bitdata Bool = False [B0] | True  [B1]
  deriving (Eq, Bounded, ToBits, FromBits)  -- TODO: deriving Ord?

otherwise :: Bool
otherwise  = True

infixr 3 &&
infixr 2 ||

-- NB: although the && and || operators are defined here as regular
-- functions, making them strict in both arguments, the compiler
-- recognizes uses of these operators with two arguments and
-- replaces those calls with the corresponding if-expressions,
-- restoring the lazy/short-circuit evaluation that would be
-- expected as special cases.  As such, the following definitions
-- will only come in to effect in cases where one of these operators
-- is partially applied.

(&&), (||) :: Bool -> Bool -> Bool
x && y      = if x then y else False
x || y      = if x then True else y

data Unit    = Unit
               deriving (Eq, Ord, Bounded)

data Maybe a = Nothing | Just a
               deriving (Eq, Ord)


-- Type Level Numbers (4.2) -------------------------------------

infixl type 6 +, -
infixl type 7 *, /
infixl type 8 ^
infixl type 4 <=, <

class (+) (m :: nat) (n :: nat) (p :: nat)
  | m n -> p, m p -> n, n p -> m

class (*) (m :: nat) (n :: nat) (p :: nat)
  | m n -> p

class (-) (a :: nat) (b :: nat) = (c::nat)
   | a b -> c, b c -> a, c a -> b, b + c = a

instance x - y = z  if  y + z = x
else     x - y = z  fails

class (<=) (n :: nat) (m :: nat)
class (<) (n :: nat) (m :: nat)

instance x <= y if x < (y + 1)
else     x <= y fails

class (/) (m :: nat) (n :: nat) (p :: nat)
  | m n -> p, n p -> m

primitive class (^) (m :: nat) (n :: nat) (p :: nat)
  | m n -> p, m p -> n

class GCD (n :: nat) (m :: nat) = (p :: nat)
   | m n -> p


-- Dot Notation: the Select and Update Classes (4.3) ------------

data Proxy a = Proxy   -- parser interprets #t as (Proxy :: Proxy t)
                       -- in an expression, or (Proxy t) in a type.

class Select (r :: *) (f :: lab) = (t :: *) where
  select :: r -> #f -> t

class Update (r :: *) (f :: lab) where
  update :: r -> #f -> Select r f -> r


-- TODO: TypeInference.hs should really be the one to introduce these
primitive type BitdataCase (r::type) (f::lab)
primitive structSelect
  :: Select (ARef m s) f (ARef n t) => ARef m s -> #f -> ARef n t
primitive bitdataSelect
  :: Select (BitdataCase r c) f t => BitdataCase r c -> #f -> t
primitive bitdataUpdate
  :: Update (BitdataCase r c) f
       => BitdataCase r c -> #f -> Select (BitdataCase r c) f -> BitdataCase r c
primitive constructBitdata :: t


-- Standard Classes (4.4) ---------------------------------------

infix 4 ==, /=

class Eq t where
  (==), (/=) :: t -> t -> Bool
  x /= y      = not (x == y)   -- default definition

instance Eq (a -> b) fails

primitive private primBitdataEquals :: BitSize t n => t -> t -> Bool

infix 4  <=, <, >, >=

class Ord t | Eq t where
  compare              :: t -> t -> Ordering
  (<), (<=), (>), (>=) :: t -> t -> Bool
  min, max             :: t -> t -> t

  -- default definitions:
  x <= y  = case compare x y of GT -> False; _ -> True
  x <  y  = case compare x y of LT -> True;  _ -> False
  x >= y  = case compare x y of LT -> False; _ -> True
  x >  y  = case compare x y of GT -> True;  _ -> False

  min x y = if x <= y then x else y
  max x y = if y <= x then x else y

  compare x y | x==y      = EQ
              | x<=y      = LT
              | otherwise = GT

data Ordering = LT | EQ | GT
                deriving Eq, Ord, Bounded

class Bounded t where
  minBound, maxBound :: t

infixl 7 *
infixl 6 +, -

class Num t where
  (+), (-), (*) :: t -> t -> t
  negate        :: t -> t
  x - y = x + negate y   -- default definition


-- Division (4.6) -----------------------------------------------

infixl 7 `quot`, `rem`, `div`, `mod`

class NonZero t = t' | Num t, t -> t' where
  nonZero             :: t -> Maybe (NonZero t)
  div, mod, quot, rem :: t -> NonZero t -> t

primitive type NZ :: * -> *
primitive primNonZero :: NonZero t (NZ t) => t -> Maybe (NZ t)
primitive primDiv, primMod, primQuot, primRem
   :: NonZero t (NZ t) => t -> NZ t -> t

instance NumLit n (NZ t) if 0<n, NumLit n t where
  fromLiteral = primFromLiteralNZ

primitive primFromLiteralNZ :: (0<n, NumLit n t) => #n -> NZ t

-- instance NumLit n (NonZero t) if NumLit n t, 0 < n -- TODO: ambiguous tyvars ...

-- Numeric Literals (4.5) ---------------------------------------

class NumLit n t where
  fromLiteral :: #n -> t

instance NumLit n (Bit m) if Width m, (n < 2^m)
  where fromLiteral = primFromLiteralBit

primitive primFromLiteralBit :: NumLit n (Bit m) => #n -> Bit m

-- Index Types (4.7) --------------------------------------------

primitive type Ix :: nat -> *

class Index n | 0 < n where
  incIx, decIx :: Ix n -> Maybe (Ix n)
  maybeIx      :: Unsigned -> Maybe (Ix n)
  modIx        :: Unsigned -> Ix n
  (<=?)        :: Unsigned -> Ix n -> Maybe (Ix n)
  relaxIx      :: (Index m, n < m) => Ix n -> Ix m

instance Index (2^n) if n < WordSize where
  -- implementation can use bit-oriented operations (e.g., masking)
  incIx     = primIncIx
  decIx     = primDecIx
  maybeIx u = primMaybeIx u.bits
  modIx u   = primModIxMask u.bits
  u <=? i   = primLeqIx u.bits i
  relaxIx   = primRelaxIx
else Index n if 0 < n, n < 2^WordSize where
  -- implementation uses modulo arithmetic
  incIx     = primIncIx
  decIx     = primDecIx
  maybeIx u = primMaybeIx u.bits
  modIx u   = primModIxMod u.bits
  u <=? i   = primLeqIx u.bits i
  relaxIx   = primRelaxIx

primitive primIncIx     :: (0 < n) => Ix n -> Maybe (Ix n)
primitive primDecIx     :: (0 < n) => Ix n -> Maybe (Ix n)
primitive primMaybeIx   :: (0 < n) => Bit WordSize -> Maybe (Ix n)
primitive primModIxMod  :: (0 < n) => Bit WordSize -> Ix n
primitive primModIxMask :: (n < WordSize) => Bit WordSize -> Ix (2^n)
primitive primLeqIx     :: (0 < n) => Bit WordSize -> Ix n -> Maybe (Ix n)
primitive primRelaxIx   :: (0 < n, n < m, Index m) => Ix n -> Ix m

instance Eq (Ix n) if Index n
 where (==) = primIxEq

primitive primIxEq :: Ix n -> Ix n -> Bool

instance Ord (Ix n) if Index n
 where (<)  = primIxLt
       (<=) = primIxLe

primitive primIxLt, primIxLe :: Ix n -> Ix n -> Bool

instance Bounded (Ix n) if Index n
 where minBound = 0
       maxBound = primIxMaxBound

primitive primIxMaxBound :: Ix n

instance Num (Ix n) fails

instance NumLit i (Ix n) if Index n, i < n
  where fromLiteral = primIxFromLiteral

primitive primIxFromLiteral :: (n < m) => #n -> Ix m


-- Bit Vector Types (4.8) ---------------------------------------

primitive type Bit :: nat -> *

primitive (:#) :: (Width n, Width m, Width p, n + m = p)
                    => Bit n -> Bit m -> Bit p

instance Eq (Bit n) if Width n where
  (==) = primEqBit

primitive primEqBit :: Width n => Bit n -> Bit n -> Bool

instance Ord (Bit n) if Width n where
  compare = primCompareBit

primitive primCompareBit :: Width n => Bit n -> Bit n -> Ordering

instance Bounded (Bit n) if Width n
  where minBound = 0
        maxBound = not 0

instance Num (Bit n) if Width n
 where (+)    = primBitPlus
       (-)    = primBitMinus
       (*)    = primBitTimes
       negate = primBitNegate

primitive primBitPlus, primBitMinus, primBitTimes
   :: Width n => Bit n -> Bit n -> Bit n
primitive primBitNegate :: Width n => Bit n -> Bit n

instance NonZero (Bit n) = NZ (Bit n) if Width n
  where nonZero = primNonZero
        div     = primDiv
        mod     = primMod
        quot    = primQuot
        rem     = primRem

class Width (n :: nat) | n <= WordSize
instance Width n if n < 33
else     Width n fails


-- Bit-level Representation Classes (4.9) -----------------------

class BitSize (t :: *) = (n :: nat) | t -> n, Width n

class ToBits t where
  toBits :: t -> Bit (BitSize t)

class FromBits t | ToBits t where
  fromBits :: Bit (BitSize t) -> t
  isJunk   :: t -> Bool

primitive primToBits   :: ToBits t   => t -> Bit (BitSize t)
primitive primFromBits :: FromBits t => Bit (BitSize t) -> t
primitive primIsJunk   :: FromBits t => t -> Bool

class BitManip t | FromBits t, Index (BitSize t) where
  bit                       :: Ix (BitSize t) -> t
  setBit, clearBit, flipBit :: t -> Ix (BitSize t) -> t
  bitSize                   :: t -> Ix (BitSize t)
  testBit                   :: t -> Ix (BitSize t) -> Bool

instance BitSize (Bit n) = n if Width n

instance ToBits (Bit n) if Width n
  where toBits bits = bits

instance FromBits (Bit n) if Width n
  where fromBits bits = bits
        isJunk   bits = False

instance BitManip (Bit n) if Width n, Index n
  where bit      = primBitBit
        setBit   = primSetBitBit
        clearBit = primClearBitBit
        flipBit  = primFlipBitBit
        bitSize  = primBitSizeBit
        testBit  = primTestBitBit

primitive primBitBit        :: Ix n -> Bit n
primitive primSetBitBit     :: Bit n -> Ix n -> Bit n
primitive primClearBitBit   :: Bit n -> Ix n -> Bit n
primitive primFlipBitBit    :: Bit n -> Ix n -> Bit n
primitive primBitSizeBit    :: Bit n -> Ix n
primitive primTestBitBit    :: Bit n -> Ix n -> Bool

instance BitSize (Ix p) = IxBits p if Width (IxBits p)
else     BitSize (Ix p) = m fails

class IxBits (n::nat) = (m::nat)
instance IxBits 0 = n fails
else     IxBits 1 = 0
else     IxBits n = 1 + IxBits (n / 2)
else     IxBits n = 1 + IxBits ((n+1) / 2)

instance ToBits (Ix p) if Width (IxBits p)
  where toBits = primToBitsIx

primitive primToBitsIx :: Width (IxBits p) => Ix p -> Bit (IxBits p)

instance FromBits (Ix (2^n)) if ToBits (Ix (2^n))
  where fromBits    = primFromBitsIx
        isJunk bits = False
else FromBits (Ix m) fails

primitive primFromBitsIx :: Width n => Bit n -> Ix (2^n)

instance BitManip (Ix (2^n)) if FromBits (Ix (2^n)), Width n, Index (BitSize (Ix (2^n))) -- 2^n = p, IxBits p = n
  where bit i        = fromBits (bit i)
        setBit m i   = fromBits (setBit (toBits m) i)
        clearBit m i = fromBits (clearBit (toBits m) i)
        flipBit m i  = fromBits (flipBit (toBits m) i)
        bitSize m    = bitSize (toBits m)
        testBit m i  = testBit (toBits m) i

-- Boolean and Shift Classes (4.10) -----------------------------

infixl 7 .&.  -- bitwise and
infixl 6 .^.  -- bitwise exclusive or
infixl 5 .|.  -- bitwise inclusive or

class Boolean t where
  (.&.), (.|.), (.^.) :: t -> t -> t
  not                 :: t -> t

primitive primBoolAnd, primBoolOr, primBoolXor :: Bool -> Bool -> Bool
primitive primBoolNot :: Bool -> Bool

instance Boolean Bool where
  (.&.) = primBoolAnd
  (.|.) = primBoolOr
  (.^.) = primBoolXor
  not   = primBoolNot

instance Boolean (Bit n) if Width n where
  (.&.) = primAndBit
  (.|.) = primOrBit
  (.^.) = primXorBit
  not   = primNotBit

primitive primAndBit, primOrBit, primXorBit :: Width n => Bit n -> Bit n -> Bit n
primitive primNotBit :: Width n => Bit n -> Bit n

instance Boolean (Ix p) if Index p, 2^n = p
  where (.&.) = primAndIx
        (.|.) = primOrIx
        (.^.) = primXorIx
        not   = primNotIx

primitive primAndIx, primOrIx, primXorIx :: Ix (2^n) -> Ix (2^n) -> Ix (2^n)
primitive primNotIx :: Ix (2^n) -> Ix (2^n)

infixl 8 shiftL, shiftR  -- shift left (*2), shift right (/2)
class Shift t | Boolean t where
  shiftL, shiftR  :: t -> Unsigned -> t

instance Shift (Bit n) if Width n
  where shiftL = primShiftLBit
        shiftR = primShiftRBit

primitive primShiftLBit, primShiftRBit :: Width n => Bit n -> Unsigned -> Bit n

instance Shift (Ix p) if Index p, 2^n = p
  where shiftL = primShiftLIx
        shiftR = primShiftRIx

primitive primShiftLIx, primShiftRIx :: Ix (2^n) -> Unsigned -> Ix (2^n)


-- Words (4.11) -------------------------------------------------

type WordSize = 32

bitdata Unsigned /WordSize = Unsigned [ bits :: Bit WordSize ]
 deriving (Eq, Ord, Bounded, ToBits, FromBits, Num, Boolean, BitManip, Shift)

instance NonZero Unsigned = NZ Unsigned
  where nonZero = primNonZero
        div     = primDiv
        mod     = primMod
        quot    = primQuot
        rem     = primRem

instance NumLit n Unsigned if n < 2 ^ WordSize
  where fromLiteral n = Unsigned [ bits = fromLiteral n ]

bitdata Signed /WordSize = Signed [ bits :: Bit WordSize ]
 deriving (Eq, Ord, Bounded, ToBits, FromBits, Num, Boolean, BitManip, Shift)

class ToUnsigned t where
  unsigned :: t -> Unsigned

instance ToUnsigned Unsigned
  where unsigned u = u

instance ToUnsigned Signed
  where unsigned (Signed x) = Unsigned [ bits = x.bits ]

instance ToUnsigned (Bit n) if Width n
  where unsigned bs = Unsigned [ bits = 0 :# bs ]

instance ToUnsigned (Ix n)  if Index n
  where unsigned =  primIxToUnsigned

primitive primIxToUnsigned :: Index n => Ix n -> Unsigned

{-
class ToSigned t where
  signed :: t -> Signed
instance ToSigned Unsigned
instance ToSigned Signed
instance ToSigned (Bit n) if Width n
instance ToSigned (Ix n)  if Index n
-}


-- Monads (4.13) ------------------------------------------------

class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b

class Proc p | Monad p

primitive type M :: * -> *
primitive primReturnM :: a -> M a
instance Monad M
  where return  = primReturnM
        c >>= f = do v <- c; f v

instance Proc M
else Proc m if Monad m  -- implementation required by specializer
else Proc m fails

instance Monad Maybe where
  return        = Just
  Just x  >>= f = f x
  Nothing >>= f = Nothing


-- Memory Areas, References and Alignment (4.14) ----------------

class Alignment (l :: nat)
instance Alignment (2^n)
else     Alignment m fails

primitive type ARef :: nat -> area -> *

instance Eq (ARef l a) if Alignment l
  where (==) = primEqARef

primitive primEqARef :: Alignment l => ARef l a -> ARef l a -> Bool

instance BitSize (ARef (2^n) a) = WordSize - n

instance ToBits (ARef (2^n) a)
  where toBits = primToBitsARef

primitive primToBitsARef :: ARef (2^n) a -> Bit (BitSize (ARef (2^n) a))

primitive type APtr  :: nat -> area -> *
type Ptr = APtr MinAlign
type Ref = ARef MinAlign
type MinAlign = 1

primitive Null :: APtr l a
primitive Ref  :: ARef l a -> APtr l a

instance FromBits (ARef l a) fails

instance BitSize (APtr (2^n) a) = (WordSize - n)

class AreaOf (t :: *) = (a :: area)
instance AreaOf (ARef l a) = a
else     AreaOf (APtr l a) = a
else     AreaOf t a fails

class AlignOf (t :: *) = (l :: nat)
instance AlignOf (ARef l a) = l
else     AlignOf (APtr l a) = l
else     AlignOf t a fails

class ValIn (a :: area) = (t :: type) | a -> t
instance ValIn (Stored Unsigned) = Unsigned


class ByteSize (a :: area) = (n :: nat)

primitive type Stored :: type -> area

primitive type Array :: nat -> area -> area
primitive type Pad   :: nat -> area -> area

primitive (@@) :: Index n =>
                   ARef l (Array n a) ->
                    Ix n ->
                     ARef (GCD l (ByteSize a)) a

instance ByteSize (Array n a) = n * ByteSize a
instance ByteSize (Pad n a)   = n * ByteSize a
instance ByteSize (Stored (ARef l a)) = WordSize / 8
else     ByteSize (Stored (APtr l q)) = WordSize / 8
else     ByteSize (Stored t)          = BitSize t / 8 -- maybe only for 8, 16, and 32 ?
else     ByteSize (Stored t)          = WordSize / 8 if BitSize t <= WordSize
else     ByteSize (Stored t)          = n fails
{-
instance ByteSize (Stored t)  = BitSize t / 8
else     ByteSize (Stored t)  = n fails
-}

-- Memory Area Initialization (4.15) ----------------------------

primitive type Init :: area -> *
-- instance Pointed (Init a) fails

primitive initArray :: Index n => (Ix n -> Init a) -> Init (Array n a)
primitive initSelf  :: (Ref a -> Init a) -> Init a


-- Initialization of Stored Data (4.15.1) -----------------------

primitive initStored :: t -> Init (Stored t)   -- TODO: wrong!

instance NumLit n (Init (Stored t)) if NumLit n t where
  fromLiteral n = initStored (fromLiteral n)


-- Null Initialization (4.15.2) ---------------------------------

class NullInit a where
  nullInit :: Init a

instance NullInit (Array n a) if Index n, NullInit a where
  nullInit = initArray (\ix -> nullInit)

instance NullInit (Pad n a) fails

instance NullInit (Stored (APtr l a)) if Alignment l where
  nullInit = initStored Null
else     NullInit (Stored (Ix n)) if Index n where
  nullInit = initStored 0
else     NullInit (Stored t) if FromBits t, Width (BitSize t) where
  nullInit = initStored (fromBits 0)
else     NullInit (Stored t) fails


-- No Initialization (4.15.3) -----------------------------------

class NoInit a where
  noInit :: Init a

instance NoInit (Pad n a)   if NoInit a where
  noInit = primNoInit

instance NoInit (Array n a) if NoInit a where
  noInit = primNoInit

instance NoInit (Stored t)  if FromBits t where
  noInit = primNoInit

primitive primNoInit :: NoInit a => Init a


-- Default Initialization (4.15.4) ------------------------------

class Initable a where
  initialize :: Init a

instance Initable (Stored t) if NullInit (Stored t) where
  initialize = nullInit

instance Initable (Array n a) if Index n, Initable a where
  initialize = initArray (\ix -> initialize)

instance Initable (Pad n a) if NoInit a where
  initialize = noInit


-----------------------------------------------------------------
