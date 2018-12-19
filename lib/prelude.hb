-- Partial data types: ------------------------------------------

class (@) (t :: k' -> k) (u :: k')

-- Basic types: -------------------------------------------------
data Zero

primitive type (->) :: * -> * -> *
infixr type 5 ->

type WordSize = 32

data Maybe a = Nothing | Just a
               -- deriving ...

bitdata Bool = False [ B0 ] | True [ B1 ]
               -- deriving ...

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
               -- deriving ...

-- Arithmetic, etc. ---------------------------------------------
infixl type 6 +, -
infixl type 7 *, /
infixl type 8 ^
infixl type 4 <=, <, ==

class (==) (a :: k) (b :: k) | a -> b, b -> a
instance a == a

class (+) (a :: nat) (b :: nat) = (c::nat)
   | a b -> c, b c -> a, c a -> b

class (-) (a :: nat) (b :: nat) = (c::nat)
   | a b -> c, b c -> a, c a -> b

instance x - y = z  if  y + z = x
else     x - y = z  fails

class (*) (a :: nat) (b :: nat) = (c::nat)
   | a b -> c

class (/) (a :: nat) (b :: nat) = (c::nat)
   | a b -> c, b c -> a

class Div (a :: nat) (b :: nat)

class (^) (a :: nat) (b :: nat) = (c :: nat)
   | a b -> c, a c -> b

class GCD (n :: nat) (m :: nat) = (p :: nat)

class LCM (n :: nat) (m :: nat) = (p :: nat)

class (<=) (n :: nat) (m :: nat)
class (<) (n :: nat) (m :: nat)

instance x <= y if x < (y + 1)
else     x <= y fails

-- Labels and dot notation: -------------------------------------
data Proxy t = Proxy


class Select (r :: *) (f :: lab) = (t :: *)
  where select :: r -> #f -> t

class Update (r :: *) (f :: lab)
  where update :: r -> #f -> Select r f -> r

-- Standard Classes: --------------------------------------------

infix 4 ==, /=

class Eq t where
  (==), (/=) :: t -> t -> Bool
  x /= y      = not (x == y)   -- default definition

instance Eq (a -> b) fails

instance Eq Bool where
  False == False = True
  True  == True  = True
  _     == _     = False

instance Eq (Maybe a) if Eq a where
  Nothing == Nothing = True
  Just x == Just y = x == y
  _ == _ = False
  Nothing /= Nothing = False
  Just x /= Just y = x /= y
  _ /= _ = True

----------------

infix 4 <=, <, >, >=

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
              | True      = GT

data Ordering = LT | EQ | GT
                deriving Eq, Ord, Bounded

class Bounded t | Ord t where
  minBound, maxBound :: t

----------------

infixl 7 *
infixr 6 +, -

class Num t where
  (+), (-), (*) :: t -> t -> t
  negate        :: t -> t

  x - y = x + negate y   -- default definition

-- Numeric Literals: --------------------------------------------
class NumLit (n :: nat) t where
  fromLiteral :: #n -> t

instance NumLit n (Bit m) if n < 2^m
  where fromLiteral = primBitFromLiteral
primitive primBitFromLiteral :: #n -> Bit m

-- Bit vectors: -------------------------------------------------

class Width (n :: nat)
instance Width n if n <= 32
else     Width n fails

primitive type Bit :: nat -> *

primitive (:#) :: (Width n, Width m, Width p, n + m = p)
                    => Bit n -> Bit m -> Bit p

class BitSize (t :: *) = (n :: nat) | t -> n
instance BitSize (Bit n) = n

instance Eq (Bit n) if Width n where   -- comment this requirement out at your peril ...
  (==) = primBitEq

primitive primBitEq :: Bit n -> Bit n -> Bool

instance Ord (Bit n) if Width n where   -- comment this requirement out at your peril ...
  (<) = primBitLt
  (<=) = primBitLe

primitive primBitLt :: Bit n -> Bit n -> Bool
primitive primBitLe :: Bit n -> Bit n -> Bool

instance Num (Bit n)         if Width n
 where (+)    = primBitPlus
       (-)    = primBitMinus
       (*)    = primBitTimes
       negate = primBitNegate

primitive primBitPlus, primBitMinus, primBitTimes
   :: Bit n -> Bit n -> Bit n
primitive primBitNegate :: Bit n -> Bit n

instance Num Unsigned where
  x + y    = Unsigned [bits = x.bits + y.bits]
  x - y    = Unsigned [bits = x.bits - y.bits]
  x * y    = Unsigned [bits = x.bits * y.bits]
  negate x = Unsigned [bits = negate x.bits]

-- Bit-level representation: ------------------------------------

class ToBits t where
  toBits :: t -> Bit (BitSize t)

instance ToBits (Bit n) where
  toBits v = v

instance ToBits Bool where  -- I assume there are more efficient ways to do this :-)
  toBits True  = B1
  toBits False = B0

class FromBits t | ToBits t where
  fromBits :: Bit (BitSize t) -> t
  isJunk   :: t -> Bool

instance FromBits (Bit n) where
  fromBits v = v
  isJunk   v = False

instance FromBits Bool where -- this also looks like a candidate for a primitive ...
  fromBits b = if b==B0 then False else True
  isJunk b   = False

instance ToBits Unsigned
   where toBits u = u.bits

instance FromBits Unsigned
   where fromBits bs = Unsigned [bits = bs]
         isJunk bs   = False

instance ToBits  (Ix p)      if Index p, 2^n = p  -- OVERLY RESTRICTIVE
 where toBits = primIxToBit

instance FromBits (Ix p)     if Index p, 2^n = p
 where fromBits = primIxFromBits
       isJunk _ = False

primitive primIxFromBits :: Bit m -> Ix n   -- where n = 2^m

class BitManip t {- | Index (BitSize t) -} where
  bit                       :: Ix (BitSize t) -> t
  setBit, clearBit, flipBit :: t -> Ix (BitSize t) -> t
  bitSize                   :: t -> Ix (BitSize t)
  testBit                   :: t -> Ix (BitSize t) -> Bool

instance BitManip (Bit n) if Index n
 where bit      = primBitBit
       setBit   = primBitSetBit
       clearBit = primBitClearBit
       flipBit  = primBitFlipBit
       bitSize  = primBitBitSize
       testBit  = primBitTestBit

primitive primBitBit      :: Ix n  -> Bit n
primitive primBitSetBit   :: Bit n -> Ix n -> Bit n
primitive primBitClearBit :: Bit n -> Ix n -> Bit n
primitive primBitFlipBit  :: Bit n -> Ix n -> Bit n
primitive primBitBitSize  :: Bit n -> Ix n
primitive primBitTestBit  :: Bit n -> Ix n -> Bool

instance BitManip Unsigned
    where bit n         = Unsigned [bits = bit n]
          setBit u n    = Unsigned [bits = setBit u.bits n]
          clearBit u n  = Unsigned [bits = clearBit u.bits n]
          flipBit u n   = Unsigned [bits = flipBit u.bits n]
          bitSize u     = bitSize u.bits
          testBit u n   = testBit u.bits n




-- Boolean and Shift Classes: -----------------------------------

infixl 7 .&.     -- bitwise and
infixl 6 .^.     -- bitwise exclusive or
infixl 5 .|.     -- bitwise inclusive or

class Boolean t where
  (.&.), (.|.), (.^.) :: t -> t -> t
  not                 :: t -> t

instance Boolean Bool where
  x .&. y    = fromBits (toBits x .&. toBits y)
  x .|. y    = fromBits (toBits x .|. toBits y)
  x .^. y    = fromBits (toBits x .^. toBits y)
  not x      = fromBits (not (toBits x))

pmNot False = True  -- pattern match implementation, for comparison
pmNot True  = False

instance Boolean (Bit n) where
  (.&.)     = primBitAnd
  (.|.)     = primBitOr
  (.^.)     = primBitXor
  not       = primBitNot

primitive primBitAnd,
          primBitOr,
          primBitXor :: Bit n -> Bit n -> Bit n
primitive primBitNot :: Bit n -> Bit n

instance Boolean Unsigned
    where x .&. y = Unsigned [bits = x.bits .&. y.bits]
          x .|. y = Unsigned [bits = x.bits .|. y.bits]
          x .^. y = Unsigned [bits = x.bits .^. y.bits]
          not x   = Unsigned [bits = not x.bits]

instance Boolean (Ix p)  if Index p, 2^n = p
 where x .&. y = fromBits (toBits x .&. toBits y)
       x .|. y = fromBits (toBits x .|. toBits y)
       x .^. y = fromBits (toBits x .^. toBits y)
       not x   = fromBits (not (toBits x))

infixl 8 shiftL, shiftR

class Shift a where
   shiftL :: a -> Ix (BitSize a) -> a
   shiftR :: a -> Ix (BitSize a) -> a

instance Shift (Bit n) if Width n
 where shiftL x y = primBitShiftL x y
       shiftR x y = primBitShiftRu x y

instance Shift Unsigned
    where shiftL x y = Unsigned [bits = shiftL x.bits y]
          shiftR x y = Unsigned [bits = shiftR x.bits y]

primitive primBitShiftL :: Bit n -> Ix n -> Bit n
primitive primBitShiftRu :: Bit n -> Ix n -> Bit n

instance BitSize (Ix p) = n if Index p, 2^n = p

instance Shift (Ix p) if Index p, 2^n = p
 where shiftL x y = primIxShiftL x y
       shiftR x y = primIxShiftR x y

primitive primIxShiftL :: Ix n -> Ix m -> Ix n
primitive primIxShiftR :: Ix n -> Ix m -> Ix n

-- References and memory areas: ---------------------------------

-- primitive type ARef  :: nat -> area -> *
-- type Ref = ARef MinAlign

primitive type Ref :: area -> *

-- instance ByteSize (Stored (ARef n a)) = 4
instance ByteSize (Stored (Ref a)) = 4

-- primitive type APtr  :: nat -> area -> *
primitive type Ptr :: area -> *

primitive Null :: Ptr a
primitive Ref  :: Ref a -> Ptr a

-- instance ByteSize (Stored (APtr n a)) = 4
instance ByteSize (Stored (Ptr a)) = 4

type MinAlign = 1

class AreaOf (t :: *) = (a :: area)
instance AreaOf (Ref a) = a
else     AreaOf (Ptr a) = a
else     AreaOf a n fails -- why?

-- instance AreaOf (ARef l a) = a
-- else     AreaOf (APtr l a) = a
-- else     AreaOf t a fails

class AlignOf (t :: *) = (l :: nat)
instance AlignOf (Ref a) = Alignment a
else     AlignOf (Ptr a) = Alignment a
else     AlignOf t a fails -- again, why?

-- instance AlignOf (ARef l a) = l
-- else     AlignOf (APtr l a) = l
-- else     AlignOf t a fails

class ByteSize (a :: area) = (n :: nat)
class Alignment (a :: area) = (n :: nat)

-- Good enough in general?
instance Alignment (Stored t) = ByteSize (Stored t)

class ValIn (a :: area) = (t :: type) | a -> t
instance ValIn (Stored Unsigned) = Unsigned

-- Arrays and padding: ------------------------------------------

primitive type Array :: nat -> area -> area
primitive type Pad   :: nat -> area -> area

instance ByteSize (Array n a)  = n * ByteSize a
instance ByteSize (Pad n a)    = n * ByteSize a
instance Alignment (Pad n a)   = 1
instance Alignment (Array n a) = Alignment a

-- Indexes: -----------------------------------------------------

primitive type Ix :: nat -> *

instance Eq (Ix n)         if Index n
 where (==) = primIxEq

primitive primIxEq :: Ix n -> Ix n -> Bool

instance Ord (Ix n)        if Index n
 where (<)  = primIxLt
       (<=) = primIxLe

primitive primIxLt, primIxLe :: Ix n -> Ix n -> Bool

instance Bounded (Ix n)    if Index n
 where minBound = 0
       maxBound = primIxMaxBound

primitive primIxMaxBound :: Ix n

instance Num (Ix n) fails

instance NumLit i (Ix n) if Index n, i < n
  where fromLiteral = primIxFromLiteral

primitive primIxFromLiteral :: #n -> Ix m

class Index n | 0 < n where
  incIx, decIx :: Ix n -> Maybe (Ix n)
  maybeIx      :: Unsigned -> Maybe (Ix n)
  modIx        :: Unsigned -> Ix n
  (<=?)        :: Unsigned -> Ix n -> Maybe (Ix n)
  relaxIx      :: (Index m, n < m) => Ix n -> Ix m

instance Index n if 0 < n   -- TODO: needs more
  where incIx     = primIncIx
        decIx     = primDecIx
        maybeIx x = primMaybeIx x.bits
        modIx x   = primModIx x.bits
        x <=? y   = primLeqIx x.bits y
        relaxIx   = primRelaxIx

primitive primIncIx   :: Ix n -> Maybe (Ix n)
primitive primDecIx   :: Ix n -> Maybe (Ix n)
primitive primMaybeIx :: Bit w -> Maybe (Ix n)
primitive primModIx   :: Bit w -> Ix n
primitive primLeqIx   :: Bit w -> Ix n -> Maybe (Ix n)
primitive primRelaxIx :: Ix n -> Ix m

-- Stored Data: -------------------------------------------------


{-

There's a problem with treating Stored etc. as type synonyms: we can't define
instances for them, as they might overlap with anything else.  I think the
original intention was to capture the additional ToBits and BitSize constaints.
If so, this is actually an embryonic partial data type, and should use that
mechanism instead.

When it exists, that is.


class BE (t :: *) = (a :: area) | t -> a
instance BE t = _ if ToBits t, BitSize t = 8 * n

class LE (t :: *) = (a :: area) | t -> a
instance LE t = _ if ToBits t, BitSize t = 8 * n


class Stored (t :: *) = (a :: area) | t -> a
instance Stored Unsigned = _

instance Stored (Ix m) = _     -- BOGUS!
-}

primitive type Stored, BE, LE :: type -> area

class Storable t where
  initStored :: t -> Init (Stored t)

{-

Taking the same approach to primInitStored... as we take to writeRef: that is, just assert that
anything can be  written and let the back end figure out what's what.  Conceivably, this function
could be hidden in some way that would prevent direct calls to it, which might offer some greater
degree of assurance.

-}

instance Storable Unsigned where
  initStored = primInitStored

instance Storable (Ix n) if n <= 2^32
  where initStored = primInitStored
{-
else     Storable (Ix n) if n <= 2^16
  where initStored = primInitStoredIxShort
else     Storable (Ix n) if n <= 2^32
  where initStored = primInitStoredIxWord
else     Storable (Ix n) fails
-}

instance ByteSize (Stored (Ix n)) = 1 if n <= 256
else     ByteSize (Stored (Ix n)) = 2 if n <= 2^16
else     ByteSize (Stored (Ix n)) = 4 if n <= 2^32
else     ByteSize (Stored (Ix n)) = n fails

instance Storable (Bit n) where
  initStored = primInitStored

instance ByteSize (Stored (Bit n)) = 1 if n <= 8
else     ByteSize (Stored (Bit n)) = 2 if n <= 16
else     ByteSize (Stored (Bit n)) = 4 if n <= 32
else     ByteSize (Stored (Bit n)) = n fails

primitive (@)      :: Ref (Array n a) -> Ix n -> Ref a


-- Initialization: ----------------------------------------------

primitive type Init      :: area -> *

primitive primInitArray  :: (Ix n -> Init a) -> Init (Array n a)
initArray = primInitArray
primitive initSelf       :: (Ref a -> Init a) -> Init a

primitive primInitStored :: t -> Init (Stored t)
primitive primInitLE     :: t -> Init (LE t)
primitive primInitBE     :: t -> Init (BE t)

instance NumLit n (Init (Stored t)) if NumLit n t, Storable t where
  fromLiteral n = initStored (fromLiteral n)
instance NumLit n (Init (BE t)) if NumLit n t where
  fromLiteral n = primInitBE (fromLiteral n)
instance NumLit n (Init (LE t)) if NumLit n t where
  fromLiteral n = primInitLE (fromLiteral n)

-- Null initialization: -----------------------------------------

class NullInit a
  where nullInit :: Init a

instance NullInit (Array n a) if NullInit a, Index n where
  nullInit = initArray (const nullInit)

-- Here is the previous prelude NullInit instance for arrays.  I've commented it
-- out because it seems to introduce a silly extra primitive (primInitZeroArray)
-- that could equally well be handled in the existing primInitArray primitive.
-- (This doesn't even make sense if we were expanding initArray... surely we
-- could still handle a 0-ary loop without needing to add primitives.  instance
-- NullInit (Array n a) if 0<n, NullInit a where nullInit = initArray (\i ->
-- nullInit) else NullInit (Array 0 a) where nullInit = primInitZeroArray

instance NullInit (Pad n a) fails

-- The language report calls for the following instance.  It does _not_,
-- however, call for an instance of Storable (Aptr l a), so the call to
-- initStored fails.  Leaving this for now ...
--
-- instance NullInit (Stored (APtr l a)) where
--    nullInit = initStored Null

instance NullInit (Stored (Ix n)) if Storable (Ix n), 0 < n where
   nullInit = initStored 0
instance NullInit (Stored Unsigned) where
   nullInit = initStored 0

-- Non-initalization: -------------------------------------------

class NoInit a
  where noInit :: Init a
instance NoInit (Pad n a)   if NoInit a
  where noInit  = primNoInitPad
instance NoInit (Array n a) if NoInit a
  where noInit  = primNoInitArray
instance NoInit (Stored t) if FromBits t
  where noInit  = primNoInitStored
instance NoInit (BE t) if FromBits t
  where noInit  = primNoInitBE
instance NoInit (LE t) if FromBits t
  where noInit  = primNoInitLE


-- The language report omits these primitives, instead just defining the
-- instances above without methods.  That seems like a mistake to me.

-- The previous versions of these primitives had class constraints.  My
-- intuition is that we should never have class constraints on primitives---what
-- would it mean to pass evidence to a primitive operation?

primitive primNoInitPad    :: Init (Pad n a)    -- I think these are safe, but
primitive primNoInitArray  :: Init (Array n a)  -- should they be exposed?
primitive primNoInitStored :: Init (Stored a)
primitive primNoInitBE     :: Init (BE a)
primitive primNoInitLE     :: Init (LE a)


-- Default initialization: --------------------------------------

class Initable a
  where initialize :: Init a

instance Initable (Array n a) if Initable a, Index n
  where initialize = initArray (\i -> initialize)

instance Initable (Pad n a) if NoInit a
  where initialize = noInit

-- Numerics: ----------------------------------------------------
bitdata Unsigned = Unsigned [ bits :: Bit 32 ]

instance ByteSize (Stored Unsigned) = 4
instance Initable (Stored Unsigned)
  where initialize = 0

instance Eq Unsigned
  where x == y = x.bits == y.bits

instance NumLit i Unsigned if i < 2^WordSize
  where fromLiteral n = Unsigned [ bits = fromLiteral n ]

class ToUnsigned t where
  unsigned :: t -> Unsigned

instance ToUnsigned Unsigned
 where unsigned x = x
instance ToUnsigned Signed
 where unsigned x = Unsigned [ bits = x.bits ]

instance ToUnsigned (Bit n) if n < 33 -- not Width n
 where unsigned x = Unsigned [ bits = 0 :# x ]

instance ToUnsigned (Ix n)  if Index n
 where unsigned x = Unsigned [ bits = primIxToBit x ]

instance Ord Unsigned where
  x <  y = x.bits <  y.bits
  x <= y = x.bits <= y.bits
  x >  y = x.bits >  y.bits
  x >= y = x.bits >= y.bits
  max x y = Unsigned [bits = max x.bits y.bits]
  min x y = Unsigned [bits = min x.bits y.bits]

primitive primIxToBit :: Ix n -> Bit m

-----------------------------------------------------------------

bitdata Signed   = Signed [ bits :: Bit 32 ]

instance NumLit i Signed   if i < 2^(WordSize - 1)
 where fromLiteral n = Signed [ bits = fromLiteral n ]

instance Eq Signed
  where x == y = x.bits == y.bits

primitive primBitSGt, primBitSGe, primBitSLt, primBitSLe :: Bit w -> Bit w -> Bool

instance Ord Signed
  where x <  y = primBitSLt x.bits y.bits
        x <= y = primBitSLe x.bits y.bits
        x >  y = primBitSGt x.bits y.bits
        x >= y = primBitSGe x.bits y.bits

instance Num Signed
  where x + y    = Signed [bits = x.bits + y.bits]
        x - y    = Signed [bits = x.bits - y.bits]
        x * y    = Signed [bits = x.bits * y.bits]
        negate x = Signed [bits = negate x.bits]


class ToSigned t where
  signed :: t -> Signed

instance ToSigned Unsigned
 where signed x = Signed [ bits = x.bits ]
instance ToSigned Signed
 where signed x = x
--
-- Unclear on what the right behavior here should be---do we interpret signed
-- (111) as being an operation on the unsigned 3-bit value 7 or the signed 3-bit
-- value -1?  Leaving unimplemented for the time being.
--
-- instance ToSigned (Bit n) if Width n
--  where signed x = Signed [ bits = primBitSignExtend x ]
instance ToSigned (Ix n)  if Index n, n < 2^(WordSize - 1)
 where signed x = Signed [ bits = primIxToBit x ]



-- Monads and Procedures: ---------------------------------------
class Monad m
  where return :: a -> m a
        (>>=)  :: m a -> (a -> m b) -> m b

primitive type M :: * -> *     -- The "M"achine monad

primitive primReturnM :: a -> M a

instance Monad M
  where return  = primReturnM
        c >>= f = do v <- c; f v

class Proc p | Monad p  -- super class required!
instance Proc M
else     Proc m if Monad m
else     Proc m fails

instance Select (p r) f = p (Select r f) if Proc p
  where select c f = do r <- c; return (select r f)
else     Select (m r) f = m (Select r f) if Monad m
  where select c f = c >>= (\r -> return (select r f))

-- more to come ...

-- TODO: TypeInference.hs should really be the one to introduce these
primitive type BitdataCase :: * -> lab -> *
primitive structSelect
  :: Ref s -> #f -> Ref t
primitive bitdataSelect
  :: BitdataCase r c -> #f -> t
primitive bitdataUpdate
  :: BitdataCase r c -> #f -> t -> BitdataCase r c
primitive constructBitdata :: t

const :: a -> b -> a
const x y = x

id :: a -> a
id x = x

otherwise :: Bool
otherwise = True

primitive undefined :: a
