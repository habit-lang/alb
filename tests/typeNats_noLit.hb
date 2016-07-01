-- ### Programs using type level natural numbers:

data Bool = False | True

data Bit (n :: nat)    -- Can we say:  Bit :: nat -> *  ?

zero   :: Bit n
zero    = zero

isZero :: Bit n -> Bool
isZero  = isZero

zeroWord :: Bit 32
zeroWord  = 0

infixl type 6 +, -
infixl type 7 *, /
infix  type 4 <=, <

-- Examples of class headers using equality constraint notation:

class (a::nat) + (b::nat) = (c::nat) | a b -> c, b c -> a, c a -> b
class (a::nat) - (b::nat) = (c::nat) | a b -> c, b c -> a, c a -> b
class (a::nat) * (b::nat) = (c::nat) | a b -> c
class (a::nat) / (b::nat) = (c::nat) | a b -> c

-- Examples of (otherwise the same) headers in prefix notation:

class (+!) (a::nat) {- + -} (b::nat) {- = -} (c::nat) | a b -> c, b c -> a, c a -> b
class (-!) (a::nat) {- - -} (b::nat) {- = -} (c::nat) | a b -> c, b c -> a, c a -> b
class (*!) (a::nat) {- * -} (b::nat) {- = -} (c::nat) | a b -> c
class (/!) (a::nat) {- / -} (b::nat) {- = -} (c::nat) | a b -> c

class (a::nat) < (b::nat)
class (a::nat) <= (b::nat)

infixl #
(#) :: Bit n -> Bit m -> Bit (n + m)
(#)  = (#)

plus3a      :: Bit n -> Bit m -> Bit p -> Bit (n + m + p)
plus3a x y z = x # y # z

plus3b      :: Bit n -> Bit m -> Bit p -> Bit ((n + m) + p)
plus3b x y z = x # y # z

plus3c      :: Bit n -> Bit m -> Bit p -> Bit (n + (m + p))
plus3c x y z = x # (y # z)

class GCD (m::nat) (n::nat) = (p::nat) | m n -> p

class GCD1 (m::nat) (n::nat) (p::nat) | m n -> p


const1   = 0    :: Bit 1
const128 = 128  :: Bit 128
const4K  = 4K   :: Bit 4K
const4M  = 4M   :: Bit 4M
const16M = 16M  :: Bit 16M
const16G = 16G  :: Bit 16G
const16T = 16T  :: Bit 16T   -- that's a very big bit string :-)

values = [ 0, 1, 10, 11, 123, 1304505, 100_000, 100_000_,
           0o0, 0o1, 0o12, 0o123, 0o1304505,
           0O0, 0O1, 0O12, 0O123, 0O1304505,
           00,  01,  012,  0123,  01304505,
           0x0, 0x1, 0x12, 0x123, 0x1304505, 0xa, 0xA, 0xbac, 0xcafebabe9,
           0xCafe_Babe, 0x_a, 0xA_, 0x1_2,
           0X0, 0X1, 0X12, 0X123, 0X1304505, 0Xa, 0XA, 0Xbac, 0Xcafebabe9,
           0xAaBbCcDdEeFf00,
           0XAaBbCcDdEeFf00,
           0b0, 0b1, 0b11, 0b111, 0b1110101, 0b11, 0b000, 0b0101010101010101,
           0B0, 0B1, 0B11, 0B111, 0B1110101, 0B11, 0B000, 0B0101010101010101,
           0b1_1_1_1, 0b11_00, 0b___1, 0b1___, 0b_0_,
           0 ]

-- bad    = [ 0o8, 08, 0o10009, 0O100080,
--            0xg, 0xfffz, 0Xg, 0Xfffz,
--            0b32, 0b45, 0b00000100002, 0b_,
--            0x, 0X, 0b, 0B, 0o, 0O ]

data Unsigned
data Signed

class BitSize (t :: *) = (n :: nat) | t -> n

class ToBits t where
  toBits :: t -> Bit (BitSize t)

class ToBits t => FromBits t where
  fromBits :: Bit (BitSize t) -> t
  isJunk   :: t -> Bool

class ByteSize (a :: area) = (n :: nat) | a -> n

instance ByteSize (BE t)      = BitSize t / 8
instance ByteSize (LE t)      = BitSize t / 8
instance ByteSize (Stored t)  = BitSize t / 8
instance ByteSize (Array n t) = n * ByteSize t

-- Unfortunately, those instances are ambiguous.  For example,
-- expanding functional notation, we have:
-- 
--   instance ByteSize (BE t) = BitSize t / 8
-- =>
--   instance BE t a => ByteSize a (BitSize t / 8)
-- =>
--   instance (BE t a, Bitsize t n) => ByteSize a (n / 8)
-- =>
--   instance (BE t a, Bitsize t n, n / 8 = m) => ByteSize a m
-- 
-- Note that t appears on the left of the => symbol, but not on the right.
-- 
-- 
-- If BE is a tycon rather than a predicate, then:
-- 
--   instance ByteSize (BE t) = BitSize t / 8
-- =>
--   instance (BitSize t = n) => ByteSize (BE t) = n / 8
-- =>
--   instance (BitSize t = n, n / 8 = m) => ByteSize (BE t) = m
-- 
-- and we avoid ambiguity ...
-- 
-- Hacks for primitive area constructors:

class BE (t :: *) (a :: area) | t -> a
class LE (t :: *) (a :: area) | t -> a
class Stored (t :: *) (a :: area) | t -> a
class Array (n :: nat) (t :: area) (a :: area) | n t -> a

