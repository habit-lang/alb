-- Porting Dominics LargeWord module to Habit
requires miniprelude
requires ondeckprelude

data LargeWord a b = LargeWord a b
type Word64 = LargeWord (Bit 32) (Bit 32)
type Word128 = LargeWord Word64 Word64
type Word192 = LargeWord Word128 Word64
type Word256 = LargeWord Word128 Word128
type Word384 = LargeWord Word256 Word128
type Word512 = LargeWord Word256 Word256
type Word768 = LargeWord Word512 Word256
type Word1024 = LargeWord Word512 Word512
type Word2048 = LargeWord Word1024 Word1024
type Word3092 = LargeWord Word2048 Word1024
type Word4096 = LargeWord Word2048 Word2048
type Word8192 = LargeWord Word4096 Word4096

-- Helper functions
loPart :: LargeWord a b -> a
loPart (LargeWord a _) = a

hiPart :: LargeWord a b -> b
hiPart (LargeWord _ b) = b

-- Guts
instance BitSize (LargeWord a b) = BitSize a + BitSize b

opBit :: (0 < BitSize a, 0 < BitSize b, BitSize a < o, BitManip a, 0 < o) =>
         (a -> Ix (BitSize a) -> a) -> (b -> Ix (BitSize b) -> b) -> a -> b -> Ix o -> LargeWord a b
opBit opA opB a b n =
      let un = unsigned n
          aS = bitSize a
      in if relaxIx aS <= n
          then LargeWord a (opB b (modIx (un - unsigned aS)))
          else LargeWord (opA a (modIx un)) b

-- It isn't possible to have a "Bits m | m = BitSize (LargeWord a b)"
-- so we can't have meaningful ToBits or FromBits instances.

instance NumLit n (LargeWord a b) if NumLit n a, n < 2^(BitSize a), NumLit 0 b where
  fromLiteral a = LargeWord (fromLiteral a) 0

instance BitManip (LargeWord a b) if NumLit 0 a, NumLit 0 b, BitManip a, BitManip b, 0 < BitSize (LargeWord a b), 0 < BitSize a, 0 < BitSize b, BitSize a < BitSize (LargeWord a b) where
  bit n = setBit (LargeWord 0 0) n
  setBit (LargeWord a b) n = opBit setBit setBit a b n
  clearBit (LargeWord a b) n = opBit clearBit clearBit a b n
  flipBit (LargeWord a b) n = opBit flipBit flipBit a b n
  testBit (LargeWord a b) n =
      let un = unsigned n
      in if n >= relaxIx (bitSize a)
          then testBit b (modIx (un - unsigned (bitSize a)))
          else testBit a (modIx un)
  bitSize (LargeWord a b) = modIx (unsigned (bitSize a) + unsigned (bitSize b))

instance Eq (LargeWord a b) if Eq a, Eq b where
  (LargeWord a b) == (LargeWord x y) = a == x && b == y

instance Ord (LargeWord a b) if Ord a, Ord b, Eq (LargeWord a b) where
   (LargeWord a1 b1) <  (LargeWord a2 b2) = b1 < b2 || (b1 <= b2 && a1 <  a2)
   (LargeWord a1 b1) <= (LargeWord a2 b2) = b1 < b2 || (b1 <= b2 && a1 <= a2)

-- This instance is obviously wrong.  The negation and multiplication are pretty messed up.
instance Num (LargeWord a a) if Ord a, Num a, NumLit 0 a, NumLit 1 a, NumLit 1 (LargeWord a a), 1 < 2^(BitSize a), Boolean a, BitwiseShift a where
   (LargeWord a1 b1) + (LargeWord a2 b2) =
     let lo = a1 + a2
         hi = b1 + b2 + (if lo < a1 then 1 else 0)
     in LargeWord lo hi
   l1@(LargeWord a1 b1) * l2@(LargeWord a2 b2) = undefined {- TODO
     if testBit b2 0
       then l1 + (l1 `bitShiftL` 1) * (l2 `bitShiftR` 1)
       else (l1 `bitShiftL` 1) * (l2 `bitShiftR` 1)  -}
   negate (LargeWord a b) = (LargeWord (not a) (not b)) + 1

instance Boolean (LargeWord a b) if Boolean a, Boolean b where
  (.&.) (LargeWord alo ahi) (LargeWord blo bhi) =
    LargeWord lo' hi' where
      lo' = alo .&. blo
      hi' = ahi .&. bhi
  (.|.) (LargeWord alo ahi) (LargeWord blo bhi) =
    LargeWord lo' hi' where
      lo' = alo .|. blo
      hi' = ahi .|. bhi
  (.^.) (LargeWord alo ahi) (LargeWord blo bhi) =
    LargeWord lo' hi' where
      lo' = alo .^. blo
      hi' = ahi .^. bhi
  not (LargeWord a b) = LargeWord (not a) (not b)

instance Bounded (LargeWord a b) if Ord (LargeWord a b), Bounded a, Bounded b where
  minBound = LargeWord minBound minBound
  maxBound = LargeWord maxBound maxBound

instance ToUnsigned (LargeWord a b) if ToUnsigned a where
  unsigned (LargeWord lo _) = unsigned lo

asTypeOf :: a -> a -> a
asTypeOf x _ = x

halfIx :: (m + m = n, Index m, Index n) => Ix n -> Ix m
halfIx n = modIx (unsigned n)

invertIx :: (Index n) => Ix n -> Ix n
invertIx n = modIx ( unsigned (maxBound `asTypeOf` n) - unsigned n + 1)

decNIx :: (Index n) => Ix n -> Unsigned -> Ix n
decNIx n x = modIx (unsigned n - x)

instance BitwiseShift (LargeWord a a)
    if Boolean a, NumLit 0 a, BitwiseShift a, BitManip a, 0 < BitSize a, 0 < BitSize (LargeWord a a), BitSize a + BitSize a = BitSize (LargeWord a a), Index (BitSize a)  where
  bitShiftL (LargeWord a b) n
    | uN < aS + 1 =
      let n' = halfIx n
          a' = bitShiftL a n'
          bOrMask = a `bitShiftR` invertIx n'
          b' = (b `bitShiftL` n') .|. bOrMask
      in LargeWord a' b'
    | True =
       let n' = decNIx n (aS + 1)
       in bitShiftL (LargeWord 0 a) n'
    where aS = unsigned (bitSize a)
          uN = unsigned n
  bitShiftR (LargeWord a b) n
    | uN < aS + 1 =
        let n' = halfIx n
            b' = bitShiftR b n'
            aOrMask = b `bitShiftL` (modIx ((aS + 1) - uN) `asTypeOf` n')
            a' = (a `bitShiftR` n') .|. aOrMask
        in LargeWord a' b'
    | True =
        let n' = decNIx n (aS + 1)
        in bitShiftR (LargeWord b 0) n'
    where aS = unsigned (bitSize a)
          uN = unsigned n
