--  A temporary place for things that might belong in the prelude

requires miniprelude

instance NoInit (Stored Unsigned)
  where noInit = primNoInitStored

odd :: (BitManip t, BitSize t n, 0 < n) => t -> Bool
odd x = testBit x 0

even :: (BitManip t, BitSize t n, 0 < n) => t -> Bool
even x = not (odd x)

instance ToUnsigned Bool where
  unsigned True  = 1
  unsigned False = 0

-- This is useless until we support top-level non-functional decls
instance Bounded Unsigned where
  minBound = 0
  maxBound = not minBound

-- Haskell's (^) implementation, a direct rip-off
-- see the Glasgow Haskell Compiler License (BSD style)
(^) :: Unsigned -> Unsigned -> Unsigned
x0 ^ y0 | y0 < 0    = 0 -- error "Negative exponent"
        | y0 == 0   = 1
        | True = f x0 y0
    where quot = div
          -- f : x0 ^ y0 = x ^ y
          f x y | even y    = f (x * x) (y `quot` 2)
                | y == 1    = x
                | True = g (x * x) ((y - 1) `quot` 2) x
          -- g : x0 ^ y0 = (x ^ y) * z
          g x y z | even y = g (x * x) (y `quot` 2) z
                  | y == 1 = x * z
                  | True = g (x * x) ((y - 1) `quot` 2) (x * z)

-- Some temporary functions while we lack NonZero.
div :: Unsigned -> Unsigned -> Unsigned
div x y
  | x < y = 0
  | True  = f 0 y
 where
   f :: Unsigned -> Unsigned -> Unsigned
   f n k = if x < 2 * k || k >= maxK then bit (modIx n) + div (x - k) y
                                   else f (n + 1) (2 * k)
     where maxK :: Unsigned
           maxK = bit (bitSize k)

rem :: Unsigned -> Unsigned -> Unsigned
rem x y = x - (x `div` y) * y

swapEndian :: (FromBits x, ToBits x, BitSize x 32) => x -> x
swapEndian x =
 let a = toBits x
     b0 = (a .&. 0xFF) `bitShiftL` 24
     b1 = (a .&. 0xFF00) `bitShiftL` 8
     b2 = (a .&. 0xFF0000) `bitShiftR` 8
     b3 = (a .&. 0xFF000000) `bitShiftR` 24
 in fromBits (b0 .|. b1 .|. b2 .|. b3)

data Ordering = LT | EQ | GT
