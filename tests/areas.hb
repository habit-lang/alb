-- TODO: compilation fails with alb: type_prim undefined prim name:primStructInit, ...
requires prelude
requires ondeckprelude

struct S [ x, y, z :: Stored Unsigned ]
 deriving (NullInit, NoInit)

{-
baz = S [ x <- initialize | y <- initialize | z <- initialize ]
-}

area test <- nullInit :: ARef 4 S

myInit :: Init S
myInit  = nullInit

struct S0         [ x, y, z :: Stored Unsigned ]
struct S1/12      [ x, y, z :: Stored Unsigned ]
struct S2/(8+4)   [ x, y, z :: Stored Unsigned ]
struct S3/(3*4)   [ x, y, z :: Stored Unsigned ]
struct S4/((1+2)*(1+1+1+1))
                  [ x, y, z :: Stored Unsigned ]
type SLength = 6 * 2
struct S5/SLength
                  [ x, y, z :: Stored Unsigned ]
--The following should not be valid!
--struct S6/n       [ x, y, z :: Stored Unsigned ]
--struct S7/(n + m) [ x, y, z :: Stored Unsigned ]

struct R  [ u <- primInitS0 :: S0 | v :: Stored Unsigned | w :: S0 ]
struct R1 [ u :: S0 | Stored Unsigned | w :: S0 ]

struct T [ left  :: Array 10 (Stored Unsigned)
         | right :: Array 2 (Array 4 (Stored Unsigned)) ]

----area foo :: ARef 8 (Array 12 (Stored Unsigned))
----area bar <- primInitS0 :: ARef 4 S0

primitive primInitS0 :: Init S0

-- rejected, correctly: (multiple fields called x, y)
-- struct U [ x :: Stored Unsigned | x :: Stored Unsigned | y :: Stored Unsigned | x :: Stored Unsigned | y :: Stored Unsigned ]

-- rejected, correctly: (multiple fields called x)
-- bitdata V = HJ [ x :: Bit 5 | x :: Bit 4 ]

bitdata V = HJ [ x :: Bit 5 | xy :: Bit 4 ]

-- Rejected: there are no fields called z for constructor HJ
-- t1 = HJ [ xy = B1010 | x = B10101 | z = B11 ]

-- Rejected: multiple 
-- t2 = HJ [ xy = B1010 | x = B10101 | x = B11111 ]
-- t3 = HJ [ xy = B1010 | x = B11111 | x = B10101 ]

main = id True
