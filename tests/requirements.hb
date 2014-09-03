requires prelude
requires test

-- Transitive closure of a class:
class To t u
   where to :: t -> u

require To t v if To t u, To u v

instance To Unsigned (Bit 32)
    where to x = x.bits

instance To Bool Unsigned
    where to True = 1
          to False = 0

-- To test: comment out the following instance.  Should fail to compile
instance To Bool (Bit 32)
     where to True = 0b1
           to False = 0b0

-- Divisor-like class.  Missing a few operations
class DivisorLike t u | t -> u

require NumLit n u if NumLit n t, DivisorLike t u, 0 < n

-- Fake a non-zero type
data NZU = NZU Unsigned

instance DivisorLike Unsigned NZU

-- To test: comment out the following instance.  Should fail to compile:
instance NumLit n NZU if NumLit n Unsigned, 0 < n
   where fromLiteral x = NZU (fromLiteral x)

-- Requirements don't have to be for predicates of the form C vs:

class C t
   where foo :: t -> Unsigned
class D t
   where bar :: t -> Unsigned

require D t if C (Maybe t)

instance C Unsigned
   where foo x = x

instance C (Maybe Bool)
    where foo _ = 1
-- To test: comment out the following instance.
instance D Bool
    where bar x = foo (Just x)

f :: C (Maybe t) => t -> Unsigned
f x = bar x + foo (Just x)

main = do x <- runTests (Cons (return (f True == 2)) Nil)
          return x