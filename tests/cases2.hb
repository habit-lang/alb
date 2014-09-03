requires prelude
requires test

class F t u | t -> u
    where foo :: t -> u
class C t
    where bar :: t -> Unsigned

instance F Unsigned Unsigned
   where foo x = x
else F t Bool
   where foo x = False

instance C Unsigned
   where bar x = x
else C t
   where bar x = 0

f :: t -> Unsigned
f x = bar (foo x)

-- g = foo
-- h :: Unsigned -> Bool
-- h = g

main = do x <- runTests (Cons (return (f True /= f (1 :: Unsigned)))
                        (Cons (return (f True == f (0 :: Unsigned)))
                         Nil))
          return x
