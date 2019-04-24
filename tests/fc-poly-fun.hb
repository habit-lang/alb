class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *

data Bool = True | False

data Nat = Z | S Nat

data Pair a b = (forall a, b) P a b 

id = \x -> x

-- p :: Pair Bool Nat
p = P (id True) (id Z)

main = p
