primitive type (->) :: * -> * -> *

class C (a::type)

class T (a::type) where t :: a -> a

class U (a::type)
instance T a if U a fails
  where t x = x

data Unit = Unit
instance U Unit fails
instance C Unit

f :: (U t fails, C t) => t -> t
f = t

g = f

main = g (t Unit) :: Unit

-- Testing for overlapping instances:
-- class C (a::type)
-- instance C a fails
-- instance C Unit

