-- Bug #51: Using Bounded (Ix n) causes a type error

requires miniprelude
requires test

main = do
  x <- runTests (Cons (return (2 == unsigned (maxBound :: Ix 3))) Nil)
  return x
