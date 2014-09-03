requires prelude
requires test

main = do
  x <- runTests (Cons (equalM 3 main4) (Cons (equalM 3 main5) Nil))
  return x

-- This works:

m4 :: () -> Unsigned
m4 _ = 3

main4 :: M Unsigned
main4 = do x <- return (m4 ())
           return x

-- This fails:

m5 :: () -> Unsigned
m5 () = 3

main5 :: M Unsigned
main5 = do x <- return (m5 ())
           return x
