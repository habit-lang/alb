requires miniprelude
requires test

  

area big <- (initArray (\x -> initStored 42)) :: Ref( Array 16384 (Stored Unsigned))


main = do
   x <- runTests (Cons main0 Nil)
   return x

main0 :: M Bool
main0 = do x <- readRef (big @ 1024)
           return (x == 42)

