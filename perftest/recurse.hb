requires miniprelude
requires test

main = do x <- runTests (map (equalM 3) (Cons (bigrecurser 1000000000) Nil))
          return x

bigrecurser :: Unsigned -> M Unsigned
bigrecurser acc = case acc of 0 -> return 3
                              x -> (bigrecurser (x-1))


			
