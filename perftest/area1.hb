requires miniprelude
requires test
--This tests a naive recursion to see if tail call works
--Also does some checking on how good the dead code eliminator is
--and generally tests the performance of "function call"

--Main function, does very little
main :: M Unsigned
main = do x <- return (bigrecurser (10000))
          return x

area a1 <- initStored 3 :: Ref (Stored Unsigned)
--recurses acc times, then returns three
bigrecurser :: Unsigned -> Unsigned
bigrecurser acc = case acc of 0 -> 3
                              x -> (bigrecurser (x-1))
