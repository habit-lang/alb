requires miniprelude
requires test
--This tests a naive recursion to see if tail call works
--Also does some checking on how good the dead code eliminator is
--and generally tests the performance of "function call"

--Main function, does very little
main :: M Unsigned
main = do x <- return (bigrecurser (10000))
          return x

bubblesort'iter :: List Unsigned -> List Unsigned
bubblesort'iter (Cons x (Cons y (Cons xs Nil))) = case (x > y) of True ->  (Cons y (bubblesort'iter (Cons x (Cons xs Nil))))
                                                                  False -> (Cons x (bubblesort'iter (Cons y (Cons xs Nil))))

bubblesort'iter :: List Unsigned -> List Unsigned
bubblesort'iter (Cons x (Cons y Nil)) = (Cons x (Cons y Nil))

bubblesort'iter :: List Unsigned -> List Unsigned
bubblesort'iter (Cons x Nil) = (Cons x  Nil)

bubblesort' :: List Unsigned -> Unsigned -> List Unsigned
bubblesort' xs i = case (i == length xs) of True -> xs
                                            False -> (bubblesort' (bubblesort'iter xs) (i + 1))
     
bubblesort :: List Unsigned -> List Unsigned
bubblesort xs = bubblesort' xs 0

area a1 <- initStored 3 :: Ref (Stored Unsigned)
--recurses acc times, then returns three
bigrecurser :: Unsigned -> Unsigned
bigrecurser acc = case acc of 0 -> 3
                              x -> (bigrecurser (x-1))
