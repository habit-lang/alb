requires miniprelude
requires test
--This tests a naive recursion to see if tail call works
--Also does some checking on how good the dead code eliminator is
--and generally tests the performance of "function call"

--Main function, does very little
main :: M Unsigned
main = do x <- return (bigrecurser (10000))
          return x

area a1 <- initArray (\x -> initStored (3)) :: Ref (Array 1000 (Stored Unsigned))

--bubblesort-
--  for(int i = 0; i< length of array; i++)
--      for (int j = 0; j < length of array-1; j++)
--         if(array[j]>array[j+1])
--         {
--             int temp = array[j];
--             array[j]=array[j+1];
--             array[j+1]=temp;
--          }
--
--          Note-THis is quite inefficient, doesn't break if there are no swaps

--inner for loop
bubblesort'iter :: Ref (Array 1000 (Stored Unsigned)) -> Unsigned -> Ref (Array 1000 (Stored Unsigned))
bubblesort'iter axs i = case (i == 999) of True -> axs
                                           False -> bubblesort'iter (if (readRef (axs @ i) > readRef (axs @ (i+1))) then (let temp = readRef (axs @ i) 
                                                                                                                          in let foo = writeRef (axs @ (i)) (readRef (axs @ (i+1))
                                                                                                                             in writeRef (axs @ (i+1)) (temp)) else axs) (i+1)

--outer for loop
bubblesort' :: Ref (Array 1000 (Stored Unsigned)) -> Unsigned -> Ref (Array 1000 (Stored Unsigned))
bubblesort' xs i = case (i == 1000) of True -> xs
                                       False -> (bubblesort' (bubblesort'iter xs 0) (i + 1))
     

bubblesort :: Ref (Array 1000 (Stored Unsigned)) -> Ref (Array 1000 (Stored Unsigned))
bubblesort xs = bubblesort' xs 0

--recurses acc times, then returns three
bigrecurser :: Unsigned -> Unsigned
bigrecurser acc = case acc of 0 -> 3
                              x -> (bigrecurser (x-1))
