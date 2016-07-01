requires miniprelude
requires test

main :: M Unsigned
main = do x <- return (recurse1 10)
	  return x

recurse1 :: Unsigned -> Unsigned
recurse1 acc = case acc of 0 -> 3
                           x -> if (recurse2 10) /= (recurse1 (x-1)) then 4 else 3

recurse2 :: Unsigned -> Unsigned
recurse2 acc = case acc of 0 -> 3
                           x -> if (recurse3 10) /= (recurse2 (x-1)) then 4 else 3

recurse3 :: Unsigned -> Unsigned
recurse3 acc = case acc of 0 -> 3
                           x -> if (recurse4 10) /= (recurse3 (x-1)) then 4 else 3

recurse4 :: Unsigned -> Unsigned
recurse4 acc = case acc of 0 -> 3
                           x -> if (recurse5 10) /= (recurse4 (x-1)) then 4 else 3

recurse5 :: Unsigned -> Unsigned
recurse5 acc = case acc of 0 -> 3
                           x -> if (recurse6 10) /= (recurse5 (x-1)) then 4 else 3

recurse6 :: Unsigned -> Unsigned
recurse6 acc = case acc of 0 -> 3
                           x -> if (recurse7 10) /= (recurse6 (x-1)) then 4 else 3

recurse7 :: Unsigned -> Unsigned
recurse7 acc = case acc of 0 -> 3
                           x -> if (recurse8 10) /= (recurse7 (x-1)) then 4 else 3

recurse8 :: Unsigned -> Unsigned
recurse8 acc = case acc of 0 -> 3
                           x -> if (recurseLast 10) /= (recurse8 (x-1)) then 4 else 3

recurseLast :: Unsigned -> Unsigned
recurseLast acc = case acc of 0 -> 3
                              x -> (recurseLast (x-1))
