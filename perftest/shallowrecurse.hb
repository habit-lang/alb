requires miniprelude
requires test

main :: M Unsigned
main = do x <- return (recurser1 10)
	  return x

recurser1 :: Unsigned -> Unsigned
recurser1 acc = case acc of 0 -> 3
                            x -> (recurse2 10) + (recurser1 (x-1))

recurse2 :: Unsigned -> Unsigned
recurse2 acc = case acc of 0 -> 3
                           x -> (recurse3 10) + (recurse2 (x-1))

recurse3 :: Unsigned -> Unsigned
recurse3 acc = case acc of 0 -> 3
                           x -> (recurse4 10) + (recurse3 (x-1))

recurse4 :: Unsigned -> Unsigned
recurse4 acc = case acc of 0 -> 3
                           x -> (recurse5 10) + (recurse4 (x-1))

recurse5 :: Unsigned -> Unsigned
recurse5 acc = case acc of 0 -> 3
                           x -> (recurse6 10) + (recurse5 (x-1))

recurse6 :: Unsigned -> Unsigned
recurse6 acc = case acc of 0 -> 3
                           x -> (recurse7 10) + (recurse6 (x-1))

recurse7 :: Unsigned -> Unsigned
recurse7 acc = case acc of 0 -> 3
                           x -> (recurseLast 10) + (recurse7 (x-1))

recurseLast :: Unsigned -> Unsigned
recurseLast acc = case acc of 0 -> 3
                              x -> (recurseLast (x-1))



			
