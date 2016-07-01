requires miniprelude
requires test
--This tests a naive recursion to see if tail call works
--Also does some checking on how good the dead code eliminator is
--and generally tests the performance of "function call"

--Main function, does very little
main :: M Unsigned
main = do x <- return (loop1 (1000000000 ))
          return x

--recurses acc times, then returns three
loop1:: Unsigned -> Unsigned
loop1 acc = case acc of 0 -> 0
                        x -> (loop2 (x-1))

--recurses acc times, then returns three
loop2:: Unsigned -> Unsigned
loop2 acc = case acc of 0 -> 0
                        x -> (loop1 (x-1))
