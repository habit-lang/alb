requires miniprelude
requires test

main :: M Unsigned
main = do x <- testmonad1 (1000)
          y <- testmonad2 (x)
--          z <- testmonad3 (1000)
--          a <- testmonad4 (102)
--          b <- testmonad4 (102)
          return ((((x+y)+x)+y)+x)

testmonad1:: Unsigned -> M Unsigned
testmonad1 x = return 5

testmonad2:: Unsigned -> M Unsigned
testmonad2 x = if x == 4 then return 5 else return 6

testmonad3:: Unsigned -> M Unsigned
testmonad3 x = (return x) >>= (\z -> return 7)

testmonad4:: Unsigned -> M Unsigned
testmonad4 x = do i <- testmonad1 x
                  j <- testmonad2 x
                  k <- testmonad2 x
                  return (i+j+k)
