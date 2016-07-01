requires miniprelude
requires test

main :: M Unsigned
main = do x <- return (bigrecurser (1000000000 * 10))
          return x

bigrecurser :: Unsigned -> Unsigned
bigrecurser acc = if (acc /= 0) then bigrecurser (acc-1) else 3
