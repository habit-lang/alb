requires prelude
requires mem
requires io

struct S[x, y :: Stored Unsigned]

area a <- S[x <- 1 | y <- 2] :: Ref S

main = do z <- readRef a.x
          putint z
