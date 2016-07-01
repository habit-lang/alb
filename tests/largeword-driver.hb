requires miniprelude
requires largeword
requires test

main :: M Unsigned
main = do
  x <- runTests (Cons (do x <- return (bit 4504 :: Word8192)
                          y <- return (bit 4505 :: Word8192)
                          return (((y + x) - y) == x)) Nil)
  return x
