requires md5
requires miniprelude
requires test
requires ondeckprelude
requires io

main :: M Unsigned
main = do
  x <- readInts
  case <- md5 x of
    MD5Digest (MD5Par a b c d) ->
      do putHexInt (fromBits (swapEndian a))
         putchar 0x20
         putHexInt (fromBits (swapEndian b))
         putchar 0x20
         putHexInt (fromBits (swapEndian c))
         putchar 0x20
         putHexInt (fromBits (swapEndian d))
         putchar 0x0A
         return (0 :: Unsigned)
