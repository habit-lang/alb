requires md5
requires miniprelude
requires test
requires ondeckprelude

dgst a b c d = MD5Digest (MD5Par (swapEndian a) (swapEndian b) (swapEndian c) (swapEndian d))

kat1 = do
 b <- md5 Nil
 return (b == dgst 0xd41d8cd9 0x8f00b204 0xe9800998 0xecf8427e)

kat2 = do
  b <- md5 (Cons 97 Nil)
  return (b == dgst 0x332ce785 0xe973574a 0x1c5fdaf3 0xeee3f083)

kat3 = do
  b <- md5 (Cons 0x50534148 Nil) -- "HASP"
  return (b == dgst 0xa1a2740e 0x202e3bad 0x0abe31f1 0x67cab851)

main :: M Unsigned
main = do
  x <- runTests 
         (Cons kat1
         (Cons kat2
         (Cons kat3
         Nil)))
  return x
