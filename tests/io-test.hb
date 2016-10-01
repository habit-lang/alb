requires prelude
requires io

main :: M Unsigned
main = do
  putchar 72; putchar 105; putchar 10 -- "Hi\n"
  putint (negate 1)
  putchar 0x0A
  putint 0
  putchar 0x0A
  putint 9
  putchar 0x0A
  putint 10
  putchar 0x0A
  putint 99
  putchar 0x0A
  putint 100
  putchar 0x0A
  putint 123
  putchar 0x0A
  putint 4294
  putchar 0x0A
  putint 42949
  putchar 0x0A
  putint 429496
  putchar 0x0A
  putint 4294967
  putchar 0x0A
  putint 42949672
  putchar 0x0A
  putint 429496729
  putchar 0x0A
  putint 4294967295
  putchar 0x0A
  return 0
