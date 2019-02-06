requires prelude
requires list
requires io

equalM x m = do
  m' <- m
  return (x == m')

runTests :: List (M Bool) -> M Unsigned
runTests xs = f 0 0 xs where
  passChar = 0x2E
  failChar = 0x58
  f :: Unsigned -> Unsigned -> List (M Bool) -> M Unsigned
  f pass total Nil = do
    putchar 0x20 -- space
    putchar 0x5B -- [
    putint pass
    putchar 0x20 -- space
    putchar 0x6F -- o
    putchar 0x66 -- f
    putchar 0x20 -- space
    putint total
    putchar 0x20 -- space
    putchar 0x74 -- t
    putchar 0x65 -- e
    putchar 0x73 -- s
    putchar 0x74 -- t
    putchar 0x73 -- s
    putchar 0x20 -- space
    putchar 0x70 -- p
    putchar 0x61 -- a
    putchar 0x73 -- s
    putchar 0x73 -- s
    putchar 0x5D -- ]
    putchar 0x0A -- \n
    return (total - pass)
  f pass total (Cons m ms) = do
    pass' <- if<- m then do putchar passChar; return (pass+1) else do putchar failChar; return pass
    flush
    f pass' (total+1) ms
