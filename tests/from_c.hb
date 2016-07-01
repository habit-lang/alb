requires miniprelude
requires list
requires io

area counter <- (initStored 3) :: Ref (Stored Unsigned)

incArea :: M Unsigned
incArea = do
  v <- readRef counter
  writeRef counter (v + 1)
  return v

inc :: Unsigned -> Unsigned -> M Unsigned
inc x y = return (0x10000 * x + y + 1)

incPure :: Unsigned -> Unsigned -> Unsigned
incPure x y = 0x10000 * x + y + 1

main :: M Unsigned
main = do
  x <- return 0
  return x
