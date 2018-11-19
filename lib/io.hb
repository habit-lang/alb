requires prelude
requires list

-- Perhaps these types could be updated?  I'm guessing that putchar should really return unit, and
-- fflush doesn't need an argument?

primitive getchar :: M Unsigned -- really should be Signed for -1
primitive putchar :: Unsigned -> M Unsigned
primitive fflush :: Unsigned -> M Unsigned

flush :: M ()
flush = do
  b <- return True
  fflush 0
  return ()

getint :: M Unsigned
getint = do x0 <- getchar
            if x0 == (negate 1)
            then return (negate 1)
            else do x1 <- getchar
                    if x1 == (negate 1)
                    then return (negate 1)
                    else do x2 <- getchar
                            if x2 == (negate 1)
                            then return (negate 1)
                            else do x3 <- getchar
                                    if x3 == (negate 1)
                                    then return (negate 1)
                                    else return (x3 `shiftL` 24 + x2 `shiftL` 16 + x1 `shiftL` 8 + x0)

putint :: Unsigned -> M ()
putint d | d < 10 = do putchar (d + 0x30); return ()
         | True = do putint (div10 d); putint (mod10 d)
  where mod10 :: Unsigned -> Unsigned
        mod10 x = unsigned (modIx x :: Ix 10)

        div10 :: Unsigned -> Unsigned
        div10 x | x < 10 = 0
                | True = f 1
          where f k = if x < 100 * k || k >= maxK then k + div10 (x - (10 * k)) else f (k * 10)
                maxK = 10000000

putHexChar :: Unsigned -> M Unsigned
putHexChar d | d < 0xa = putchar (d + 0x30)
             | True    = putchar (d + 0x37)

putHexInt :: Unsigned -> M ()
putHexInt d | d < 16 = do putHexChar d; return ()
            | True = do putHexInt (d `shiftR` 4); putHexInt (d .&. 0xF)

putLine :: M Unsigned
putLine = do
  x <- return ()
  putchar 0x0A

readInts :: M (List (Bit 32))
readInts = do
  x <- getint
  if x == (negate 1) then return Nil else do { xs <- readInts; return (Cons x.bits xs) }


putStr :: List Unsigned -> M Unsigned
putStr Nil = return (0)
putStr (Cons x xs) = do putchar x
                        putStr xs
