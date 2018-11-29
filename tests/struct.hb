requires prelude
requires mem
requires io

struct S[y :: Stored Unsigned | x :: Stored (Bit 8)]

-- Things that should fail:
--
-- struct S[y :: Stored Unsigned | x :: Stored (Bit 8)]
--   aligned 1
--
-- Because the alignment is too small for the 'y' component
--
-- struct S[x :: Stored (Bit 8) | y :: Stored Unsigned]
--
-- Because the y field has the wrong alignment

struct T / 5 [y :: Stored Unsigned | x :: Stored (Bit 8)]
  aligned 4K

area a <- S[x <- 1 | y <- 2] :: Ref S

main = do z <- readRef a.y
          putint z
