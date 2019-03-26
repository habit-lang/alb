requires prelude
requires io

foo :: Bit 6 -> Bit 8
foo x = y :# y :# z --  ~~> (in part) (let { pbc = primBitsConcat{1,1,2}; v = pbc y y } ...)
  where y :: Bit 1
        y :# z = x
        -- v = {y :# z <- x => ^(y, z)}  ~~>  {let { getHi = primBitsHi{1,6};
        --                                           getLo = primBitsLo{5,6};
        --                                           y = getHi x;
        --                                           z = getLo x } => ^(y, z)}
        -- y = fst v
        -- z = snd v

main = putint (Unsigned[bits = 0 :# foo B10_0000])