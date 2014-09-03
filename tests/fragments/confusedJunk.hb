requires prelude

bitdata Vals    = V [ x :: Bit 2 | B001 | y :: Perms ]
                | W [ u :: Bit 2 | B010 | B111       ]

bitdata Perms   = Perms [ r, w, x :: Bit 1 ]

bitdata Whittle = None [ B00000 ]
                | Some [ x :: Bit 4 | B0 ]
                | Many [ y :: Bit 4 | B0 ]
                  deriving ToBits, FromBits

bitdata Toys = T [ x :: Bit 2 | B001 | y :: Ix 6 ]

bitdata Frank   = Jet    [ engine :: Bit 4 ]
                | Turbo  [ prop :: Bit 1 | B010 ]
                | Glider [ span :: Bit 2 | other :: Odd ]
                  deriving ToBits, FromBits

bitdata Odd = A [ B00 ]
            | B [ B11 ]
              deriving ToBits, FromBits
