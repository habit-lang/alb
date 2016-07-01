requires miniprelude

--  Some bitdata test cases:

bitdata PCI   = PCI [ bus :: Bit 8 | dev :: Bit 5 | fun :: Bit 3 ]

bitdata Perms = Perms [ r, w, x :: Bool ]
bitdata FPage = FPage   [ base :: Bit 22 | size :: Bit 6 | B0 | perms :: Bit 3 ]
              | NilPage [ 0 ]

-- Examples from the report of invalid definitions:
-- bitdata U = X [ x :: U ]

-- rejected, but perhaps for the wrong reason ...
-- bitdata V = Y [ x :: W | B1 ]
-- bitdata W = Z [ z :: V ]

-- rejected, error could be better (say width not uniquely determined, actually no solutions)
-- bitdata V1    = Y [ x :: W1 | B1 ]
-- bitdata W1/32 = Z [ z :: V1 ]

bitdata R/8 = A [ x :: Bit 4 | 0 ]
bitdata S   = B  [ 0 ]  | C  [ B1111]
-- bitdata S1  = B1 [ 16 ] | C1 [ B1111] -- rejected, correctly, literal 16 is too big for 4 bits
bitdata S2  = B2 [ 16 ] | C2 [ B11110]

bitdata Perms1 = Perms1 [ r=False, w=False, x=False :: Bool ] -- duplicate constructor!
bitdata Perms2 = Perms2 [ r=B0, w=B0, x=B0 :: Bit 1 ] -- duplicate constructor!

nilPerms1 = Perms2 [ x=B1 | r=B0 | w=B0 ]
nilPerms2 = Perms2 [ r=B0 | x=B1 | w=B0 ]
nilPerms3 = Perms2 [ w=B0 | x=B1 ]
nilPerms4 = Perms2 [ x=B1 ]
nilPerms  = Perms2 [ ]

-- data Baz = Q | Q -- should be rejected: duplicate constructor

-- data F1 = X1 | Z -- cannot be defined together: both use a constructor called Z
-- data F2 = X2 | Z
