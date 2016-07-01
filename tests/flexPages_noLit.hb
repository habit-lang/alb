-- ### Flexpage data type and operations:

type WordSize = 32
type ByteSize = 8


-- Permissions:

bitdata Perms/3 = Perms [ r, w, x :: Bit 1 ]

nilPerms :: Perms
nilPerms  = Perms [ r=B0 | w=B0 | x=B0 ]

allPerms :: Perms
allPerms  = Perms [ r=B1 | w=B1 | x=B1 ]


-- Flexpages:

bitdata Fpage/WordSize
  = Fpage [ base :: Bit 22 | size :: Bit 6 | B0 | perms :: Perms ]


fpageSize        :: Fpage -> Bit 6
fpageSize fp      = fpsize fp.size

fpsize           :: Bit 6 -> Bit 6
fpsize n
  | n==1 || n==32 = 32
  | n<12 || n>32  = 0
  | otherwise     = n


fpageMask        :: Fpage -> Unsigned
fpageMask fp      = fpmask fp.size

fpmask           :: Bit 6 -> Unsigned
fpmask n
  | n==1 || n==32 = not 0
  | n<12 || n>32  = 0
  | otherwise     = (1 << n) - 1

-- It would be nice to have *fpmask* and *fpsize* compiled into
-- lookup tables.


-- Nil and complete flexpages:

nilFpage       :: Fpage
nilFpage        = Fpage [ base=0 | size=0 | perms=nilPerms ]

isNil          :: Fpage -> Bool
isNil fp        = fpageMask fp == 0

completeFpage  :: Perms -> Fpage
completeFpage p = Fpage [ base=0 | size=1 | perms=p ]

isComplete     :: Fpage -> Bool
isComplete fp   = not (fpageMask fp) == 0


-- Flexpage address ranges:

fpageStart        :: Fpage -> Unsigned
fpageStart fp      = (fp.base # 0) .&. not (fpageMask fp)

fpageEnd          :: Fpage -> Unsigned
fpageEnd fp        = (fp.base # 0) .|. fpageMask fp


inside            :: Fpage -> Fpage -> Bool
fp1 `inside` fp2   = (fpageStart fp1 <= fpageStart fp2)
                     && (fpageEnd fp2 <= fpageEnd fp1)

overlaps          :: Fpage -> Fpage -> Bool
fp1 `overlaps` fp2 = not (fp1 `disjoint` fp2)

disjoint          :: Fpage -> Fpage -> Bool
fp1` disjoint` fp2 = (fp1 `before` fp2) || (fp2 `before` fp1)

before            :: Fpage -> Fpage -> Bool
fp1 `before` fp2   =  fpageEnd fp1 < fpageStart fp2


-- Trimming flexpages:

trimFpage :: Fpage -> Unsigned -> Fpage -> Fpage
trimFpage big base small
  = small [ base = (big.base .&. not bmask) .|. (base .&. bmask .&. not smask) ]
    where (bmask # _ ) = fpageMask big
          (smask # _ ) = fpageMask small


