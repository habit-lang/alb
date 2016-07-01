-----------------------------------------------------------------
requires prelude

-- Misc Test Code/Staging ---------------------------------------

data Wrap a = MkWrap a
 deriving (Bounded, Num, Boolean, Ord, Eq)

data Bar = A | B | C
  deriving Eq, Ord, Bounded

data Foo = X Bar -- Bar
 deriving Bounded, Eq, Ord

x = maxBound :: Foo

instance Num Bar
  where x + y = A
        x - y = B
        x * y = C
        negate x = x

data List a = Nil | Cons a (List a)
  deriving Eq, Ord

data Quad a b c d = Quad a b c d
 deriving Eq, Ord, Bounded

type Three = 3
bitdata Test /Three = MkBits [ value :: Ix 6 ]
 deriving (ToBits)

test  :: Test -> Test
test t = case incIx t.value of
           Nothing -> MkBits [value=0]
           Just i  -> MkBits [value=i]

-----------------------------------------------------------------
