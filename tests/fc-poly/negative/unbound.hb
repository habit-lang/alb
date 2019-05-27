-- Partial data types: ------------------------------------------

class (@) (t :: k' -> k) (u :: k')

-- Basic types: -------------------------------------------------

primitive type (->) :: * -> * -> *
infixr type 5 ->

data Blah2 m = MkBlah2 (f g -> m)
