class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *
infixr type 5 ->

data Mnd m = (forall a, b) (if m @ a, m @ b) MkMonad (a -> m a) (m a -> (a -> m b) -> m b)
