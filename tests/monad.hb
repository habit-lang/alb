class Functor f
    where fmap :: (a -> b) -> f a -> f b

class Monad m | Functor m
    where return :: a -> m a
          (>>=)  :: m a -> (a -> m b) -> m b