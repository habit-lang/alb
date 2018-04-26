requires qprelude
-- requires rdatatypes

data Maybe a = Nothing | Just a

-- class Functor f m | m -> f where
--       fmap :: {- what should be the predicates here? -} (a -> b) ->{f1} m a ->{g1} m b

-- class Applicative f m | m -> f where
--       pure :: {- what should be the predicates here? -} t -> m t
--       (<$>) :: {- what should be the predicates here? -} m (a -> b) ->{f1} m a ->{g1} m b

class Monad f m | m -> f where
      return :: (t >:= m t) => t -> m t
      -- [ANI] TODO we need to give too many details here
      -- can we reduce the constraints to only (m t >:= g, f >:= m u)
      (>>=)  :: (f >:= m u, m t >:= ((t ->{f} m u) ->{g} m u))
                => m t ->{h} (t ->{f} m u) ->{g} m u

-- TODO This is broken now
instance Monad (-!*>) Maybe where
         -- return :: a -> Maybe a
         return = \a -> Just a

         -- we cannot have a linear funtion f
         -- here as it is can be discarded in the case of Nothing
         -- described above by (-!*>)
         -- (>>=) :: m a -> (a -> m b) -> m b
         (>>=) a f = case a of
                       Nothing -> Nothing
                       Just v  -> f v

-- instance Monad (-!*>) NEList where
--          return a = Last a
--          (>>=) (Last a) f = f a
--          (>>=) (Cons' a as) f = Cons' (f a) ((>>=) as f)

data Either a b = Left a | Right b

instance Monad (-!*>) (Either a) where
         return a  = Right a
         (>>=) a f = case a of
                       Left l -> Left l
                       Right l -> f l
