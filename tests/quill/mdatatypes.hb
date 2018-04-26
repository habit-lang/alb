requires qprelude
-- requires rdatatypes

data Maybe a = Nothing | Just a

data Either l r = Left l | Right r


instance Un (Either a b) if Un a, Un b
else Un (Either a b) fails

class Functor f m | m -> f where
      fmap :: ((m a) >:= ((a ->{f} b) ->{g2} (m b))) => m a ->{g1} (a ->{f} b) ->{g2} m b

instance Functor (-!*>) Maybe where
      fmap a f = case a of
                   Nothing -> Nothing
                   Just a  -> Just (f a)

instance Functor (-!*>) (Either a) where
       fmap a f = case a of
                    Left a' -> Left a'
                    Right a' -> Right (f a')

-- interestingly the alternative definition where the function is mentioned first fails
-- class Functor f m | m -> f where
--       fmap :: ((Maybe a) >:= ((a ->{f} b) ->{g2} (Maybe b))) => (a ->{f} b) ->{g1} m a ->{g2} m b

-- instance Functor (-!*>) Maybe where
--       fmap f a = case a of
--                    Nothing -> Nothing
--                    Just a  -> Just (f a)

class Applicative f m | m -> f where
      pure  :: t -> m t
      (<*>) :: ( Un a
               , Un (m ((-!*>) a b))
               -- , (m a) >:= m (a ->{f} b) ->{g2} (m b)
               , (>:=) (m a) (g2 (m ((-!*>) a b)) (m b)))
               => m a ->{g1} m (a ->{f} b) ->{g2} m b

instance Applicative (-!*>) Maybe where
         pure a = Just a
         (<*>) a f = case a of
                       Nothing -> Nothing
                       Just a' -> case f of
                                    Nothing -> Nothing
                                    Just f' -> Just (f' a')

instance Applicative (-!*>) (Either a) where
       pure a = Right a
       (<*>) a f = case f of
                     Left e -> Left e
                     Right f' -> fmap a f'

class Monad f m | m -> f where
      return :: (t >:= m t) => t -> m t
      -- [ANI] TODO we need to give too many details here
      -- can we reduce the constraints to only (m t >:= g, f >:= m u)
      (>>=)  :: (f >:= m u, m t >:= ((t ->{f} m u) ->{g} m u))
                => m t ->{h} (t ->{f} m u) ->{g} m u

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

instance Monad (-!*>) (Either a) where
         return a  = Right a
         (>>=) a f = case a of
                       Left l -> Left l
                       Right l -> f l

-- instance Monad (-!*>) NEList where
--          return a = Last a
--          (>>=) (Last a) f = f a
--          (>>=) (Cons' a as) f = Cons' (f a) ((>>=) as f)
