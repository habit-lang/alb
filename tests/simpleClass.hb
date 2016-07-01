requires miniprelude

class C (a :: type) where
  c :: a -> a

class M0 (m :: type -> type) where
  m0 :: a -> m a

class M1 (m :: type -> *) where
  m1 :: a -> m a

class M2 (m :: * -> type) where
  m2 :: a -> m a

class M3 (m :: * -> *) where
  m3 :: a -> m a

