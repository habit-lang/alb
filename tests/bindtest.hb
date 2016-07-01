
-- Monads:

class Monad m
  where retn  :: a -> m a
        (>>=) :: m a -> (a -> m b) -> m b

-- The machine monad:

primitive type M (a :: *)

primitive primReturnM :: a -> M a
primitive primBindM   :: M a -> (a -> M b) -> M b

instance Monad M
  where retn  = primReturnM
        (>>=) = primBindM

-- The Proc(edure) class:

class Proc p | Monad p  -- super class required!
instance Proc M
else     Proc m if Monad m
else     Proc m fails

-- Simple test code
primitive type Int
primitive one :: Int
primitive type Char

primitive foo :: Int -> M Char

data Pair a b = Pair a b

main1 = foo one >>= (\x ->
        foo one >>= (\y ->
        retn (Pair x y)))

main = do x <- foo one
          y <- foo one
          retn (Pair x y)

