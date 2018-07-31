requires prelude

class MemMonad m | Monad m
    where memZero :: ARef l a -> m ()
          memCopy :: ARef l a -> ARef l' a -> m ()
          readRef :: ARef l a -> m (ValIn a)
          writeRef :: ARef l a -> ValIn a -> m ()

instance MemMonad M
    where memZero = primMemZeroM
          memCopy = primMemCopyM
          readRef = primReadRefM
          writeRef = primWriteRefM

primitive primMemZeroM  :: ARef l a -> M ()
primitive primMemCopyM  :: ARef l a -> ARef l' a -> M ()
primitive primReadRefM  :: ARef l a -> M (ValIn a)
primitive primWriteRefM :: ARef l a -> ValIn a -> M ()