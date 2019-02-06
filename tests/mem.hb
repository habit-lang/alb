requires prelude

readRef  = primReadRefStored
writeRef = primWriteRefStored


primitive primReadRefStored  :: Ref (Stored a) -> M a
primitive primWriteRefStored :: Ref (Stored a) -> a -> M ()

-- class MemMonad m | Monad m
--     where memZero :: ARef l a -> m ()
--           memCopy :: ARef l a -> ARef l' a -> m ()
--           readRef :: ARef l a -> m (ValIn a)
--           writeRef :: ARef l a -> ValIn a -> m ()
--
-- instance MemMonad M
--     where memZero = primMemZero
--           memCopy = primMemCopy
--           readRef = primReadRef
--           writeRef = primWriteRef
--
-- primitive primMemZero  :: ARef l a -> M ()
-- primitive primMemCopy  :: ARef l a -> ARef l' a -> M ()
-- primitive primReadRef  :: ARef l a -> M (ValIn a)
-- primitive primWriteRef :: ARef l a -> ValIn a -> M ()