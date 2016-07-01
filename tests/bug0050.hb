-- Bug #50: The primMaybeIx LC->Fidget rule doesn't always match

requires miniprelude
requires test

area a <- (initArray (\ix -> 0)) :: ARef 1 (Array 64 (Stored (Ix 32)))

main0 :: M Bool
main0 = do
  case maybeIx 0 of
    Nothing -> return 0
    Just i' -> readRef (a @ i')
  return True

main = do
  x <- runTests (Cons (main0) Nil)
  return x
