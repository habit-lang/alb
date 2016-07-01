requires miniprelude, list

opaque type Stack t = List t
    where new   :: List t -> Stack t
          new xs = xs

          push     :: t -> Stack t -> Stack t
          push x xs = Cons x xs

          pop            :: Stack t -> Maybe (t, Stack t)
          pop Nil         = Nothing
          pop (Cons x xs) = Just (x, xs)

          top            :: Stack t -> Maybe t
          top Nil         = Nothing
          top (Cons x xs) = Just x

f :: Eq t => t -> List t -> Bool
f x xs =
  case pop s of
    Nothing -> False
    Just (y, s') ->
      case top s' of
        Nothing -> False
        Just y' -> y == y'
  where s = push x (push x (new xs))
