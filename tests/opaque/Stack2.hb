requires miniprelude, list

class Stack t = u | u -> t, opaque u
    where new :: List t -> u
          push :: t -> u -> u
          pop :: u -> Maybe (t, u)
          top :: u -> Maybe t

instance Stack t (List t)
    where new xs = xs

          push x xs = Cons x xs

          pop Nil = Nothing
          pop (Cons x xs) = Just (x, xs)

          top Nil = Nothing
          top (Cons x _) = Just x

f :: t -> t -> List t -> t
f x y xs = case pop (push x (push x (new xs))) of
             Nothing -> y
             Just (_, s) ->
               case pop s of
                 Nothing -> y
                 Just (z, _) -> z


g :: Eq t => t -> List t -> Bool
g x xs =
  let s = push x (push x (new xs)) in
  case pop s of
    Nothing -> False
    Just (y, s') ->
      case top s' of
        Nothing -> False
        Just y' -> y == y'
