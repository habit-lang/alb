requires miniprelude

f x = let y = x + 1 in (
      let x = y + 1 in (
      let g x = f x + 1 in (
      let f x = g x + 1 in (
      f x + f y ))))

g x = let y = x + 1 in
      let x :: Unsigned
          x = y + 1 in
      x

data T = T Unsigned

h x = case x of
        T x -> case T x of
                 T x -> x + 1

j x = case y - 1 of
        0 -> 0
        y' -> case y' - 1 of
                0 -> 0
                y'' -> y''
    where y = x + 1