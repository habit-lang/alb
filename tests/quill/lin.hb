requires quill

f x y = x
f' (x, y) = x -- Temporarily broken

g :: t -> t
g y = (\x -> x) y

id x = x
h x = id x
j x = (\f -> f (f x)) id

eq x y = id (x == y)
ne x y = not (x == y)

pair x y = (\x -> (\w -> (x, w))) y x