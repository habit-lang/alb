requires quill

data T a b = MkT a b

f a = MkT a

g (MkT a b) = a
