--------------------------------------------------------------------------------
-- Quill prelude
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Primitive types and classes: functions and linearity

primitive type (-*>) :: * -> * -> *
primitive type (-!>) :: * -> * -> *
class (->) (f :: * -> * -> *)
infixr type 5 -*>, -!>, ->

instance (->) (-!>)
else (->) (-*>)
else (->) t fails

class t >:= u
instance t >:= u fails if Un t fails, Un u
else t >:= u

class Un t
instance Un (-!>)
instance Un ((-!>) t)
instance Un (t -!> u)

instance Un (-*>) fails
instance Un ((-*>) t) fails
instance Un (t -*> u) fails

class ShFun t
instance ShFun (-*>) fails
instance ShFun ((-*>) t) fails
instance ShFun (t -*> u) fails

instance ShFun (-!>)
instance ShFun ((-!>) t)
instance ShFun (t -!> u)

class SeFun t
instance SeFun (-!>) fails
instance SeFun ((-!>) t) fails
instance SeFun (t -!> u) fails

instance SeFun (-*>)
instance SeFun ((-*>) t)
instance SeFun (t -*> u)


--------------------------------------------------------------------------------
-- Basic examples for pair


-- This is now broken ¯\_(ツ)_/¯
-- shPair = \s -> \&h -> \*sh -> sh s h
-- sePair = \s -> \*e -> \se -> se s e



-- Because this is a sharing pair, there should not be any Uns on the
-- variables that are not used
fst = \x -> \&y -> x
snd = \x -> \&y -> y

-- cfst :: ((->) f, SeFun g, (>:=) a (g b (h c a)),
--              Un b, ShFun h, (>:=) a (h c a), Un c) =>
--                 a -{f} (b ->{g} (c ->{h} a))
cfst = \z -> \*x -> \&y -> z


-- csnd :: ((->) f, (>:=) c (f a (g b (h c c))),
--          (>:=) b (f a (g b (h c c))), Un a, SeFun g,
--          (>:=) c (g b (h c c)),
--          ShFun h, (>:=) b (h c c)) =>
--                  a ->{f} (b ->{g}(c ->{h} c))
csnd = \z -> \*x -> \&y -> y


-- csnd' :: ((->) f, (>:=) c (f a (g b (h c b))),
--           (>:=) b (f a (g b (h c b))), Un a, SeFun g,
--           (>:=) c (g b (h c b)),
--           ShFun h, (>:=) b (h c b)) =>
--                  a ->{f} (b ->{g} (c ->{h} b))
csnd' = \z -> \*x -> \&y -> x

-- how will fst . shPair typecheck?
-- how will snd . shPair typecheck?


-- This is a linear pair, hence the variables that
-- that are not used should be marked as Un
fst' = \x -> \*y -> x
snd' = \x -> \*y -> y
