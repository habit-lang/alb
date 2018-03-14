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



-- shPair :: ((->) f$2w, ShFun f$30, (>:=) t$3g (f$30 t$36 (f$34 (f$3j t$3g (f$3e t$36 t$33)) t$33)),
--            (->) f$34, (>:=) t$3g (f$34 (f$3j t$3g (f$3e t$36 t$33)) t$33),
--            (>:=) t$36 (f$34 (f$3j t$3g (f$3e t$36 t$33)) t$33)) =>
--            f$2w t$3g (f$30 t$36 (f$34 (f$3j t$3g (f$3e t$36 t$33)) t$33))

shPair :: ((->) f1, ShFun g1
           , a >:= (b ->{g1} ((a ->{k1} (b ->{j1} c)) ->{h1} c))
           , (>:=) a (h1 (k1 a (j1 b c)) c)
           , (->) h1
           -- , a >:= ((a ->{k1} (b ->{k1} c)) ->{g1} c)
           , b >:= ((a ->{k1} (b ->{j1} c)) ->{h1} c)
           -- , a >:= ((a ->{k1} (b ->{j1} c)) ->{h1} c)   -- This could not be automatically infered
           , (>:=) b (f1 a (g1 b (h1 (k1 a (j1 b c)) c))) -- This could not be automatically infered
           , SeFun j1, SeFun k1                        -- Th1is could not be automatically infered
           ) => a ->{f1} (b ->{g1} ((a ->{k1} (b ->{j1} c)) ->{h1} c))
shPair = \sh1 -> \&sh2 -> \sh -> sh sh1 sh2


sePair :: ((->) f, SeFun g
           , a >:= (b ->{g} ((a ->{k} (b ->{j} c)) ->{h} c))
           , (>:=) a (h (k a (j b c)) c)
           , (->) h
           -- , a >:= ((a ->{k} (b ->{j} c)) ->{h} c)
           , b >:= ((a ->{k} (b ->{j} c)) ->{h} c)
           , SeFun j, SeFun k -- This could not be automatically infered
           ) =>
           a ->{f} (b ->{g} ((a ->{k} (b ->{j} c)) ->{h} c))
sePair = \sp1 -> \*sp2 -> \sp -> sp sp1 sp2



-- Because this is a sharing pair, there should not be any Uns on the
-- variables that are not used
fst = \x1 -> \&y1 -> x1
snd = \x2 -> \&y2 -> y2

-- cfst :: ((->) f, SeFun g, (>:=) a (g b (h c a)),
--              Un b, ShFun h, (>:=) a (h c a), Un c) =>
--                 a -{f} (b ->{g} (c ->{h} a))
-- cfst = \z -> \*x -> \&y -> z


-- csnd :: ((->) f, (>:=) c (f a (g b (h c c))),
--          (>:=) b (f a (g b (h c c))), Un a, SeFun g,
--          (>:=) c (g b (h c c)),
--          ShFun h, (>:=) b (h c c)) =>
--                  a ->{f} (b ->{g}(c ->{h} c))
-- csnd = \z -> \*x -> \&y -> y


-- csnd' :: ((->) f, (>:=) c (f a (g b (h c b))),
--           (>:=) b (f a (g b (h c b))), Un a, SeFun g,
--           (>:=) c (g b (h c b)),
--           ShFun h, (>:=) b (h c b)) =>
--                  a ->{f} (b ->{g} (c ->{h} b))
-- csnd' = \z -> \*x -> \&y -> x

-- how will fst . shPair typecheck?
-- how will snd . shPair typecheck?


-- This is a linear pair, hence the variables that
-- that are not used should be marked as Un
-- fst' = \x -> \*y -> x
-- snd' = \x -> \*y -> y
