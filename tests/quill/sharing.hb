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

shPair = \x -> \&y -> \sh -> sh x y

sePair = \x -> \*y -> \se -> se x y

-- Because this is a sharing pair, there should not be any Uns on the
-- variables that are not used
fst = \x -> \&y -> x
snd = \x -> \&y -> y

-- how will fst . shPair typecheck?
-- how will snd . shPair typecheck?


-- This is a linear pair, hence the variables that
-- that are not used should be marked as un
fst' = \x -> \*y -> x
snd' = \x -> \*y -> y
