primitive type (->) :: * -> * -> *
infixr type 5 ->

class AreaOf (t :: *) = (a :: area)
instance AreaOf (Ref a) = a
else     AreaOf a n fails -- why?

class Update (r :: *) (f :: lab)
  where update :: r -> #f -> Select r f -> r

class Select (r :: *) (f :: lab) = (t :: *)
  where select :: r -> #f -> t

data Proxy t = Proxy

primitive type ARef   :: nat -> area -> *
primitive type Ref    :: area -> *
primitive type Init   :: area -> *
primitive type Stored :: type -> area
primitive type Bit    :: nat -> *

bitdata Unsigned = Unsigned [ bits :: Bit 32 ]

external area test = 0x0012 :: ARef 4 (Stored Unsigned) 
