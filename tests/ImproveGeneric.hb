requires miniprelude

class C (t :: *) (u :: *)
class F (t :: *) = (u :: *)
class G (t :: *) = (u :: *)

instance F Unsigned Bool
instance G Unsigned (Bit 4)

instance C t u if F t u
instance C t u if F t u fails, G t u

h :: (C Unsigned t) => t -> t
h = h

