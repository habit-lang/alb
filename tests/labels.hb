requires miniprelude

primitive type T :: *
primitive type U :: *

primitive t :: T
primitive u :: U

instance Select T "f" U
   where select _ _ = u

x = select t #"f"
y = select t #"g"