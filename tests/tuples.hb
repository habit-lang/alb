requires miniprelude

x = (True, False)
y = (False, True, True)
z = (,,) False True True

a :: (Bool, Bool)
a  = (False, True)

not True = False
not False = True

f (x, y) = (y, not x)

g :: (Bool, Bool) -> (,) Bool Bool
g ((,) x y) = (,) (not y) (not x)