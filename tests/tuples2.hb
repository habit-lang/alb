requires miniprelude

aa = (True, False)
bb = (True, False, True, True)

ff (x, y) = (x, not x, y, not y)

gg :: (Bool, Bool, Bool) -> (Bool, Bool)
gg (x, y, z) = (not z, not y)