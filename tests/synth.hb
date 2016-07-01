requires miniprelude

bitdata T = K [ x, y :: Bit 3 ]

instance T.z = Bit 6
  where t.z = t.x :# t.y

f :: (r.x = a) => r -> a
f r = r.x
