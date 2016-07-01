requires miniprelude

type D t = Maybe t

class C t
instance C (D t)
instance C Bool