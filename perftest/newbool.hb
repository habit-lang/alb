requires miniprelude

myNot :: Bool -> Bool
myNot x = case x of True -> False
		    False -> True
