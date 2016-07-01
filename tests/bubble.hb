-- Work in progress.... 
requires miniprelude

swap :: Storable a => Ref (Stored a) -> Ref (Stored a) -> M ()
swap l r = do temp <- readRef l
              readRef r >>= writeRef l
              writeRef r temp


for :: Index n => (Ix n) -> (Ix n) -> ((Ix n) -> M ()) -> M ()
for i j f | i == j = f i
          | i < j  = do f i
                        case (incIx i) of 
                           Just i' -> for i' j f              
                           Nothing -> return ()