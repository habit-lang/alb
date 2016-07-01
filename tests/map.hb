-- module map

requires miniprelude
requires ondeckprelude

data Map k a  = Tip
              | Bin Size k a (Map k a) (Map k a)

type Size = Unsigned

isEmpty :: Map k a -> Bool
isEmpty Tip      = True
isEmpty (Bin _ _ _ _ _) = False

size :: Map k a -> Unsigned
size Tip              = 0
size (Bin sz _ _ _ _) = sz

lkup :: Ord k => k -> Map k a -> Maybe a
lkup k = go
  where
    go Tip = Nothing
    go (Bin _ kx x l r) =
        case compare k kx of
            LT -> go l
            GT -> go r
            EQ -> Just x


member :: Ord k => k -> Map k a -> Bool
member k m = case lkup k m of
    Nothing -> False
    Just _  -> True

notMember :: Ord k => k -> Map k a -> Bool
notMember k m = not (member k m)

findWithDefault :: Ord k => a -> k -> Map k a -> a
findWithDefault def k m = case lkup k m of
    Nothing -> def
    Just x  -> x

empty :: Map k a
empty = Tip

singleton :: k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip

insert :: Ord k => k -> a -> Map k a -> Map k a
insert kx x = go
  where
    go Tip = singleton kx x
    go (Bin sz ky y l r) =
        case compare kx ky of
            LT -> balance ky y (go l) r
            GT -> balance ky y l (go r)
            EQ -> Bin sz kx x l r

join :: Ord k => k -> a -> Map k a -> Map k a -> Map k a
join kx x Tip r  = insertMin kx x r
join kx x l Tip  = insertMax kx x l
join kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL <= sizeR  = balance kz z (join kx x l lz) rz
  | delta*sizeR <= sizeL  = balance ky y ly (join kx x ry r)
  | otherwise             = bin kx x l r

insertMax,insertMin :: k -> a -> Map k a -> Map k a
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y l (insertMax kx x r)

insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y (insertMin kx x l) r

merge :: Map k a -> Map k a -> Map k a
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  | delta*sizeL <= sizeR = balance ky y (merge l ly) ry
  | delta*sizeR <= sizeL = balance kx x lx (merge rx r)
  | otherwise            = glue l r

glue :: Map k a -> Map k a -> Map k a
glue Tip r = r
glue l Tip = l
glue l r
  | size l > size r = let ((km,m),l') = deleteFindMax l in balance km m l' r
  | otherwise       = let ((km,m),r') = deleteFindMin r in balance km m l r'
delta,ratio :: Unsigned
delta = 4
ratio = 2

balance :: k -> a -> Map k a -> Map k a -> Map k a
balance k x l r
  | sizeL + sizeR <= 1    = Bin sizeX k x l r
  | sizeR >= delta*sizeL  = rotateL k x l r
  | sizeL >= delta*sizeR  = rotateR k x l r
  | otherwise             = Bin sizeX k x l r
  where
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1

-- rotate
rotateL :: a -> b -> Map a b -> Map a b -> Map a b
rotateL k x l r@(Bin _ _ _ ly ry)
  | size ly < ratio*size ry = singleL k x l r
  | otherwise               = doubleL k x l r
-- rotateL _ _ _ Tip = error "rotateL Tip"

rotateR :: a -> b -> Map a b -> Map a b -> Map a b
rotateR k x l@(Bin _ _ _ ly ry) r
  | size ry < ratio*size ly = singleR k x l r
  | otherwise               = doubleR k x l r
-- rotateR _ _ Tip _ = error "rotateR Tip"

-- basic rotations
singleL, singleR :: a -> b -> Map a b -> Map a b -> Map a b
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3
-- singleL _ _ _ Tip = error "singleL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)
-- singleR _ _ Tip _ = error "singleR Tip"

doubleL, doubleR :: a -> b -> Map a b -> Map a b -> Map a b
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
-- doubleL _ _ _ _ = error "doubleL"
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
-- doubleR _ _ _ _ = error "doubleR"

bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r
  = Bin (size l + size r + 1) k x l r

deleteFindMin :: Map k a -> ((k,a),Map k a)
deleteFindMin t
  = case t of
      Bin _ k x Tip r -> ((k,x),r)
      Bin _ k x l r   -> let (km,l') = deleteFindMin l in (km,balance k x l' r)
--       Tip             -> (error "Map.deleteFindMin: can not return the minimal element of an empty map", Tip)

deleteFindMax :: Map k a -> ((k,a),Map k a)
deleteFindMax t
  = case t of
      Bin _ k x l Tip -> ((k,x),l)
      Bin _ k x l r   -> let (km,r') = deleteFindMax r in (km,balance k x l r')
--      Tip             -> (error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)
