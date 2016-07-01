requires miniprelude
requires ondeckprelude
requires list
requires test

readRef' :: ARef 1 (Stored (Bit 32)) -> M Unsigned
readRef' a = do 
           i <- readRef a
           return (fromBits i)

writeRef' :: ARef 1 (Stored (Bit 32)) -> Unsigned -> M ()
writeRef' a i = writeRef a (toBits i)

mapM :: Proc m => (a -> m b) -> List a -> m (List b)
mapM f Nil = return Nil
mapM f (Cons x xs) = do
            b <- f x
            bs <- mapM f xs
            return (Cons b bs)

mapM_ :: Proc m => (a -> m b) -> List a -> m ()
mapM_ f xs = mapM f xs >>= (\ x -> return ()) 

forM :: Proc m => List a -> (a -> m b) -> m ()
forM xs f = mapM_ f xs

area mt <- (initArray (const 0)) :: ARef 1 (Array 624 (Stored (Bit 32)))
area ix <- nullInit              :: ARef 1 (Stored (Ix 624))

enum :: Unsigned -> Unsigned -> List Unsigned
enum l u | l > u = Nil
         | True = Cons l (enum (1 + l) u)

fromJust :: Maybe a -> a
fromJust (Just i) = i

initGenerator :: Unsigned -> M ()
initGenerator seed = do
    writeRef' (mt @ 0) seed
    forM (enum 1 623) (\i -> do
                         x <- readRef' (mt @ (modIx (i - 1)))
                         let x' = bitShiftR x 30
                         let x'' = 1812433253*(x .^. x') + i 
                         writeRef' (mt @ (modIx i)) x'')

guard :: Bool -> M () -> M ()
guard True m = m
guard False m = return ()

extractNum :: M Unsigned
extractNum = do
  i <- readRef ix
  guard (i == 0) (generateNums ())
  y <- readRef' (mt @ i)
  let y1 = y .^. (bitShiftR y 11)
      y2 = y1 .^. (bitShiftL y1 7 .&. 2636928640)
      y3 = y2 .^. (bitShiftL y2 15 .&. 4022730752)
      y4 = y3 .^. (bitShiftR y3 18)
      i' = case incIx i of 
             Just new_ix -> new_ix
             Nothing -> 0
  writeRef ix i'
  return y4

generateNums :: () -> M ()
generateNums _ = forM (enum 0 623) (\i -> do
                                       mt1 <- readRef' (mt @ (modIx i))
                                       mt2 <- readRef' (mt @ (modIx (i + 1)))
                                       let y = (bit 31 .&. mt1) .|. (clearBit mt2 31)
                                       mt3 <- readRef' (mt @ (modIx (i + 397)))
                                       let mti = (mt3 .^. (bitShiftR y 1))
                                           mti' = if odd y 
                                                     then mti .^. 2567483615
                                                     else mti
                                       writeRef' (mt @ modIx i) mti')

main' :: M (List Unsigned)
main' = do
     initGenerator 0
     x1 <- extractNum
     x2 <- extractNum
     x3 <- extractNum
     x4 <- extractNum
     return (Cons x1 (Cons x2 (Cons x3 (Cons x4 Nil))))

main :: M Unsigned
main = do
  x <- runTests (Cons (equalM (Cons 2357136044 (Cons 2546248239 (Cons 3071714933 (Cons 3626093760 Nil))))
                              main') Nil)
  return x
