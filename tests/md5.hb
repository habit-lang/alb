-- An MD5 library + basic test.  NOTES:

-- * The 'Finalize' is probably wrong.  There should be a particular
--   amound of padding, I just didn't bother with the correct
--   calculation.
--
-- * I use 'List Bit32' as my input.  This is horrible, but I'm not sure what
--   would be better.  Perhaps, if we assume all incoming data is placed in a
--   static (compile time-defined) area then I could just accept an area?  But
--   we run into that not being pure, and this is a pure algorithm.  Mark?  Garrett?
--
-- * This is (still) monadic and really doesn't or shouldn't need to be.
--
-- * Otherwise, this is a mirror of Haskell's pureMD5, which I wrote
--   when I should have been sleeping - so any notion that is correct
--   either is a poor assumption ;-)

requires list
requires miniprelude
requires ondeckprelude
requires largeword
requires io

-- We'll define some basic types:

type Word32 = Bit 32

data MD5Partial = MD5Par Word32 Word32 Word32 Word32

instance Eq MD5Partial where
  (MD5Par a b c d == MD5Par w x y z) = 
         a == w && b == x && c == y && d == z

data MD5Context = MD5Ctx MD5Partial Word32 {- FIXME Word64 -} (List Word32)

-- The final digest is just a context, but we use a different type for
-- safety reasons (so users can't "finalize" the digest twice).

data MD5Digest = MD5Digest MD5Partial
instance Eq MD5Digest where
  (MD5Digest a) == (MD5Digest b) = a == b

md5A :: MD5Digest -> Word32
md5A (MD5Digest (MD5Par a _ _ _)) = a

md5B :: MD5Digest -> Word32
md5B (MD5Digest (MD5Par _ b _ _)) = b

md5C :: MD5Digest -> Word32
md5C (MD5Digest (MD5Par _ _ c _)) = c

md5D :: MD5Digest -> Word32
md5D (MD5Digest (MD5Par _ _ _ d)) = d

-- The initial context values are specified by the MD5 algorithm

md5InitialContext :: () -> MD5Context
md5InitialContext _ = 
  let h0 = 0x67452301
      h1 = 0xEFCDAB89
      h2 = 0x98BADCFE
      h3 = 0x10325476
  in MD5Ctx (MD5Par h0 h1 h2 h3) 0 Nil

-- The number of word32s in each MD5 block
-- *sigh* where have all the top level constants gone
blockSize_words :: () -> Unsigned
blockSize_words _ = 16

-- Ugly MD5-defined constants.  This will hopefully go away with some new habit syntax.

roundShiftList :: () -> List (Ix 32)
roundShiftList _ =
  Cons 7 (Cons 12 (Cons 17 (Cons 22 (Cons 7 (Cons 12 (Cons 17 (Cons 22
  (Cons 7 (Cons 12 (Cons 17 (Cons 22 (Cons 7 (Cons 12 (Cons 17 (Cons 22
  (Cons 5 (Cons 9 (Cons 14 (Cons 20 (Cons 5 (Cons 9 (Cons 14 (Cons 20
  (Cons 5 (Cons 9 (Cons 14 (Cons 20 (Cons 5 (Cons 9 (Cons 14 (Cons 20
  (Cons 4 (Cons 11 (Cons 16 (Cons 23 (Cons 4 (Cons 11 (Cons 16 (Cons 23
  (Cons 4 (Cons 11 (Cons 16 (Cons 23 (Cons 4 (Cons 11 (Cons 16 (Cons 23
  (Cons 6 (Cons 10 (Cons 15 (Cons 21 (Cons 6 (Cons 10 (Cons 15 (Cons 21
  (Cons 6 (Cons 10 (Cons 15 (Cons 21 (Cons 6 (Cons 10 (Cons 15 (Cons 21
  Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

sinConstList :: () -> List Word32
sinConstList _ =
  Cons 3614090360 (Cons 3905402710 (Cons 606105819 (Cons 3250441966
  (Cons 4118548399 (Cons 1200080426 (Cons 2821735955 (Cons 4249261313
  (Cons 1770035416 (Cons 2336552879 (Cons 4294925233 (Cons 2304563134
  (Cons 1804603682 (Cons 4254626195 (Cons 2792965006 (Cons 1236535329
  (Cons 4129170786 (Cons 3225465664 (Cons 643717713 (Cons 3921069994
  (Cons 3593408605 (Cons 38016083 (Cons 3634488961 (Cons 3889429448
  (Cons 568446438 (Cons 3275163606 (Cons 4107603335 (Cons 1163531501
  (Cons 2850285829 (Cons 4243563512 (Cons 1735328473 (Cons 2368359562
  (Cons 4294588738 (Cons 2272392833 (Cons 1839030562 (Cons 4259657740
  (Cons 2763975236 (Cons 1272893353 (Cons 4139469664 (Cons 3200236656
  (Cons 681279174 (Cons 3936430074 (Cons 3572445317 (Cons 76029189
  (Cons 3654602809 (Cons 3873151461 (Cons 530742520 (Cons 3299628645
  (Cons 4096336452 (Cons 1126891415 (Cons 2878612391 (Cons 4237533241
  (Cons 1700485571 (Cons 2399980690 (Cons 4293915773 (Cons 2240044497
  (Cons 1873313359 (Cons 4264355552 (Cons 2734768916 (Cons 1309151649
  (Cons 4149444226 (Cons 3174756917 (Cons 718787259 (Cons 3951481745
  (Nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

area roundShift <- (initArray (\ix -> initStored ((roundShiftList ()) !! (unsigned ix)))) :: ARef 1 (Array 64 (Stored (Ix 32)))

area sinConst <- (initArray (\ix -> initStored ((sinConstList ()) !! (unsigned ix)))) :: ARef 1 (Array 64 (Stored Word32))

readRef' :: NumLit 0 x => ARef 1 (Array 64 (Stored x)) -> Unsigned -> M x
readRef' arr i =
  case maybeIx i of
    Nothing -> return 0
    Just i' -> readRef (arr @ i')

-- It would be nice to generalize this to `Bit n` but that would
-- require reification to figure out (n - x) in computing the lower
-- bits.
rotateL :: Word32 -> Ix 32 -> Word32
rotateL b 0 = b
rotateL b x =
  let h = b `bitShiftL` x
      l = b `bitShiftR` modIx (32 - unsigned x)
  in h .|. l

applyMD5Round :: List Word32 -> MD5Partial -> Unsigned -> M MD5Partial
applyMD5Round w (MD5Par a b c d) r
   | r <= 15 = do
               rs <- readRef' roundShift r
               sc <- readRef' sinConst r
               let j  = r
                   b' = ff a b c d (w!!j) rs sc
               return (MD5Par d b' b c)
   | r <= 31 = do
               rs <- readRef' roundShift r
               sc <- readRef' sinConst r
               let j  = (5*r + 1) `rem` blockSize_words ()
                   b' = gg a b c d (w!!j) rs sc
               return (MD5Par d b' b c)
   | r <= 47 = do
               rs <- readRef' roundShift r
               sc <- readRef' sinConst r
               let j  = (3*r + 5) `rem` blockSize_words ()
                   b' = hh a b c d (w!!j) rs sc
               return (MD5Par d b' b c)
   | True    = do
               rs <- readRef' roundShift r
               sc <- readRef' sinConst r
               let j  = (7*r) `rem` blockSize_words ()
                   b' = ii a b c d (w!!j) rs sc
               return (MD5Par d b' b c)
  where
       f x y z = (x .&. y) .|. ((not x) .&. z)
       g x y z = (x .&. z) .|. (y .&. (not z))
       h x y z = (x .^. y .^. z)
       i x y z = y .^. (x .|. (not z))
       ff :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> (Ix 32) -> Word32 -> Word32
       ff a b c d x s ac =
               let a' = f b c d + x + a + ac
                   a'' = a' `rotateL` s
               in a'' + b
       gg a b c d x s ac =
               let a' = g b c d + x + a + ac
                   a'' = a' `rotateL` s
               in a'' + b
       hh a b c d x s ac =
               let a' = h b c d + x + a + ac
                   a'' = a' `rotateL` s
                   in a'' + b
       ii a b c d  x s ac =
               let a' = i b c d + x + a + ac
                   a'' = a' `rotateL` s
               in a'' + b

succ x = x + 1

-- Belongs in some 'base' library, no?  Would anyone object if I/we
-- started to cobble together some base modules?
foldM :: Proc m => (a -> b -> m a) -> a -> List b -> m a
foldM f i Nil = return i
foldM f i (Cons x xs) = do
      i' <- f i x
      foldM f i' xs

applyMD5Rounds :: MD5Partial -> List Word32 -> M MD5Partial
applyMD5Rounds par w = foldM (applyMD5Round w) par (iterate (64 :: Unsigned) succ 0)

-- The algorithm is just a sum of the components of the current state along
-- with the rounds result of the new state.  it assumes 'dat' is at least 16 words long!

performMD5Update :: MD5Partial -> List Word32 -> M MD5Partial
performMD5Update par@(MD5Par a b c d) dat = do
    par' <- applyMD5Rounds par dat
    case par' of
        MD5Par a' b' c' d' -> return (MD5Par (a' + a) (b' + b) (c' + c) (d' + d)) 

-- blockAndDo will execute and MD5 round on each block of 512 bits (16 Word32's).

blockAndDo :: MD5Partial -> List Word32 -> M MD5Partial
blockAndDo ctx Nil = return ctx
blockAndDo ctx dat = do
   new <- performMD5Update ctx dat
   blockAndDo new (drop (blockSize_words ()) dat)

-- The "md5Update" routine is the workhorse of the MD5 algorithm,
-- compressing all input into our "MD5Context" which is eventually
-- finalized.
--
-- md5Update specifically adjusts the totalLength value, all suboperations
-- do not maintain that information.

md5Update :: MD5Context -> List Word32 -> M MD5Context
md5Update (MD5Ctx p totLen end) dat =
   let len   = length end + length dat
       nr    = len - (len `rem` blockSize_words ())
       input = append end dat
       blksRem = splitAt nr input
   in case blksRem of
	(Nil, remainder) -> return (MD5Ctx p totLen remainder)
        (blks, remainder) -> do
            new <- blockAndDo p blks
            return (MD5Ctx new (totLen + 64) remainder)

-- Finalization converts a running context into the desired result (a digest)

md5Finalize :: MD5Context -> M MD5Digest
md5Finalize (MD5Ctx par totLen end) = do
   let l = 4 * length end
       totLen' = 8 * (totLen + toBits l) -- FIXME LargeWord (toBits l) 0) -- in bits
       lenZeroPad = -- In BYTES
              (if (l + 1) <= 64 - 8
                       then (64 - 8) - (l + 1) else (2*64 - 8) - (l + 1)) - 3
       pad :: List Word32
       pad = Cons 0x80 (iterate (lenZeroPad `div` 4) (const 0) 0)
       w64l :: Word32
       w64l = totLen' -- FIXME loPart totLen'
       w64h :: Word32
       w64h = 0 -- FIXME hiPart totLen'
       lenTail = Cons w64l (Cons w64h Nil)
       paddedEnd =
                 concat (
                 Cons end (           -- l bytes
                 Cons pad (           -- (64 - 8) - (l + 1) or (120 - (l + 1))
                 Cons lenTail Nil)))  -- 8 bytes
   p <- blockAndDo par paddedEnd
   return (MD5Digest p)

-- A wrapper function of use any time you have
-- all data needing hashed at the same time.
md5 :: List Word32 -> M MD5Digest
md5 lst = do
  ctx <- md5Update (md5InitialContext ()) lst
  md5Finalize ctx

printMD5 :: MD5Digest -> M ()
printMD5 (MD5Digest (MD5Par a b c d)) = do
  putHexInt (swapEndian (unsigned a))
  putHexInt (swapEndian (unsigned b))
  putHexInt (swapEndian (unsigned c))
  putHexInt (swapEndian (unsigned d))
  return ()
