> {-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

Monadic compilation for Habit
=============================

We adapt a monadic intermediate language, and its compilation scheme, from the HASP project to the
(eventually entire) Habit language.  This pass essentially combines the existing pattern-match
compilation and MIL compilation passes.  They're combined here on the grounds that eliminating an
intermediate language simplifies the overall compiler structure, and that we preserve the structure
of matches.

Relationship to mon6.lhs
------------------------

Differences between the source language for mon6.lhs (henceforth LCish) and monomorphic XMPEG:

 - LCish seems to omit a number of the (low-level) feature of Habit:

     * Bitdata types/Binary constants
     * Structs and struct types
     * Areas

   On the other hand, perhaps these should have been compiled to constants before reaching LCish.

 - LCish assumes that constructors are fully applied

 - LCish distinguishes (in the AST) between references to local and top-level bindings

 - LCish relies on an expression-level alternative construct for pattern-match failures.

Remaining work
--------------

I'm dividing the work remaining into two categories: fixes to known problems and entirely
unimplemented features.

Unimplemented:
  - Eta-expand primitives?
  - Primitives
  - Structs
  - Areas
  - Mon6 simplification

> module Mon6a where

> import Control.Monad.Reader
> import Control.Monad.Writer hiding ((<>))
> import Data.Bits
> import Data.Char (chr, ord)
> import Data.Either (partitionEithers)
> import Data.Graph (SCC(..), stronglyConnComp)
> import Data.List (nub)
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe (fromMaybe)
> import Data.Word
> import System.IO
> import System.IO.Error

> import Common
> import Printer.Common
> import Printer.Mon6
> import Printer.XMPEG
> import Syntax.Mon6
> import qualified Syntax.Specialized as X
> import qualified Syntax.XMPEG as X
> import qualified Utils.BDD as BDD

Compilation
============

> data TopLevels = TopLevels{ primNames, topLevels :: [Id],
>                             bitdataCtors :: Map Id (BDD.Pat, [X.BitdataField]) }
> newtype CompM t = CompM{ runCompM :: WriterT [Defn PrimImpl] (ReaderT TopLevels Base) t }
>     deriving (Functor, Applicative, Monad, MonadBase, MonadWriter [Defn PrimImpl], MonadReader TopLevels)

Our notion of the free variables of a term excludes the top-level definitions and primitives.

> free :: HasVariables t => t -> CompM [Id]
> free x = do tl <- ask
>             let vs = primNames tl ++ topLevels tl
>             return (filter (`notElem` vs) (nub (freeVariables x)))

We define several convenience functions to both introduce new definitions and generate the 'tail'
for invoking them.

> addBlock :: Code -> CompM Tail
> addBlock c = do b <- fresh "b"
>                 vs <- free c
>                 tell [BlockDefn b vs c]
>                 return (BlockCall b vs)

> addClosure :: [Var] -> Var -> Tail -> CompM Name
> addClosure free param body =
>     do k <- fresh "k"
>        tell [ClosureDefn k free param body]
>        return k

The "abort" continuation used for pattern-match failure.

> abort = BlockCall "abort" []

Compiling expressions
---------------------

The primitive monad: I'm skeptical of preserving monadic-ness into Mon6.  So, instead, the values of
type M t are interpreted as () -> t, return is "closure allocation" (not even, it produces a Fun
value), and bind inserts unit applications.

  TODO: Why is this a bad idea?

  TODO: Repeated binds only need a single surrounding thunk.  Introduce some kind of flattenBinds
  operator.

Compilation is defined in terms of 'compile-time continuation', which embeds the result of
compilation into the larger program.

> exprTail :: X.Expr -> (Tail -> CompM Code) -> CompM Code
> exprTail (X.ELamVar v) kt =
>     do prims <- asks primNames
>        if v `elem` prims then kt (PrimCall v []) else kt (Return (Var v))

LC-ish assumed that constructors were fully applied.  We don't require this of MPEG (yet), so the
constructor logic is mostly invoked from the handling of EApp.  ECon nodes are only handled
separately for nullary or unapplied constructors.

> exprTail (X.ECon (X.Inst c _ _)) kt = compileCon c [] kt
> exprTail (X.EBits val size) kt
>     | size <= finiteBitSize bits = kt (Return (Const bits))
>     | otherwise = error "Mon6a.lhs:32"
>     where bits = fromIntegral val
> exprTail (X.ELet (X.Decls ds) e) kt = loop ds
>     where loop [] = exprTail e kt
>           loop (X.Defn name _ (Right (X.Gen [] [] e)) : ds) =
>               exprBinding e $ \w ->
>               do c <- loop ds
>                  return (Bind name (Return (Var w)) c)
> exprTail e@(X.ELam{}) kt = loop xs >>= kt . snd
>     where (params, body) = X.flattenLambda e
>           xs             = map fst params
>           loop []      = do b <- addBlock =<< exprTail body (return . Done)
>                             vs <- free body
>                             return (vs, b)
>           loop (v:vs)  = do (free, b') <- loop vs
>                             let free' = filter (v /=) free
>                             k <- addClosure free' v b'
>                             return (free', ClosAlloc k free')
> exprTail e@(X.EApp _ _) kt =
>     do prims <- asks primNames
>        case op of
>          X.ECon (X.Inst ctor _ _) -> compileCon ctor args kt
>          X.ELamVar x | x `elem` prims -> primLoop x args []
>          _ -> exprBinding op $ \op -> loop op args
>     where (op, args) = X.flattenApp e
>           loop appl [e] = exprBinding e $ \e -> kt (Enter appl e)
>           loop appl (e : es) = do r <- fresh "r"
>                                   c <- loop r es
>                                   exprBinding e $ \e -> return (Bind r (Enter appl e) c)
>           primLoop prim [] xs = kt (PrimCall prim (reverse xs))
>           primLoop prim (e:es) xs = exprBinding e $ \x -> primLoop prim es (x:xs)

> exprTail (X.EMatch m) kt = matchTail abort m kt
> exprTail (X.EBind _ _ _ _ v e k) kt =
>     do u <- fresh "u"
>        exprBinding e $ \ev -> do e <- exprTail k kt
>                                  return (Bind u (DataAlloc "Unit" []) $    -- How to allocate units...
>                                          Bind v (Enter ev u) $
>                                          e)

The polymorphic XMPEG syntax tree actually has quite a bit of junk by this point.

> exprTail (X.ELetVar _) _       = error "Mon6a.lhs:31"
> exprTail (X.EMethod _ _ _ _) _ = error "Mon6a.lhs:33"
> exprTail (X.ELetTypes _ _) _   = error "Mon6a.lhs:34"
> exprTail (X.ESubst _ _ _) _    = error "Mon6a.lhs:35"

Bitdata construction is currently represented in XMPEG by an ECon node applied to the result of a
call to the constructBitdata primitive.  This makes sense as

  (a) Bitdata constructors do not add an extra layer of allocation and tagging, unlike data
      constructors; and,

  (b) constructBitdata is entirely magical, untypable in XMPEG (except by forall a. a) and can only
      be given a semantics by reference to the top-level declarations.

So, in compiling a constructor, we have separate cases for bitdata constructors (for which the
constructor node is essentially the unit function) and data constructors (for which the constructor
node is meaningful).

> compileCon :: Id -> [X.Expr] -> (Tail -> CompM Code) -> CompM Code
> compileCon ctor es kt =
>     do bds <- asks (Map.keys . bitdataCtors)
>        if ctor `elem` bds
>        then case es of
>               [e] -> exprTail e kt
>               _   -> error "Mon6a.lhs:167"
>        else loop es []
>     where loop (e:es) vs = exprBinding e $ \v -> loop es (v:vs)
>           loop [] vs = kt (DataAlloc ctor (reverse vs))


We frequently compile an expression and then immediately bind the result to a variable.  This
function captures that pattern, and attempts to avoid producing blocks of the form

    v <- w
    M[v]

instead producing

    M[w]

> exprBinding :: X.Expr -> (Var -> CompM Code) -> CompM Code
> exprBinding (X.ELamVar v) kv = kv v
> exprBinding e kv             = exprTail e $ \t ->
>                                do r <- fresh "r"
>                                   c <- kv r
>                                   return (Bind r t c)

Compiling matches
-----------------

The first argument is the 'abort' continuation to be used in case of failure.

> matchTail :: Tail -> X.Match -> (Tail -> CompM Code) -> CompM Code
> matchTail a X.MFail kt = kt a
> matchTail a (X.MCommit e) kt = exprTail e kt

This implements the following MPEG transformation

     (let Ds => M | M')  ==>  let Ds => (M | M')

This probably ought to be part of a more general treatment of `let` guards; we capture it as a
special case now because it appears in the translation of `if`.

> matchTail a (X.MElse (X.MGuarded (X.GLet ds) m) m') kt =
>     matchTail a (X.MGuarded (X.GLet ds) (X.MElse m m')) kt

We flatten collections of |'d matches and treat them as a unit; independent `p <- x => M` matches
are treated as their singleton case.

> matchTail a m@(X.MElse _ _) kt = pmc a (X.flattenElses m) kt
> matchTail a m@(X.MGuarded (X.GFrom _ _) _) kt = pmc a [m] kt
> matchTail a (X.MGuarded (X.GLet (X.Decls ds)) m) kt = loop ds
>     where loop [] = matchTail a m kt
>           loop (X.Defn name _ (Right (X.Gen [] [] e)) : ds) =
>               exprBinding e $ \w ->
>               do c <- loop ds
>                  return (Bind name (Return (Var w)) c)

This next bit is based on pattern-match compilation...

We begin by splitting groups of alternatives according to their scrutinee variable.  We assume that
each collection of alternatives includes at least one pattern-guarded match.  This seems likely: we
only enter pattern match compilation upon finding a pattern-guarded match (see matchTail), and we
should only start looking for a new group of elses upon finding another pattern-guarded match.  To
avoid producing collections of matches that will confuse buildCaseStatement, we inline trivial
guards (either of the form y <- x => m or _ <- x => m) before grouping elses.

There is a remaining design decisition around what to do with matches like

    (p <- x => M | let Ds => p' <- x => M')

We could either compile this as two case blocks, in which the first has a default branch to jump to
the Ds definitions and the second case block, or as one case block in which the Ds pushed into M':

    (let Ds => p <- x => M)  ==>  (p <- x => let Ds => M)    (x not bound by Ds)
    (let Ds => (M | M'))  ==> (let Ds => M | let Ds => M')

We currently take the former approach; I think the latter approach might be 'better', but as it
doesn't seem to correspond to the output of the compiler, I'm not terribly concerned about
implementing it as yet.

> partitionElses :: [X.Match] -> [(Maybe X.Decls, [X.Match])]
> partitionElses [] = []
> partitionElses (m@(X.MGuarded (X.GFrom _ y) _) : ms) = (Nothing, m : these) : partitionElses rest
>     where (these, rest) = loop y ms
>           loop x [] = ([], [])
>           loop x (X.MGuarded (X.GFrom (X.PVar z _) y) m : ms) =
>               loop x (rename [(z, y)] m : ms)
>           loop x (X.MGuarded (X.GFrom X.PWild y) m : ms) =
>               loop x (m : ms)
>           loop x ms'@(m@(X.MGuarded (X.GFrom _ y) _) : ms)
>               | x == y = let (these, rest) = loop x ms
>                          in (m : these, rest)
>               | otherwise = ([], ms')
>           loop x (ms@(X.MGuarded (X.GLet _) _ : _)) = ([], ms)
>           loop x (m@(X.MCommit e) : ms) = (m : these, rest)
>               where (these, rest) = loop x ms
>           loop x ms = error ("Mon6a.lhs:117:" ++ show (ppr (foldl1 X.MElse ms)))
> partitionElses (X.MGuarded (X.GLet ds) m : ms) = (Just (maybe ds (X.appendDecls ds) ds'), ms') : rest
>     where ((ds', ms') : rest) = partitionElses (m : ms)
> partitionElses (m:ms) = error ("Mona.lhs:138:" ++ show (ppr m))


Given a group of matches guarded by the same scrutinee, we can build a Mon6 base branch.  The
initial tail is the 'outer' abort continuation.

> buildCaseStatement :: Tail -> (Maybe X.Decls, [X.Match]) -> (Tail -> CompM Code) -> CompM Code
> buildCaseStatement a (mdecls, alts@(X.MGuarded (X.GFrom _ x) _ : _)) kt = loop defns
>     where (branches, def) = coalesceBranches (map classifyBranch alts)
>           defns = case mdecls of
>                     Nothing -> []
>                     Just (X.Decls ds) -> ds
>           loop (X.Defn name _ (Right (X.Gen [] [] e)) : ds) =
>               exprBinding e $ \w ->
>               do c <- loop ds
>                  return (Bind name (Return (Var w)) c)
>           loop [] = do r <- fresh "r"
>                        join <- addBlock =<< kt (Return (Var r))
>                        def' <- case def of
>                                  Nothing -> return a
>                                  Just m  -> addBlock =<< matchTail a m (\t -> return (Bind r t (Done join)))
>                        alts' <- mapM (compAlt def' r join) branches
>                        case alts' of
>                          (Left _ : _) -> return (Case x (map fromLeft alts') def')
>                          (Right _ : _) -> return (BitCase x (map fromRight alts') def')
>                          _ -> return (Done def')
>               where fromLeft (Left x)   = x
>                     fromLeft _          = error "Mon6a.lhs:305"
>                     fromRight (Right x) = x
>                     fromRight _         = error "Mon6a.lhs:307"

Detect 'default' branches, either because they have trivially satisfied guards `(y <- x => M)` or no
guards at all.

>           classifyBranch (X.MGuarded (X.GFrom (X.PCon (X.Inst ctor _ _) vs) _) m) = Right (ctor, vs, m)
>           classifyBranch (X.MGuarded (X.GFrom (X.PVar y _) _) m) = Left (rename [(x, y)] m)
>           classifyBranch (X.MGuarded (X.GFrom (X.PWild) _) m) = Left m
>           classifyBranch m = Left m

Combine branches with the same constructor.

>           coalesceBranches [] = ([], Nothing)
>           coalesceBranches (Left m : bs) = ([], Just m)
>           coalesceBranches (Right (ctor, vs, m) : Right (ctor', vs', m') : rest)
>               | ctor == ctor' = coalesceBranches (Right (ctor, vs, X.MElse m (rename (zip vs vs') m')) : rest)
>           coalesceBranches (Right b : bs) = (b : alts, def)
>               where (alts, def) = coalesceBranches bs

>           compAlt def' r join (ctor, vs, m) =
>               do u' <- matchTail def' m (\t -> return (Bind r t (Done join)))
>                  t' <- addBlock u'
>                  bs <- asks bitdataCtors
>                  case Map.lookup ctor bs of
>                    Nothing -> return (Left (ctor, vs, t'))
>                    Just (pat, _) -> return (Right (pat, head vs, t'))

Finally, we can build mini-pattern match compilation out of the above.

> pmc :: Tail -> [X.Match] -> (Tail -> CompM Code) -> CompM Code
> pmc a ms kt = buildCaseStatements a bss kt
>     where bss = partitionElses ms
>           buildCaseStatements a [bs] kt = buildCaseStatement a bs kt
>           buildCaseStatements a (bs : bss) kt =
>               do r <- fresh "r"
>                  join <- addBlock =<< kt (Return (Var r))
>                  let kt' t = return (Bind r t (Done join))
>                  a2 <- addBlock =<< buildCaseStatements a bss kt'
>                  buildCaseStatement a2 bs kt'

Primitives
----------

> type PrimImpl = [Val] -> (Val -> RunM Val) -> RunM Val

> askBitdataFields :: Id -> CompM [X.BitdataField]
> askBitdataFields ctorName =
>     asks (snd . fromMaybe (error ("Unknown bitdata constructor " ++ show (ppr ctorName))) .
>           Map.lookup ctorName .
>           bitdataCtors)

> constructBitdata :: [X.Type] -> CompM PrimImpl
> constructBitdata [t] =
>     do fields <- askBitdataFields ctorName
>        return (build fields)
>     where X.TyApp (X.TyApp (X.TyCon (Kinded (Ident "BitdataCase" _ _) _)) _) (X.TyLabel ctorName) = resultType t
>           resultType (X.TyApp (X.TyApp (X.TyCon (Kinded (Ident "->" _ _) _)) _) t) =
>               resultType t
>           resultType t = t
>           build fields bs k = k (U (foldl (.|.) 0 (iter fields bs)))
>               where iter [] _ = []
>                     iter (X.LabeledField _ _ p offset : fs) (U b : bs) = ((b .&. mask) `shiftL` offset) : iter fs bs
>                         where width = BDD.width p
>                               mask = complement (-1 `shiftL` fromIntegral width)
>                     iter (X.ConstantField b p offset : fs) bs = ((fromIntegral b .&. mask) `shiftL` offset) : iter fs bs
>                         where width = BDD.width p
>                               mask = complement (-1 `shiftL` fromIntegral width)

> bitdataSelect :: [X.Type] -> CompM PrimImpl
> bitdataSelect [_, X.TyLabel ctorName, X.TyLabel fieldName, _] =
>     do fields <- askBitdataFields ctorName
>        let (pat, offset) = loop fields
>                where loop [] = error ("Unknown bitdata field " ++ fromId fieldName ++ " in constructor " ++ fromId ctorName)
>                      loop (X.LabeledField field' _ pat offset : fs)
>                          | field' == fieldName = (pat, offset)
>                      loop (_ : fs) = loop fs
>            mask = complement (-1 `shiftL` BDD.width pat)
>            select [U b, _] k = k (U ((b `shiftR` offset) .&. mask))
>        return select

Remaining primitives to be written (based on previous version):

  Areas:
     initStored
     initArray
     primWriteRefM
     primReadRefM
     @@

  I/O (for testing):
     getchar
     putchar
     fflush

> primitives :: [(String, [X.Type] -> PrimImpl)]
> primitives =
>     [-- In-build monad
>      ("primReturnM",
>       \[_] [v] k -> k (Fun [("$x", v)] "$y" (Return (Var "$x")))),

>      -- Bitdata and bit vectors
>      ("primBitdataEquals",
>       \[_, X.TyNat size] [U b, U b'] k ->
>           let mask = complement (-1 `shiftL` fromIntegral size)
>           in if (b .&. mask) == (b' .&. mask) then k true else k false),
>      ("primEqBit",
>       \[X.TyNat size] [U left, U right] k ->
>           let mask = complement (-1 `shiftL` fromIntegral size)
>           in if (left .&. mask) == (right .&. mask) then k true else k false),
>      ("primCompareBit",
>       \[X.TyNat size] [U left, U right] k ->
>           let mask = complement (-1 `shiftL` fromIntegral size)
>           in k $ case compare (left .&. mask) (right .&. mask) of
>                    LT -> Con "LT" []
>                    EQ -> Con "EQ" []
>                    GT -> Con "GT" []),
>      (":#",
>       \[_, X.TyNat rightSize, X.TyNat final] [U left, U right] k ->
>           k (U ((left `shiftL` fromIntegral rightSize) .|. right))),
>      -- Arithmetic
>      ("primFromLiteralBit", primFromLiteralBit),
>      ("primBitPlus", bitArith (+)),
>      ("primBitMinus", bitArith (-)),
>      ("primBitTimes", bitArith (*)),
>      -- Booleans
>      ("primBoolAnd",
>       \ [] [U b, U b'] k -> k (U (b .&. b'))),
>      ("primBoolOr",
>       \ [] [U b, U b'] k -> k (U (b .|. b'))),
>      ("primBoolXor",
>       \ [] [U b, U b'] k -> k (U (b `xor` b'))),
>      ("primBoolNot",
>       \ [] [U b] k -> k (U (b `xor` 1))),
>      -- Indexes (at least, small ones)
>      ("primIxFromLiteral",
>       \[X.TyNat val, _] [_] k -> k (U (fromIntegral val))),
>      ("primModIxMod",
>       \[X.TyNat n, _] [U bits] k ->
>           k (U (bits `mod` fromIntegral n))),
>      ("primIxToUnsigned",
>       \[_] [U bits] k -> k (U bits)),
>      ("primIncIx",
>       \[X.TyNat n] [U bits] k ->
>           if bits == fromIntegral n
>           then k (Con "Nothing" [])
>           else k (Con "Just" [U (bits + 1)])),
>      -- I/O (for testing)
>      ("getchar",
>       \ [] [] k -> k (Fun [] "$y" (PrimCall "$getchar" []))),
>      ("$getchar",
>       \ [] [] k -> do c <- liftIO $ tryIOError getChar
>                       case c of
>                         Left e | isEOFError e -> k (U (negate 1))
>                                | otherwise    -> liftIO $ ioError e
>                         Right c               -> k (U (fromIntegral (ord c)))),
>      ("putchar",
>       \ [] [v] k -> k (Fun [("$x", v)] "$y" (PrimCall "$putchar" []))),
>      ("$putchar",
>       \ [] [U v] k -> do liftIO $ putChar (chr (fromIntegral v))
>                          k (U v)),
>      ("fflush",
>       \ [] [] k -> k (Fun [] "$y" (PrimCall "$fflush" []))),
>      ("$fflush",
>       \[] [] k -> do liftIO $ hFlush stdout
>                      k (U 0))
>     ]
>     where false = U 0
>           true = U 1
>           primFromLiteralBit [X.TyNat val, X.TyNat size] [_] k
>               | fromIntegral size <= finiteBitSize bits = k (U bits)
>               | otherwise = error "Mon6a.lhs:464"
>               where mask = complement (-1 `shiftL` fromIntegral size)
>                     bits = fromIntegral val .&. mask
>           bitArith f [X.TyNat size] [U b, U b'] k = k (U (f b b' .&. mask))
>               where mask = complement (-1 `shiftL` fromIntegral size)
>           bitCompare f [X.TyNat size] [U left, U right] k = if f (left .&. mask) (right .&. mask)
>                                                             then k true
>                                                             else k false
>               where mask = complement (-1 `shiftL` fromIntegral size)


Here line primitive implementations from a previous attempt at the interpreter; perhaps they can
serve as guidance while finishing the above.

primitives =
    [-- In-built monad
     ("primReturnM",
      \ [t] ->
        vfun (\v -> vcomp (return v))),
     -- Areas
     ("initStored",
      \ [TyCon (Kinded (Ident "Unsigned" _ _) _)] ->
        vfun $ \v ->
          liftIO (do ref <- newIORef (bytesFromUnsigned v)
                     return (VRef ref))),
     ("initArray",
      \ [TyNat n, elemTy] ->
        vfun $ \(VFun bs f) ->
          VArray `fmap` mapM (inEnv bs . f . VIx) [0..n-1]),
     ("primWriteRefM",
      \ [TyNat align, TyApp (TyCon (Kinded (Ident "Stored" _ _) _)) (TyCon (Kinded (Ident "Unsigned" _ _) _)), TyCon (Kinded (Ident "Unsigned" _ _) _)] ->
        vfun $ \(VRef r) -> vfun $ \v ->
          vcomp $ liftIO (do writeIORef r (bytesFromUnsigned v)
                             return (VCon "Unit" []))),
     ("primReadRefM",
      \ [TyNat align, TyApp (TyCon (Kinded (Ident "Stored" _ _) _)) (TyCon (Kinded (Ident "Unsigned" _ _) _)), TyCon (Kinded (Ident "Unsigned" _ _) _)] ->
        vfun $ \(VRef r) ->
          vcomp $ liftIO (do bs <- readIORef r
                             return (unsignedFromBytes bs))),
     ("@@",
      \ _ ->
      vfun $ \(VArray refs) -> vfun $ \(VIx n) -> return (refs !! fromIntegral n)),
     -- I/O (for testing)
     ("getchar",
      \ [] -> vcomp $ liftIO (do c <- getChar
                                 return (VCon "Unsigned" [VBits (fromIntegral (ord c)) 32]))),
     ("putchar",
      \ [] -> vfun $ \(VCon _ [VBits char _]) -> vcomp $ liftIO (do putChar (chr (fromIntegral char))
                                                                    return (VCon "Unsigned" [VBits 1 32]))),
     ("fflush",
      \ [] -> vfun $ \_ -> vcomp $ liftIO (hFlush stdout >> return (VCon "Unsigned" [VBits 0 32])))] -- Wrong return value?


bytesFromUnsigned :: Value -> [Word8]
bytesFromUnsigned (VCon "Unsigned" [VBits value _]) = makeBytes 4 value
    where makeBytes :: Int -> Integer -> [Word8]
          makeBytes 0 value = []
          makeBytes n value = fromIntegral rem : makeBytes (n - 1) quot
              where (quot, rem) = value `divMod` (2^8)

unsignedFromBytes :: [Word8] -> Value
unsignedFromBytes bs = VCon "Unsigned" [VBits (fromIntegral (fromBytes bs)) 32]
    where fromBytes [] = 0
          fromBytes (v:vs) = v .|. (fromBytes vs `shiftL` 8)


Programs
--------

> compileProgram :: X.Specialized -> CompM Code
> compileProgram (X.Specialized tds [main] (X.Decls decls)) =
>     local (const (TopLevels prims topLevels (Map.fromList bdCtors))) $
>     loop decls >> exprBinding main (\mainv -> do u <- fresh "u"
>                                                  return (Bind u (DataAlloc "Unit" []) $
>                                                          Done (Enter mainv u)))
>     where prims = [name | X.Defn name _ (Left _) <- decls]
>           topLevels = [name | X.Defn name _ (Right _) <- decls]
>           bdCtors = [(name, (pat, fields)) | X.Bitdatatype _ _ ctors <- tds, (name, fields, pat) <- ctors]
>           loop [] = return ()
>           loop (X.Defn name _ (Left (primName, ts)) : ds)
>               | primName == "constructBitdata" =
>                   do impl <- constructBitdata ts
>                      tell [PrimDefn name impl]
>                      loop ds
>               | primName == "bitdataSelect" =
>                   do impl <- bitdataSelect ts
>                      tell [PrimDefn name impl]
>                      loop ds
>               | otherwise =
>                   do tell [PrimDefn name (fromMaybe (error ("Unknown primitive " ++ show (ppr primName))) (lookup primName primitives) ts)]
>                      loop ds
>           loop (X.Defn name _ (Right (X.Gen [] [] e)) : ds) =
>               do b <- addBlock =<< exprTail e (return . Done)
>                  tell [Init name b]
>                  loop ds

> sortDefns :: [Defn t] -> [Defn t]
> sortDefns ds = concatMap fromSCC (stronglyConnComp nodes)
>     where nodes = [(d, nameOf d, reqdBy d) | d <- ds]
>           nameOf (BlockDefn name _ _)        = name
>           nameOf (ClosureDefn name _ _ _)    = name
>           nameOf (Init name _)               = name
>           nameOf (PrimDefn name _)           = name
>           reqdBy (BlockDefn _ _ code)        = calls [] code
>           reqdBy (ClosureDefn _ _ _ _)       = []
>           reqdBy (Init _ tail)               = callsTail [] tail
>           reqdBy (PrimDefn _ _)              = []
>           calls local (Bind x t c)           = callsTail local t ++ calls (x:local) c
>           calls local (Done t)               = callsTail local t
>           calls local (Case _ alts t)        = concat [callsTail (xs ++ local) t | (_, xs, t) <- alts] ++ callsTail local t
>           calls local (BitCase _ alts t)     = concat [callsTail (x : local) t | (_, x, t) <- alts] ++ callsTail local t
>           callsTail local (BlockCall name _) = [name]
>           callsTail local (Enter name _)     = if name `elem` local then [] else [name]
>           callsTail local (Return (Var name)) = if name `elem` local then [] else [name]
>           callsTail _ _                      = []
>           fromSCC (AcyclicSCC d)             = [d]
>           fromSCC (CyclicSCC ds)             = ds

> compile :: Has s () => Pass s X.Specialized (Code, [Defn PrimImpl])
> compile = up body
>     where body :: Pass () X.Specialized (Code, [Defn PrimImpl])
>           body s = PassM (lift (do (c, ds) <- runReaderT (runWriterT (runCompM (compileProgram s))) (TopLevels [] [] Map.empty)
>                                    return (c, sortDefns ds)))

Interpreting Mon6
=================

Of course, none of that's any good if we can't do anything with the generated code.  So, we now
build a simple interpreter for the Mon6 language.

Values include unsigned's (should eventually presumably be some kind of bitdata thing), constructed
values, and functions.

> data Val = U !Word | Con !CFun ![Val] | Fun ![(Var, Val)] !Var !Tail

> instance Printable Val where
>     ppr (U w) = text (show w)
>     ppr (Con c vs) = ppr c <> parens (pprList' vs)
>     ppr (Fun _ _ _) = "<closure>"

We run Mon6 programs in the IO monad (unnecessary for now, but intended to support structs and areas
and the like) with read access to a collection of globals (i.e., the Defn's produced by compilation)
and local values:

> data RunState = RunState{ blocks :: Map Id ([Var], Code),
>                           closures :: Map Id ([Var], Var, Tail),
>                           primImpls :: Map Id PrimImpl,
>                           locals :: [(Var, Val)] }

> newtype RunM t = RunM{ run :: ReaderT RunState IO t }
>     deriving (Functor, Applicative, Monad, MonadReader RunState, MonadIO)

Access to the globals and locals will presuambly be slow, given their representations.  I wonder if
it wouldn't be worth "renumbering" blocks and closures such that they can be stored in arrays, and
using de Bruijn indices (or similar) so that locals can just be kept in a stack, rather than having
to look up names.

The main interpreter loop is written in CPS style, for two reasons. First, I hope this will go some
way to ensuring that we follow the correct evaluation order, without allowing Haskell's laziness to
leak into the semantics of Mon6.  Second, I think it should result in tail calls in Mon6
corresponding to tail calls in the interpreter.

> var :: Var -> RunM Val
> var x = do vs <- asks locals
>            case lookup x vs of
>              Nothing -> error ("Unbound variable: " ++ fromId x ++ " not in " ++ show (pprList' (map (ppr . fst) vs)))
>              Just v  -> return v

          asks (fromMaybe (error ("Unbound variable: " ++ show (ppr x))) . lookup x . locals)

> runTail :: Tail -> (Val -> RunM Val) -> RunM Val
> runTail (Return (Var v)) k = var v >>= k
> runTail (Return (Const b)) k = k (U b)
> runTail (BlockCall "abort" _) _ = error "In Mon6a: Executing abort (probably a pattern match failure)"
> runTail (BlockCall b xs) k =
>     do vs <- mapM var xs
>        (ys, body) <- asks (fromMaybe (error ("Unbound block: " ++ show (ppr b))) . Map.lookup b . blocks)
>        local (\s -> s{ locals = zip ys vs ++ locals s }) (runCode body (local (\s -> s{ locals = drop (length ys) (locals s) }) . k))
> runTail (DataAlloc c xs) k = k =<< (Con c `fmap` mapM var xs)
> runTail (ClosAlloc f xs) k =
>     do vs <- mapM var xs
>        (ys, z, t) <- asks (fromMaybe (error ("Unbound closure: " ++ show (ppr f))) . Map.lookup f . closures)
>        k (Fun (zip ys vs) z t)
> runTail (Enter f x) k =
>     do v <- var f
>        w <- var x
>        case v of
>          Fun closure y body -> local (\s -> s{ locals = (y, w) : closure ++ locals s}) (runTail body (local (\s -> s{ locals = drop (length closure + 1) (locals s)}) . k))
>          _ -> error ("Application of non-function value " ++ show (ppr v))
> runTail (PrimCall n xs) k =
>     do vs <- mapM var xs
>        primitives <- asks primImpls
>        case Map.lookup n primitives of
>          Nothing -> error ("Unknown primitive " ++ show (ppr n))
>          Just f  -> f vs k

> runCode :: Code -> (Val -> RunM Val) -> RunM Val
> runCode (Bind x t c) k = runTail t (\v -> local (\s -> s{ locals = (x,v) : locals s }) (runCode c (local (\s -> s{ locals = tail (locals s) }) . k)))
> runCode (Done t) k = runTail t k
> runCode (Case x alts def) k =
>     do v <- var x
>        case v of
>          Con c vs -> loop c vs alts
>          _        -> error ("Case on non-constructed value: " ++ show (ppr v))
>     where loop _ _ [] = runTail def k
>           loop c vs ((c', xs, body) : alts)
>               | c == c' = local (\s -> s{ locals = zip xs vs ++ locals s }) (runTail body (local (\s -> s{ locals = drop (length xs) (locals s) }) . k))
>               | otherwise = loop c vs alts
> runCode (BitCase x alts def) k =
>     do v <- var x
>        case v of
>          U b -> loop b alts
>          _   -> error ("BitCase on non-bits value: " ++ show (ppr v))
>     where loop _ [] = runTail def k
>           loop b ((pat, x, body) : alts)
>               | pat `BDD.willMatch` fromIntegral b = local (\s -> s{ locals = (x, U b) : locals s }) (runTail body (local (\s -> s{ locals = tail (locals s) }) . k))
>               | otherwise = loop b alts

> runProgram :: (Code, [Defn PrimImpl]) -> IO Val
> runProgram (c, ds) = runReaderT (run (bindInits initsList (runCode c return))) (RunState (Map.fromList blocksList) (Map.fromList closuresList) (Map.fromList primitives) [])
>     where (blocksList, closuresList, initsList, primitives) = foldr partition ([], [], [], []) ds
>           partition (BlockDefn name xs body) (blocks, closures, inits, prims) = ((name, (xs, body)) : blocks, closures, inits, prims)
>           partition (ClosureDefn name xs y body) (blocks, closures, inits, prims) = (blocks, (name, (xs, y, body)) : closures, inits, prims)
>           partition (Init x t) (blocks, closures, inits, prims) = (blocks, closures, (x, t) : inits, prims)
>           partition (PrimDefn name impl) (blocks, closures, inits, prims) = (blocks, closures, inits, (name, impl) : prims)
>           bindInits [] k = k
>           bindInits ((x,t) : bs) k = runTail t (\v -> local (\s -> s{ locals = (x,v) : locals s}) (bindInits bs k))
