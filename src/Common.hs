{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, OverlappingInstances, TemplateHaskell #-}
module Common where

import Prelude hiding ((<$>))

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer (WriterT(..), Writer(..), tell, censor, runWriterT, runWriter, Monoid(..))
import Data.Maybe (fromMaybe)
import Printer.Common
import Syntax.Common
import Text.Parsec (SourcePos, sourceName, sourceLine, sourceColumn)

concatMapM :: (Functor m, Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat `fmap` mapM f xs

mapSndM :: (Functor m, Monad m) => (a -> m b) -> [(c,a)] -> m [(c,b)]
mapSndM f pairs = zip (map fst pairs) `fmap` mapM f (map snd pairs)

----------------------------------------------------------------------------------------------------

data CompilerError = Error (Maybe Location) Doc

instance Error CompilerError
    where noMsg    = Error Nothing (empty)
          strMsg s = Error Nothing (text s)

instance Printable SourcePos
    where ppr p = text (sourceName p) <> colon <> int (sourceLine p)  <> colon <> int (sourceColumn p)

instance Printable Location
    where ppr p = text (show p)

instance Printable CompilerError
    where ppr (Error Nothing d) = d
          ppr (Error (Just p) d) = hang 4 (ppr p <> colon <$> d)

data CompilerWarning = Warning (Maybe Location) Doc

instance Printable CompilerWarning
    where ppr (Warning Nothing d) = "Warning:" <+> d
          ppr (Warning (Just p) d) = hang 4 (ppr p <> colon <$> "Warning:" <+> d)

data SnocList t = Lin | Snoc (SnocList t) t

instance Functor SnocList
    where fmap _ Lin         = Lin
          fmap f (Snoc ts t) = Snoc (fmap f ts) (f t)

instance Monoid (SnocList t)
    where mempty                 = Lin
          mappend ts Lin         = ts
          mappend ts (Snoc us u) = Snoc (mappend ts us) u

toList            :: SnocList t -> [t]
toList tsil = r tsil []
 where r Lin         = id
       r (Snoc st t) = r st . (t:)

type Warnings = [CompilerWarning]

----------------------------------------------------------------------------------------------------

-- The obvious approach at this point would be to use the various MonadX classes with particular
-- values to capture the behavior of compiler passes; unfortunately, given the functional
-- dependencies declared for those classes, such an approach limits the use of monad transformers to
-- build the passes themselves.  Instead, we capture all the base behavior in a class of its own,
-- allowing individual passes free application of transformers to the base monad without introducing
-- conflicting requirements.

class (Functor m, Monad m) => MonadBase m
    where fresh :: Id -> m Id

          getCounter :: m Int
          putCounter :: Int -> m ()

          fresh prefix = do v <- getCounter
                            putCounter (v + 1)
                            return (freshPrefix prefix v)

          failWith             :: Doc -> m t
          warn                 :: Doc -> m ()
          failAt               :: Location -> m t -> m t
          transformFailures    :: (Doc -> Doc) -> m t -> m t

-- I don't know how to make an instance of the form:
--
--   instance (MonadBase m, MonadTrans t, Monad (t m)) => MonadBase (t m)
--
-- work, because I'm not sure how to implement failAt and appendFailureContext only using lift.  So,
-- instead, here are a bunch of fairly rote instances lifting MonadBase through the commonly used
-- monad transformers.

instance MonadBase m => MonadBase (ReaderT r m)
    where fresh x      = lift (fresh x)
          getCounter   = lift getCounter
          putCounter x = lift (putCounter x)

          failWith d            = lift (failWith d)
          warn d                = lift (warn d)
          failAt p c            = ReaderT (\v -> failAt p (runReaderT c v))
          transformFailures d c = ReaderT (\v -> transformFailures d (runReaderT c v))

instance MonadBase m => MonadBase (StateT s m)
    where fresh x      = lift (fresh x)
          getCounter   = lift getCounter
          putCounter x = lift (putCounter x)

          failWith d            = lift (failWith d)
          warn d                = lift (warn d)
          failAt p c            = StateT (\s -> failAt p (runStateT c s))
          transformFailures d c = StateT (\s -> transformFailures d (runStateT c s))

instance (MonadBase m, Monoid w) => MonadBase (WriterT w m)
    where fresh x      = lift (fresh x)
          getCounter   = lift getCounter
          putCounter x = lift (putCounter x)

          failWith d            = lift (failWith d)
          warn d                = lift (warn d)
          failAt p c            = WriterT (failAt p (runWriterT c))
          transformFailures d c = WriterT (transformFailures d (runWriterT c))

----------------------------------------------------------------------------------------------------

newtype Base t = Base (StateT Int (ErrorT CompilerError (Writer (SnocList CompilerWarning))) t)
    deriving (Functor, Applicative, Monad)

runBase :: Base t -> Int -> Either (CompilerError, Warnings) (t, Warnings, Int)
runBase (Base c) z = let (e, ws) = runWriter (runErrorT (runStateT c z))
                         ws'     = toList ws
                     in case e of
                          Left ce       -> Left (ce, ws')
                          Right (t',z') -> Right (t', ws', z')

instance MonadBase Base
    where getCounter   = Base get
          putCounter x = Base (put x)

          failWith d =
              Base (throwError (Error Nothing d))
          warn d =
              Base (tell (Snoc Lin (Warning Nothing d)))
          failAt p (Base c)
              | sourceName (start p) == "<introduced>" =
                  Base c
              | otherwise =
                  Base (censor (fmap addLocation) c
                            `catchError` \(Error mpos err) -> throwError (Error (Just (fromMaybe p mpos)) err))
              where addLocation (Warning mpos msg) = Warning (Just (fromMaybe p mpos)) msg
          transformFailures d (Base c) =
              Base (censor (fmap transform) c
                        `catchError` \(Error mpos err) -> throwError (Error mpos (d err)))
              where transform (Warning mpos msg) = Warning mpos (d msg)

failWithS :: MonadBase m => String -> m t
failWithS s = failWith (text s)

appendFailureContext :: MonadBase m => Doc -> m t -> m t
appendFailureContext d = transformFailures (\d' -> d' <$> indent 4 (hang 4 d))

appendFailureContextS :: MonadBase m => String -> m t -> m t
appendFailureContextS s c = appendFailureContext (text s) c

mapLocated :: MonadBase m => (t -> m u) -> Located t -> m (Located u)
mapLocated f (At loc p) = failAt loc (At loc `fmap` f p)

----------------------------------------------------------------------------------------------------

-- Creates fresh names for a list of values, using the given prefix.
freshFor :: MonadBase m => Id -> [t] -> m [Id]
freshFor prefix vs = replicateM (length vs) (fresh prefix)

----------------------------------------------------------------------------------------------------

newtype PassM st t = PassM { unPass :: StateT st Base t }
    deriving (Functor, Applicative, Monad, MonadState st, MonadBase)

type Pass st a b = a -> PassM st b

runPass :: Pass st a b -> a -> (Int, st) -> Either (CompilerError, Warnings) (b, Warnings, (Int, st))
runPass p a (z, st) = do ((b, st'), ws, z') <- runBase (runStateT (unPass (p a)) st) z
                         return (b, ws, (z', st'))

liftBase :: Base t -> PassM st t
liftBase c = PassM (StateT (\x -> do v <- c; return (v, x)))

localState :: Pass st0 a b -> st0 -> Pass st1 a (b, st0)
localState f s0 x = PassM (StateT (body x))
    where body x s1 = do (y, s0') <- runStateT (unPass (f x)) s0
                         return ((y, s0'), s1)

first :: Pass s t u -> Pass s (t, v) (u, v)
first f (x, y) = PassM (StateT (\s -> do (x', s') <- runStateT (unPass (f x)) s
                                         return ((x', y), s')))

pure :: (a -> b) -> Pass st a b
pure f = return . f

onlyWhen :: Bool -> Pass s t t -> Pass s t t
onlyWhen True p  = p
onlyWhen False _ = return

initial :: s -> Pass s a b -> Pass s' a b
initial s p x = PassM (StateT (\s' -> do (r, _) <- runStateT (unPass (p x)) s
                                         return (r, s')))

--------------------------------------------------------------------------------

class Has s s'
    where up :: Pass s' t u -> Pass s t u

instance Has s s
    where up = id

instance Has (t, s) s
    where up f x = PassM (StateT body)
              where body (t, s) = do (y, s') <- runStateT (unPass (f x)) s
                                     return (y, (t, s'))

instance Has t s => Has (t, s') s
    where up f x = PassM (StateT body)
              where body (t, s) = do (y, t') <- runStateT (unPass (up f x)) t
                                     return (y, (t', s))
