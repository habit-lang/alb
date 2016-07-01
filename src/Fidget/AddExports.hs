{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Fidget.AddExports (addExports) where

-- Creates wrapper functions for exported functions that allow C code to call into Habit

import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.List
import qualified Data.Map as Map

import Common
import Printer.Common ((<+>), text)
import Printer.Surface
import Syntax.Common
import Fidget.AST hiding (Id)

import Debug.Trace
import Fidget.Pretty

type M a = PassM () a

addExports :: String -> [(Id, Id)] -> Bool -> Pass () Program Program
addExports prefix xs print (Program gs fs main init tcon areas structs) = do
  exports <- mapM (uncurry (addExport' prefix print fs)) xs
  return (Program gs (fs++exports) main init tcon areas structs)

addExport' :: String -> Bool -> [(Id, Fundec)] -> Id -> Id -> M (Id, Fundec)
addExport' prefix print funcs id id' = do
  let prefixId = fromString (prefix ++ fromId id)
  case lookup prefixId funcs of
    Nothing -> failWith $ text $ "Attempt to export undefined function '"++fromId id++"'"
    Just (External _) -> failWith $ text $ "Attempt to export primitive function '"++fromId id++"'"
    Just (Internal (Function args ret _)) -> do
      (args', ret', e, sig) <- addExport (Ffun (map snd args) ret) prefixId True
      when print $ warn (text $ "extern unsigned "++fromId id'++"(void * /*gc roots*/"++sig++");")
      return (id', Internal (Function args' ret' e))

addExport :: Ftyp -> Id -> Bool -> M ([(Id, Ftyp)], Ftyp, Expr, String)
addExport (Ffun args ret) id top = do
  f <- fresh "f"
  args1 <- mapM (\arg -> liftM2 (,) (fresh "x") (return arg)) args
  (args2, ret0, e, sig) <- addExport ret f False
  let call | top       = Scall (Fsignature args ret) id
           | otherwise = Sapp (Fsignature args ret) (Avar id (Ffun args ret))
  let show_arg arg = ", unsigned /*"++show (snd arg)++"*/"
  return (args1++args2, ret0, Elet f ret (call (map (uncurry Avar) args1)) e, (concatMap show_arg args1)++sig)
addExport t id _ = return ([], t, Eatom (Avar id t), "")
