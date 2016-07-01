module Fidget.CollectExterns(collectExterns) where

import Common
import Syntax.Common
import Data.List
import Fidget.AST

collectExterns :: Pass () Program Program
collectExterns = pure f where
  f p@(Program functions main globals init tconenv areas structs) =
    (Program functions' main globals init tconenv areas structs) where
      functions' = [i | i@(_, Internal _) <- functions] ++
                   [(fromString id, External id ty (id `elem` inline_prims)) | (id, ty) <- nub (program p)]
                   -- TODO: check that externals have consistent signatures
                   -- TODO: what number for external?  Do we need to keep C vs fidget names?

inline_prims = [
  "__builtin_volatile_read_int8unsigned",
  "__builtin_volatile_read_int16unsigned",
  "__builtin_volatile_read_int32",
  "__builtin_volatile_write_int8unsigned",
  "__builtin_volatile_write_int16unsigned",
  "__builtin_volatile_write_int32"]

ftyp (Funit) = error "Unsupported extern type"
ftyp (Fint) = CMInt
ftyp (Ftcon _) = error "Unsupported extern type"
ftyp (Frecordt _ _) = error "Unsupported extern type"
ftyp (Ffun _ _) = error "Unsupported extern type"
ftyp (Fix _) = CMInt
ftyp (Fref a) = CMInt {- really a pointer -}

fsignature (Fsignature args Funit) = CMSig (map ftyp args) Nothing
fsignature (Fsignature args ret) = CMSig (map ftyp args) (Just $ ftyp ret)

simpl_expr (Scall signature (TFexternal name) _) = [(name, fsignature signature)]
simpl_expr _ = []

expr (Eatom _) = []
expr (Elet lhs ty rhs body) = simpl_expr rhs ++ expr body
expr (Eletrec bindings body) = concatMap (\(_, f) -> function f) bindings ++ expr body
expr (Eifthenelse _ e1 e2) = expr e1 ++ expr e2
expr (Ecase _ clauses def_clause) = concatMap (\(_,_,e) -> expr e) clauses ++ maybe [] (expr . snd) def_clause
expr (Eixcase _ _ _ e1 e2) = expr e1 ++ expr e2
expr (Eerror _) = []
expr (Eletlabel (_,_,e1) e2) = expr e1 ++ expr e2
expr (Egoto _ _ _) = []

function (Function _ _ e) = expr e

fundec (Internal func) = function func
fundec (External _ _ _) = []

program (Program functions _ _ _ _ _ _) = concatMap (fundec . snd) functions
