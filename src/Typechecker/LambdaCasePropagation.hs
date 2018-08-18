{-# LANGUAGE TupleSections #-}
module Typechecker.LambdaCasePropagation where

import Common
import Control.Monad.State
import Printer.Common (text, vcat)
import Syntax.LambdaCase
import Typechecker.LambdaCase

-- the pattern match compiler outputs a version of LambdaCase where
-- the type annotations on EVars are left undefined. So here we just
-- infer those types and apply them
prop_expr :: Context -> Expr -> TM Expr
prop_expr g (EVar i _) = g (Term i []) >>= \t -> return (EVar i t)
prop_expr _ (EBits n s) = return $ EBits n s
prop_expr _ (ENat i) = return $ ENat i
prop_expr g (ECon i ts _) = g (Term i ts) >>= \t -> return (ECon i ts t)
prop_expr g (EBitCon i es) = EBitCon i `fmap` mapM (prop_field g) es
    where prop_field g (f, e) = do e' <- prop_expr g e
                                   return (f, e')
prop_expr g (EStructInit k fs) = EStructInit k `fmap` mapM (prop_field g) fs
    where prop_field g (f, e) = (f,) `fmap` prop_expr g e
prop_expr g (ELam i t e) =
  do
    e' <- prop_expr (update g (Term i []) t) e
    return $ ELam i t e'
prop_expr g (ELet ds e) =
  do
    ds' <- prop_decls g ds
    g' <- updateDecls ds' g
    e' <- prop_expr g' e
    return $ ELet ds' e'
prop_expr g (ECase e alts) = do e' <- prop_expr g e
                                g' <- prop_alts g alts
                                return $ ECase e' g'
prop_expr g (EApp e1 e2) = do e1' <- prop_expr g e1
                              e2' <- prop_expr g e2
                              return $ EApp e1' e2'
prop_expr g (EBitSelect e f) = flip EBitSelect f `fmap` prop_expr g e
prop_expr g (EBitUpdate e1 f e2) = do e1' <- prop_expr g e1
                                      e2' <- prop_expr g e2
                                      return (EBitUpdate e1' f e2')
prop_expr g (EFatbar e1 e2) = do e1' <- prop_expr g e1
                                 e2' <- prop_expr g e2
                                 return $ EFatbar e1' e2'
-- I'm really not sure about this bit... this is one of the hairy bits
-- in the typechecker, and we're assuming the type annotation on the
-- bind is correct and just propagating it...
prop_expr g e@(EBind i t e1 e2) = do e1' <- prop_expr g e1
                                     e2' <- prop_expr (update g (Term i []) t) e2
                                     return (EBind i t e1' e2')
prop_expr g (EReturn e) = EReturn `fmap` prop_expr g e

prop_decls :: Context -> Decls -> TM Decls
prop_decls g (Decls ds) = do ds' <- prop_decls' g ds
                             return $ Decls ds'

prop_decls' :: Context -> [Decl] -> TM [Decl]
prop_decls' g [] = return []
prop_decls' g (d:ds) = do d' <- prop_decl g d
                          g' <- updateDecl g d'
                          ds' <- prop_decls' g' ds
                          return $ d' : ds'

prop_decl :: Context -> Decl -> TM Decl
prop_decl g (Nonrec defn) = do defn' <- prop_defn g defn
                               return (Nonrec defn')
prop_decl g (Mutual defns) = do defns' <- prop_mutual g defns
                                return $ Mutual defns'


prop_defn :: Context -> Defn -> TM Defn
prop_defn g d@(Defn i t (Left _)) = return d
prop_defn g (Defn i t (Right e)) = do
  e' <- prop_expr g e
  return $ Defn i t (Right e')

prop_mutual :: Context -> [Defn] -> TM [Defn]
prop_mutual g ds = mapM (prop_defn g') ds
    where g' = foldr (\(Defn i t _) g -> update g (Term i []) t) g ds

{-
prop_mutual g [] = return []
prop_mutual g (d@(Defn i t e) :ds) = let recg = update g (Term i []) t
                                   in do d' <- prop_defn recg d
                                         g' <- updateDefn recg d'
                                         ds' <- prop_mutual g' ds
                                         return $ d' : ds'
-}

prop_alts :: Context -> [Alt] -> TM [Alt]
prop_alts g alts = mapM (prop_alt g) alts

prop_alt :: Context -> Alt -> TM Alt
prop_alt g (Alt i its ids e) = do cty <- g (Term i its)
                                  let argTs = argTypes cty
                                      g' = foldr (\(i',t) g -> update g (Term i'[] ) t) g $ zip ids argTs
                                  e' <- prop_expr g' e
                                  return $ Alt i its ids e'


prop_topdecl :: Context -> TopDecl -> TM TopDecl
prop_topdecl g (Area i v e t s a) = do e' <- prop_expr g e
                                       return $ Area i v e' t s a
prop_topdecl _ td = return td

prop_program :: Program -> TM Program
prop_program (Program ds tds) = do g <- buildTopDecls tds empty
                                   ds' <- prop_decls g ds
                                   g' <- updateDecls ds' g
                                   tds' <- mapM (prop_topdecl g') tds
                                   return $ Program ds' tds'

propagateLCTypes :: Pass () Program Program
propagateLCTypes p = case prop_program p of
                       Ok p -> return p
                       Errs errss -> failWith (vcat (map (vcat . map text) errss))

-- for testing
prop :: Program -> String
prop p = case prop_program p of
  Ok _ -> "Success"
  Errs s -> unlines $ map unlines s
