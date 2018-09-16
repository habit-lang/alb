{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Analyzer.LabeledFields (LabeledFields, desugarLabeledFields, emptyLabeledFields) where

import Control.Monad.State
import Data.Generics
import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)

import Common
import Printer.Common
import Syntax.Surface

-- Map from constructor name to (order of fields in datatype)
type LabeledFields = Map Id [Id]
emptyLabeledFields = Map.empty

type M t = PassM LabeledFields t

desugarLabeledFields :: Has s LabeledFields => Pass s Program Program
desugarLabeledFields = up desugar

desugar :: Pass LabeledFields Program Program
desugar p = do oldLabeledFields <- get
               let lf = Map.union oldLabeledFields newLabeledFields
               put lf
               everywhereM (mkM (rewriteExpr lf) `extM` rewritePattern lf)
                           p{ instances = build (datatypes p) ++ instances p }
    where newLabeledFields = collect (datatypes p)


rewriteExpr :: LabeledFields -> Located Expr -> M (Located Expr)
rewriteExpr lf e@(At loc (EUpdate conE@(At _ (ECon conid)) fs)) =
    case Map.lookup conid lf of
      Nothing -> return e
      Just fields ->
          case fieldsFor fs fields of
            Left label -> failAt loc (failWith ("Missing value for field" <+> ppr label))
            Right es   -> return (foldl eapp conE es)

    where fieldFor [] label = Left label
          fieldFor ((At _ label', e) : rest) label
              | label == label' = Right e
              | otherwise       = fieldFor rest label
          fieldsFor fs = mapM (fieldFor fs)
          eapp f e = at f (EApp f e)
rewriteExpr lf e = return e

rewritePattern :: LabeledFields -> Located Pattern -> M (Located Pattern)
rewritePattern lf p@(At loc (PLabeled conid ps)) =
    case Map.lookup conid lf of
      Nothing -> return p
      Just fields -> return (foldl papp (At loc (PCon conid)) (map (patternFor ps) fields))
    where patternFor [] _ = introduced PWild
          patternFor (At _ (FieldPattern label' p) : rest) label
              | label == label' = p
              | otherwise = patternFor rest label
          papp q p = at q (PApp q p)
rewritePattern _ p = return p

collect :: [Located Datatype] -> LabeledFields
collect = Map.fromList . concatMap collect'
    where collect' (At _ (Datatype _ ctors _ _)) = concat (map fields ctors)
          fields (Ctor (At _ name) _ _ fields) =
              case mapM fieldFrom fields of
                Nothing -> []
                Just fs -> [(name, fs)]
          fieldFrom (At _ (DataField label _)) = label


build :: [Located Datatype] -> [Located Instance]
build = concatMap builder
    where builder (At loc (Datatype t ctors _ _))
              | null labels = []
              | otherwise = map (At loc . selInstFor) labels ++ map (At loc . updInstFor) labels
              where ctorLabels (Ctor _ _ _ fields) = catMaybes [label | At _ (DataField label _) <- fields]
                    labels = nub (concatMap ctorLabels ctors)
                    selEqnFor field ctor@(Ctor (At loc name) _ _ _)
                        | field `elem` ctorLabels ctor =
                            [(At loc (PVar "select") `papp` At loc (PLabeled name [At loc (FieldPattern field (At loc (PVar field)))]) `papp` At loc PWild) :=
                             Unguarded (At loc (EVar field)) Nothing]
                        | otherwise = []
                    selInstFor field =
                        Instance
                            [(([] :=> At loc (Pred (At loc (TyCon "Select") @@ t @@ At loc (TyLabel field) @@ fieldType) Nothing Holds)),
                              (Just emptyDecls{ equations = concatMap (selEqnFor field) ctors }))]
                        where fieldType = head (concat (map typeFrom ctors))
                              typeFrom (Ctor _ _ _ fields) = [t | At _ (DataField (Just label) t) <- fields, label == field]
                    updEqnFor field ctor@(Ctor (At loc name) _ _ _)
                        | field `elem` labels =
                            [(At loc (PVar "update") `papp` (foldl papp (At loc (PCon name)) patterns) `papp` At loc PWild `papp` At loc (PVar field)) :=
                                Unguarded (foldl eapp (At loc (ECon name)) exprs) Nothing]
                        | otherwise = []
                        where labels = ctorLabels ctor
                              patterns = [if field == thisField then At loc PWild else At loc (PVar thisField) | thisField <- labels]
                              exprs    = map (At loc . EVar) labels
                    updInstFor field =
                        Instance
                            [([] :=> At loc (Pred (At loc (TyCon "Update") @@ t @@ At loc (TyLabel field)) Nothing Holds),
                              Just emptyDecls{ equations = concatMap (updEqnFor field) ctors })]

                    t @@ u = at t (TyApp t u)
                    papp q p = at q (PApp q p)
                    eapp f e = at f (EApp f e)
                    infixl 5 @@, `papp`, `eapp`
