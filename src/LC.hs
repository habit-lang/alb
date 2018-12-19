{-# LANGUAGE FlexibleInstances #-}
module LC (toLC) where

import Common
import Printer.Common
import Printer.XMPEG ()
import Syntax.MangleIds
import Syntax.Specialized
import Utils.BDD

import Control.Monad
import Data.Bits
import Data.Char (isAlpha, isSpace)
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Prelude hiding ((<$>))

import Debug.Trace


type CtorEnv = Map (Id, [Type]) Id
type TypeEnv = Map Type Id
type Envs = (CtorEnv, TypeEnv)

class LCable t
    where lc :: Envs -> t -> Doc

instance LCable Type
    where lc env@(_, tenv) t = case Map.lookup t tenv of
                                 Nothing -> lc' t
                                 Just t' -> ppr t'
              where lc' (TyCon (Kinded id _)) = ppr id
                    lc' (TyApp (TyApp (TyCon (Kinded (Ident (s@(c:_)) _ _) _)) d) r)
                     | not (isAlpha c)        = atPrecedence 5 (withPrecedence 6 (lc env d) <+> text s <+> lc env r)
                    lc' (TyApp (TyApp (TyCon (Kinded (Ident "BitdataCase" _ _) _)) ty) (TyLabel l))
                                              = atPrecedence 10 (lc env ty) <> dot <> ppr l
                    lc' (TyApp t t')          = atPrecedence 9 (lc env t <+> withPrecedence 10 (lc env t'))
                    lc' (TyNat i)             = integer i
                    lc' (TyLabel l)           = dquotes (ppr l)
                    lc' (TyVar _)             = error "LC.hs:23"
                    lc' (TyGen _)             = error "LC.hs:24"

printBitVector :: Integer -> Int -> Doc
printBitVector n s
    | s `mod` 4 == 0 = text "X" <> iter 4 hexDigits (s `div` 4) n
    | s `mod` 3 == 0 = text "O" <> iter 3 octDigits (s `div` 3) n
    | otherwise      = text "B" <> iter 1 binDigits s n
    where hexDigits = "0123456789ABCDEF"
          octDigits = "01234567"
          binDigits = "01"

          -- iter step digits s n prints the bottom 's' digits of 'n', using the list of digits in
          -- 'digits' and stepping by 'step' bits.
          iter step digits 0 _ = empty
          iter step digits s n = iter step digits (s - 1) (n `shiftR` step) <> (char (digits !! (fromIntegral n .&. (2 ^ step - 1))))

printCase :: Envs -> Match -> Doc
printCase envs (MCommit e)            = lc envs e
printCase _ MFail                  = error "LC.hs:42" -- this really could be handled correctly...
printCase envs (MElse (MGuarded (GLet ds) m1) m2) =
    lc envs (ELet ds (EMatch (MElse m1 m2)))
printCase envs@(cenv, _) m@(MElse{})            =
    case rest of
      Just m' -> foldr fatbar (printCase envs m') (map printCaseBlock casess)
      Nothing -> foldr1 fatbar (map printCaseBlock casess)
    where (casess, rest) = gather (flattenElses m)
          matchType MCommit{} = "c "
          matchType MFail{}   = "f "
          matchType MElse{}   = "e "
          matchType MGuarded{} = "g "
          gather (MGuarded g@(GFrom (PCon{}) w) m : rest) =
              case gather rest of
                ((w', alts) : altss, rest')
                    | w == w' -> ((w, MGuarded g m : alts) : altss, rest')
                    | otherwise -> ((w, [MGuarded g m]) : (w', alts) : altss, rest')
                ([], rest') ->
                    ([(w, [MGuarded g m])], rest')
          gather [] = ([], Nothing)
          gather ms  = ([], Just (foldr1 MElse ms))
          printCaseBlock (w, alts) =
              align ("case" <+> ppr w <+> "of" <$$>
                     indent 2 (align (vcat [ ppr k' <+> hsep (map ppr vs) <+> "->" <+> align (printCase envs m)
                                           | MGuarded (GFrom (PCon (Inst k ts _) vs) _) m <- alts,
                                             let k' = fromMaybe k (Map.lookup (k, ts) cenv)])))
          fatbar v w = parens (parens v <+> bar <+> parens w)
printCase envs (MGuarded (GLet ds) m) = lc envs (ELet ds (EMatch m))
printCase envs@(cenv, _) (MGuarded (GFrom (PCon (Inst k ts _) vs) w) m) =
    "case" <+> ppr w <+> "of" <$$>
    indent 2 (ppr k' <+> hsep (map ppr vs) <+> "->" <+> align (printCase envs m))
    where k' = fromMaybe k (Map.lookup (k, ts) cenv)
printCase _ (MGuarded _ _) = error "LC.hs:64"

printDo :: Envs -> Expr -> Doc
printDo envs e = text "do" <+> printBind e
    where printBind (EBind _ _ _ _ var e body) =
              align ((ppr var <+> text "<-" <+> align (lc envs e) <> semi) <$$> printBind body)
          printBind e = lc envs e

instance LCable Expr
    where lc _ (ELamVar id)      = ppr id
          lc _ (ELetVar{})       = error "LC.hs:41"
          lc _ (EBits n s)       = printBitVector n s
          lc (cenv, _) (ECon (Inst k ts _ )) =
              ppr (fromMaybe k (Map.lookup (k, ts) cenv))
          lc _ (EBitCon id [])   = ppr id
          lc envs (EBitCon id es)   = ppr id <> brackets (align (cat (punctuate " | " [ppr f <+> equals <+> lc envs e | (f, e) <- es])))
          lc envs (EStructInit k fs) = ppr k <> brackets (align (cat (punctuate " | " [ppr f <+> "<-" <+> lc envs e | (f, e) <- fs])))
          lc envs (ELam id ty body) = atPrecedence 9 $
                                      ((backslash <+>
                                        parens
                                        (text (fromId id) <+>
                                         text "::" <+> lc envs ty) <+>
                                        text "->") <+> (nest 3 $ lc envs body))
          lc _ (EMethod{})       = error "LC.hs:55"
          lc envs (ELet ds body)    = atPrecedence 9
                                      . align
                                      $ hang 2 (text "let" <+> align (lc envs ds) </> text "in" <+> (align (lc envs body)))
          lc _ (ELetTypes{})     = error "LC.hs:59"
          lc _ (ESubst{})        = error "LC.hs:60"
          lc envs (EMatch m)     = printCase envs m
          lc envs (EApp e e')       = parens $ atPrecedence 9 (lc envs e <+> (withPrecedence 10 (lc envs e')))
          lc envs (EBitSelect e f)  = atPrecedence 10 (lc envs e) <> dot <> ppr f
          lc envs (EBitUpdate e f e') = atPrecedence 10 (lc envs e) <> brackets (ppr f <+> equals <+> lc envs e')
          lc envs e@(EBind{})       = printDo envs e
          lc envs (EReturn e)       = atPrecedence 9 (text "primRet" <+> withPrecedence 10 (lc envs e))

instance LCable Defn
    where lc envs (Defn i (Forall [] [] t) (Left (pi,ts))) =
              text "external" <+> ppr i <+> braces (hsep (ppr pi : map (atPrecedence 10 . lc envs) ts)) <+> "::" <+> lc envs t
          lc envs (Defn i (Forall [] [] t) (Right (Gen _ _ e))) =
              align (ppr i <+> "::" <+> lc envs t <$>
                     ppr i <+> "=" <+> (withPrecedence 0 $ lc envs e))

instance LCable Decls
    where lc envs (Decls ds) = align (vcat (map (lc envs) ds))

instance LCable (TopDecl Type)
    where lc envs@(cenv, tenv) (Datatype name params ctors)
              | name == "Unit" = empty
              | otherwise = nest 4 (text "data" <+> ppr (fromMaybe (error "LC.hs:134") (Map.lookup (foldl TyApp (TyCon (Kinded name KStar)) params) tenv)) <+> pprCtors)
              where pprCtor (name, _, _, fields) = ppr (fromMaybe (error "LC.hs:141") (Map.lookup (name, params) cenv)) <+> sep (map (atPrecedence 10 . lc envs) fields)
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]

          lc envs (Bitdatatype name pat ctors)
              | name == "Bool" = empty
              | otherwise = nest 4 (text "bitdata" <+> ppr name <> text "/" <> int (width pat) <+> pprCtors)
              where pprCtor (name, fields, _) = ppr name <+> brackets (align (cat (punctuate (space <> bar <> space) (map (lc envs) fields))))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> align (pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ])

          lc envs (Struct name size _align fields) =
              nest 4 ("struct" <+> ppr name <+> "/" <+> int size <+> brackets (cat (punctuate (softline <> bar <> space) (map (lc envs) fields))) )

          lc envs (Area v namesAndInits ty size align) =
              vcat [nest 4 ((if v then text "volatile" <> space else empty) <>
                            text "area" <+> (ppr name <+> text "<-" <+> ppr init) </> text "::" <+> lc envs ty <+> sizeAlign size align)
                     | (name, Inst init [] []) <- namesAndInits]

sizeAlign size align = text ("{- size = "++show size++", align = "++show align++" -}")

instance LCable BitdataField
    where lc envs (LabeledField name ty width offset) =
              ppr name <::> lc envs ty <+> widthOffset width offset
          lc envs (ConstantField v width offset) = integer v <+> widthOffset width offset

widthOffset width offset = text ("{- width = "++show width++", offset = "++show offset++" -}")

instance LCable StructField
    where lc envs (StructField mname ty width offset)
            = maybe id (\name -> (ppr name <::>)) mname (lc envs ty <+> widthOffset width offset)

printEntrypoints [] = empty
printEntrypoints is = "entrypoint" <+> hcat (punctuate comma (map (ppr . fst) is))

stringOfStrings ss = intercalate "__" (map (concatMap (mangleChar False . unspace)) ss)
    where unspace c | isSpace c = '_'
                    | otherwise = c

buildEnvironments :: [TopDecl Type] -> Base (CtorEnv, TypeEnv)
buildEnvironments = foldM buildEnvironment (Map.empty, Map.empty)
    where buildEnvironment :: (CtorEnv, TypeEnv) -> TopDecl Type -> Base (CtorEnv, TypeEnv)
          buildEnvironment  (cenv, tenv) (Datatype k ts ctors)
              | k == "Unit" = return (cenv, tenv)
              | otherwise = do ctorNames <- mapM (\(k, _, _, _) -> fresh k) ctors
                               return (foldr (buildCtor ts) cenv (zip ctors ctorNames),
                                       Map.insert ty (fromString $ stringOfStrings (fromId k : map (show . ppr) ts)) tenv)
              where ty = foldl TyApp (TyCon (Kinded k (foldr (\_ k -> KFun KStar k) KStar ts))) ts
                    buildCtor ts ((k, _, _, _), z) = Map.insert (k, ts) (fromString (fromId z))
          buildEnvironment envs _ = return envs


instance LCable Specialized
    where lc envs (Specialized topDecls entries decls) =
               vcat (punctuate line ([text "type M = Proc"] ++
                                     [printEntrypoints notMainEntries] ++
                                     (if null mainEntries
                                      then []
                                      else ["export" <+> ppr (fst (head mainEntries))]) ++
                                     map (lc envs) topDecls  ++
                                     [lc envs decls]))
              where mainEntries = filter snd (entrypoints entries)
                    notMainEntries = filter (not . snd) (entrypoints entries)
                    entrypoints [] = []
                    entrypoints ((ELamVar v, b) : rest) = (v, b) : entrypoints rest
                    entrypoints _ = error "LC.hs:171"

toLC :: Pass st Specialized (Doc, [(Id, Bool)])
toLC p@(Specialized topDecls entries _) =
    liftBase $
    do envs <- buildEnvironments topDecls
       return (lc envs p, entrypoints)
    where entrypoints = [(x, b) | (ELamVar x, b) <- entries]
