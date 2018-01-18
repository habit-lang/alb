module Analyzer.Notes where

import Control.Monad.Writer
import Data.Generics

import Common
import Printer.Common
import Printer.Surface
import Syntax.Surface

type M = WriterT [Located Pred] Base

class Noted t
    where deNote :: t -> M t

instance Noted t => Noted [t]
    where deNote = mapM deNote

instance Noted t => Noted (Maybe t)
    where deNote Nothing = return Nothing
          deNote (Just x) = Just `fmap` deNote x

instance Noted t => Noted (Located t)
    where deNote (At l x) = At l `fmap` deNote x

instance Noted Type
    where deNote (TyNote t ns)  =
              do name <- case names of
                           [] -> fresh "t"
                           [t] -> return t
                           _   -> failWith (text "Too many names in annotated type")
                 ns' <- case t of
                          At _ (TyVar _) -> return []
                          At l (TyCon c) -> return [At l (TNCon c)]
                          At l (TyApp t t') -> return [At l (TNApp t t')]
                          At l _ -> failAt l (failWith (text "Unexpected annotated type" <+> ppr t))
                 tell (concatMap (predFrom name) (ns' ++ ns))
                 return (TyVar name)
              where nameFrom (TNVar id) = [id]
                    nameFrom _ = []
                    names = concat (map (nameFrom . dislocate) ns) ++
                            case dislocate t of
                              TyVar id -> [id]
                              _        -> []
                    predFrom name (At _ (TNVar _)) =
                        []
                    predFrom name (At l (TNCon id)) =
                        [At l (Pred (At l (TyApp (At l (TyCon id)) (At l (TyVar name))))
                                    Nothing Holds)]
                    predFrom name (At l (TNApp t t')) =
                        [At l (Pred (At l (((TyApp (At l ((TyApp t) t')) (At l (TyVar name))))))
                                    Nothing Holds)]
                    predFrom name (At l (TNLeftSection t op)) =
                        [At l (Pred (At l (TyApp (At l (TyApp (TyCon `fmap` op) t)) (At l (TyVar name))))
                                    Nothing Holds)]
                    predFrom name (At l (TNRightSection op t)) =
                        [At l (Pred (At l (TyApp (At l (TyApp (TyCon `fmap` op) (At l (TyVar name)))) t))
                                    Nothing Holds)]
          deNote (TyApp t t')   = liftM2 TyApp (mapLocated deNote t) (mapLocated deNote t')
          deNote (TyKinded t k) = liftM (flip TyKinded k) (mapLocated deNote t)
          deNote (TySelect t l) = liftM (flip TySelect l) (mapLocated deNote t)
          deNote (TyInfix _ _)  = error "Infix type in deNoteing"
          deNote t              = return t

instance Noted Pred
    where deNote (Pred t mt l) = do t' <- deNote t
                                    mt' <- deNote mt
                                    return (Pred t' mt' l)

instance Noted t => Noted (Qual t)
    where deNote (ps :=> x) = censor (const []) $
                              do ((ps', x'), ps) <- listen $ liftM2 (,) (deNote ps) (deNote x)
                                 return ((ps ++ ps') :=> x')

deNoteProgram' :: Program -> M Program
deNoteProgram' = go
    where go :: Data a => a -> M a
          go = gmapM go `extM`
               (deNote :: Type -> M Type) `extM`
               (deNote :: Pred -> M Pred) `extM`
               (deNote :: Qual Type -> M (Qual Type)) `extM`
               (deNote :: Qual Pred -> M (Qual Pred))

deNoteProgram :: Pass s Program Program
deNoteProgram p = liftBase (evalWriterT (deNoteProgram' p))
    where evalWriterT m = fmap fst (runWriterT m)
