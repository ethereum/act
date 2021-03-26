{-# LANGUAGE TemplateHaskell #-}

module TH where

import Data.Char (toLower)
import Control.Monad (forM, replicateM)
import Language.Haskell.TH

makeSmartCons :: Name -> Name -> Q [Dec]
makeSmartCons typ f = do
  TyConI (DataD _ _ _ _ cons _) <- reify typ
  forM (nameArity <$> cons) $ \(name, arity) -> do
    vars <- replicateM arity (newName "x")
    let body = NormalB $ AppE (VarE f) (foldl1 AppE (ConE name : (VarE <$> vars)))
    return $ FunD (underScore name) [Clause (VarP <$> vars) body []]
  where
    nameArity :: Con -> (Name, Int)
    nameArity (ForallC _ _ c)    = nameArity c
    nameArity (NormalC n ts)     = (n, length ts)
    nameArity (GadtC (n:_) ts _) = (n, length ts)

    underScore :: Name -> Name
    underScore = mkName . ('_':) . nameBase