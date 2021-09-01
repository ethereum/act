{-# LANGUAGE OverloadedLists #-}

module ErrorLogger (module ErrorLogger) where

import Control.Lens as ErrorLogger ((#))
import Control.Monad.Writer
import Data.Functor
import Data.List.NonEmpty
import Data.Validation as ErrorLogger

import Syntax.Untyped (Pn)

type Error e a = Validation (NonEmpty (Pn,e)) a

throw :: (Pn,e) -> Error e a
throw err = _Failure # [err]

bindDummy :: (Monoid a, Semigroup e) => Validation e a -> (a -> Validation e b) -> Validation e b
bindDummy val cont = validation (\e -> cont mempty <* Failure e) cont val

(>>=?) :: (Monoid a, Semigroup e) => Validation e a -> (a -> Validation e b) -> Validation e b
(>>=?) = bindDummy

liftWriter :: Writer [(Pn,e)] a -> Error e a
liftWriter writer = case runWriter writer of
  (res, []) -> pure res
  (_,   es) -> _Failure # fromList es
