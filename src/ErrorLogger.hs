{-# LANGUAGE OverloadedLists,TypeOperators, FlexibleInstances, ApplicativeDo, MultiParamTypeClasses, ScopedTypeVariables, InstanceSigs #-}

module ErrorLogger (module ErrorLogger) where

import Control.Lens as ErrorLogger ((#))
import Control.Monad.Writer
import Data.Functor
import Data.List.NonEmpty
import Data.Validation as ErrorLogger
import GHC.Generics

import Syntax.Untyped (Pn)

type Error e = Validation (NonEmpty (Pn,e))

type Logger e = Writer [(Pn,e)]

throw :: (Pn,e) -> Error e a
throw msg = _Failure # [msg]

bindDummy :: (Monoid a, Semigroup e) => Validation e a -> (a -> Validation e b) -> Validation e b
bindDummy val cont = validation (\e -> cont mempty <* Failure e) cont val

(>>=?) :: (Monoid a, Semigroup e) => Validation e a -> (a -> Validation e b) -> Validation e b
(>>=?) = bindDummy

logErrs :: Logger e a -> (a -> Error e b) -> Error e b
logErrs writer cont = case runWriter writer of
  (res, []  ) -> cont res
  (res, errs) -> cont res <* traverse throw errs

log' :: (Pn,e) -> Logger e ()
log' msg = tell [msg]

