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

throw :: (Pn,e) -> Error e a
throw msg = _Failure # [msg]
