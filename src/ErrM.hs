-- BNF Converter: Error Monad
-- Copyright (C) 2004  Author:  Aarne Ranta

-- This file comes with NO WARRANTY and may be used FOR ANY PURPOSE.
module ErrM where
import Lex (AlexPosn (..))
import Syntax.Untyped
-- the Error monad: like Maybe type with error msgs

import Control.Monad (MonadPlus(..), liftM)
import Control.Applicative (Alternative(..))

data Err a = Ok a | Bad (AlexPosn, String)
  deriving (Show, Eq)

instance Monad Err where
  return      = Ok
  Ok a  >>= f = f a
  Bad s >>= _ = Bad s

instance Applicative Err where
  pure = Ok
  (Bad s) <*> _ = Bad s
  (Ok f) <*> o  = liftM f o

instance Functor Err where
  fmap = liftM

instance MonadPlus Err where
  mzero = Bad (error"", "Err.mzero")
  mplus (Bad _) y = y
  mplus x       _ = x

instance MonadFail Err where
  fail _ = mzero

instance Alternative Err where
  empty = mzero
  (<|>) = mplus

errMessage :: (Pn, String) -> Maybe a -> Err a
errMessage _ (Just c) = Ok c
errMessage e Nothing = Bad e
