{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings #-}

-- BNF Converter: Error Monad
-- Copyright (C) 2004  Author:  Aarne Ranta

-- This file comes with NO WARRANTY and may be used FOR ANY PURPOSE.
module ErrM where

import qualified Data.Text as Text
import Data.Text (unpack)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import Control.Monad (MonadPlus(..), liftM)
import Control.Monad.Fail
import Control.Applicative (Applicative(..), Alternative(..))

import Syntax
import Lex (AlexPosn(..))
-- the Error monad: like Maybe type with error msgs

data Err a b = Bad a | Ok b
  deriving (Show, Eq)

instance Monad (Err a) where
  return      = Ok
  Ok a  >>= f = f a
  Bad s >>= _ = Bad s

instance Applicative (Err a) where
  pure = Ok
  (Bad s) <*> _ = Bad s
  (Ok f) <*> o  = fmap f o

instance Functor (Err a) where
  fmap = liftM

instance Monoid a => MonadPlus (Err a) where
  mzero = Bad mempty
  mplus (Bad _) y = y
  mplus x       _ = x

instance Monoid a => MonadFail (Err a) where
  fail _ = mzero

instance Monoid a => Alternative (Err a) where
  empty = mzero
  (<|>) = mplus

class PrintableError a where
  prettyErr :: String -> a -> IO ()

instance PrintableError (Pn, String) where
  prettyErr _ (pn, msg) | pn == nowhere = do
    hPutStrLn stderr "Internal error:"
    hPutStrLn stderr msg
    exitFailure
  prettyErr contents (pn, msg) | pn == lastPos = do
    let culprit = last $ lines contents
        line' = length (lines contents) - 1
        col  = length culprit
    hPutStrLn stderr $ show line' <> " | " <> culprit
    hPutStrLn stderr $ unpack (Text.replicate (col + (length (show line' <> " | ")) - 1) " " <> "^")
    hPutStrLn stderr msg
    exitFailure
  prettyErr contents (AlexPn _ line' col, msg) = do
    let cxt = safeDrop (line' - 1) (lines contents)
    hPutStrLn stderr $ show line' <> " | " <> head cxt
    hPutStrLn stderr $ unpack (Text.replicate (col + (length (show line' <> " | ")) - 1) " " <> "^")
    hPutStrLn stderr msg
    exitFailure
    where
      safeDrop :: Int -> [a] -> [a]
      safeDrop 0 a = a
      safeDrop _ [] = []
      safeDrop _ [a] = [a]
      safeDrop n (_:xs) = safeDrop (n-1) xs

instance PrintableError String where
  prettyErr _ msg = do
    hPutStrLn stderr msg
    exitFailure

type ParseErr = Err (Pn, String)
type TypeErr = Err (Pn, String)
type KErr = Err (Pn, String)
type SMTErr = Err String

errMessage :: (Pn, String) -> Maybe a -> Err (Pn, String) a
errMessage _ (Just c) = Ok c
errMessage e Nothing = Bad e

nowhere :: Pn
nowhere = AlexPn 0 0 0

lastPos :: Pn
lastPos = AlexPn (-1) (-1) (-1)

