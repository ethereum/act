{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings #-}

-- BNF Converter: Error Monad
-- Copyright (C) 2004  Author:  Aarne Ranta, David Terry

-- This file comes with NO WARRANTY and may be used FOR ANY PURPOSE.
module ErrM where

import qualified Data.Text as Text
import Data.Text (unpack)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import Control.Monad (MonadPlus(..), liftM, ap)
import Control.Monad.Fail
import Control.Monad.Identity
import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))

import Syntax
import Lex (AlexPosn(..))


-- Type aliases --


type ParseErr = Err (Pn, String)
type TypeErr = Err (Pn, String)
type KErr = Err (Pn, String)
type SMTErr = ErrT String IO


-- the Error monad: like Maybe type with error msgs


-- It's common practice to define the non-transformer
-- in terms of the transformer rather than the other way
-- around. This is because there exists an Identity monad,
-- which literally does nothing except embedding a normal
-- value inside a monad. If we parametrize ErrT on that,
-- we literally get back the original functionality of Err:

type Err a = ErrT a Identity

-- And since Identity is a monad, as long as we have the
-- appropriate instances for ErrT
-- (e.g. Monad m => Monad (ErrT a m))
-- we get all of those instances for free for Err.


-- Error Monad Transformer


-- Since we no longer have a simple Err which we can put
-- inside ErrT, ErrT must itself contain our constructors.
-- The below code may look weird, and in a way it is, but
-- I want to base it immediately on how Err used to look,
-- and then we can simplify it later:

data ErrT a m b = Bad (m a) | Ok (m b)

-- We need to define runErrT as a way to get out the
-- "underlying" monad. Compare this to e.g. runStateT:
-- https://hackage.haskell.org/package/transformers-0.5.6.2/docs/Control-Monad-Trans-State-Lazy.html#v:runStateT
-- Because it can contain one of two values, when we run
-- it, we can encode the result as an Either.

runErrT :: ErrT a m b -> m (Either a b)
runErrT (Bad err) = Left <$> err
runErrT (Ok val)  = Right <$> val

-- The above code won't work though. Why?
-- How can it be fixed?

-- The Functor/Applicative/Monad instances for ErrT need
-- to change because we no longer have an Err inside.
-- We could more or less copy the instances we previously
-- had for Err, but I would suggest making the types less
-- restrictive to keep the Functor > Applicative > Monad
-- hierarchy clearer:

instance Functor m => Functor (ErrT a m) where
  fmap _ (Bad err) = Bad err
  fmap f (Ok val)  = Ok (f <$> val)

instance Applicative m => Applicative (ErrT a m) where
  pure                = Ok . pure
  (Bad s) <*> _       = Bad s
  (Ok f)  <*> (Bad s) = Bad s
  (Ok f)  <*> (Ok a)  = Ok (f <*> a)

-- As for the Monad instance, we run into problems:

instance Monad m => Monad (ErrT a m) where
  return = pure
  Bad err >>= _ = Bad err
  Ok val  >>= f = _
    where
      run = do
        a <- val
        res <- runErrT $ f a
        case res of
          Right ok  -> _
          Left  bad -> _

-- We're able to run f on the contents of Ok and then
-- do runErrT to get out the Either wrapped in the
-- underlying monad. But then we want to put these values
-- back into ErrT, which we can't because we're still
-- working inside the underlying monad. This explanation
-- may not be super clear but I encourage you to play around
-- and try to get this to type check to get a feel for the
-- problem.

-- Anyway, this is why the definition of ErrT is bad.
-- We need to do this instead:

newtype ErrT2 a m b = ErrT2 { runErrT2 :: m (Either a b) }

-- The difference here is:
-- Instead of having a sum type which contains the
-- underlying monad, we have an underlying monad which
-- contains a sum type. Using this, defining all of the
-- instances will be much easier. If you're unsure, try it!

-- Note that the runErrT2 function actually works out of
-- the box, as opposed to runErrT above.

-- And compare ErrT2 to the definition of ExceptT, too!



-- Typeclass for polymorphic display of the various error types used throughout the codebase


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


-- ** Utils  ** --


--errMessage :: (Pn, String) -> Maybe a -> Err (Pn, String) a
--errMessage _ (Just c) = Ok c
--errMessage e Nothing = Bad e

nowhere :: Pn
nowhere = AlexPn 0 0 0

lastPos :: Pn
lastPos = AlexPn (-1) (-1) (-1)

