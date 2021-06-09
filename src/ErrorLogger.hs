module ErrorLogger where

import Control.Applicative
import Control.Monad.Writer

import Data.Functor (($>))
import Data.Maybe (isJust,isNothing)

-- Experimental error logging/handling

newtype Err e a = Err { unErr :: Writer [e] (Maybe a) }

instance Functor (Err e) where
  fmap f (Err w) = Err $ fmap f <$> w

instance Applicative (Err e) where
  pure a              = Err . pure . pure $ a
  (Err f) <*> (Err a) = Err $ fmap ap f <*> a

instance Alternative (Err e) where
  empty = Err $ pure Nothing
  a <|> b | succeeds a = a
          | otherwise  = b

--instance Monad (Err e) where
--  return = pure
--  (Err wA) >>= f = Err $ let (a, w1) = runWriter wA
--                    in case f <$> a of
--                      Nothing -> writer (Nothing,w1)
--                      Just eB -> writer . fmap (w1 <>) . runWriter . unErr $ eB


throw :: e -> Err e a
throw e = Err $ tell [e] $> Nothing

getErrs :: Err e a -> [e]
getErrs = execWriter . unErr

runErr :: Err e a -> (Maybe a, [e])
runErr = runWriter . unErr

getResult :: Err e a -> Maybe a
getResult = fst . runErr

fails :: Err e a -> Bool
fails = isNothing . getResult

succeeds :: Err e a -> Bool
succeeds = isJust . getResult
