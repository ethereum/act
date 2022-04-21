{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

{- | Implements a concrete evaluator for act
-}
module Eval where
import Syntax.Annotated
import Data.ByteString as BS
import Data.ByteString.Char8 as BS8
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Typeable

eval :: Behaviour -> [(String, TypedExp)] -> TypedExp
eval behv args = undefined

val :: Eq a => a -> [(a, b)] -> Maybe b
val _ [] = Nothing
val ix ((ix', e) : tl) = do
  if ix == ix'
  then pure e
  else val ix tl

substitute
  :: [(EthEnv, TypedExp)]
  -> [(String, TypedExp)]
  -> [(String, [((String, [TypedExp]), TypedExp)])]
  -> Exp a
  -> Exp a
substitute env cd store = \case
  (IntEnv _ e) -> case fromMaybe (error $ "no substitute provided for: " ++ show e) (val e env) of
    (TExp SInteger e') -> e'
    _ -> error "incorrect type"

  (ByEnv _ e) -> case fromMaybe (error $ "no substitute provided for: " ++ show e) (val e env) of
    (TExp SByteStr e') -> e'
    _ -> error "incorrect type"

  Var _ tp nm -> case fromMaybe (error $ "no substitute provided for: " ++ show nm) (val nm cd) of
   (TExp tp' e') -> case (tp, tp') of
      (SInteger, SInteger) -> e'
      (SBoolean, SBoolean) -> e'
      (SByteStr, SByteStr) -> e'
      _ -> error "incorrect type"

  (TEntry _ _ (Item tp contract name ixs)) -> let
      c = fromMaybe (error "contract not found") (val contract store)
      e = fromMaybe (error "val not found") (val (name, ixs) c)
     in case (tp, e) of
      (SInteger, TExp SInteger v) -> v
      (SBoolean, TExp SBoolean v) -> v
      (SByteStr, TExp SByteStr v) -> v
      _ -> error "incorrect type"
  a -> substitute env cd store a

reduce :: Exp a -> a
reduce e = case e of
  (And _ a b) -> reduce a && reduce b
  (Or _ a b) -> reduce a || reduce b
  (Impl _ a b) -> not (reduce a || reduce b)
  (Neg _ a) -> not (reduce a)
  (LE _ a b) -> reduce a < reduce b
  (LEQ _ a b) -> reduce a <= reduce b
  (GE _ a b) -> reduce a > reduce b
  (GEQ _ a b) -> reduce a >= reduce b
  (LitBool _ b) -> b

  -- integers
  (Add _ a b) -> (reduce a) + (reduce b)
  (Sub _ a b) -> (reduce a) - (reduce b)
  (Mul _ a b) -> (reduce a) * (reduce b)
  (Div _ a b) -> (reduce a) `div` (reduce b)
  (Mod _ a b) -> (reduce a `mod` reduce b)
  (Exp _ a b) -> (reduce a) ^ (reduce b)
  (LitInt _ i) -> i

  -- boprounds
  (IntMin _ a) -> intmin a
  (IntMax _ a) -> intmax a
  (UIntMin _ a) -> uintmin a
  (UIntMax _ a) -> uintmax a

  -- bytestrings
  (Cat _ a b) -> (reduce a) <> (reduce b)
  (Slice _ bs st end) -> BS.drop (fromIntegral $ reduce st) $ BS.take (fromIntegral $ reduce end) (reduce bs)
  (ByStr _ str) -> BS8.pack str
  (ByLit _ bs) -> bs

  -- builtins
  (NewAddr {}) -> error "unsupported"

  -- poly
  (Eq _ a b) -> (reduce a) == (reduce b)
  (NEq _ a b) -> (reduce a) /= (reduce b)
  (ITE _ cond l r) -> if reduce cond then reduce l else reduce r

  -- TODO: lift some metadata on concreteness to the type level?
  (IntEnv {}) -> error "unsubstituted env var"
  (ByEnv {}) -> error "unsubstituted env var"
  (Var {}) -> error "unsubstituted var"
  (TEntry {}) -> error "unsubstituted env var"



