{-# Language GADTs #-}

module Print (prettyExp, prettyEnv) where

import Data.ByteString.UTF8 (toString)

import Data.List.NonEmpty as NonEmpty (toList)

import Syntax
import RefinedAst

prettyExp :: Exp a -> String
prettyExp e = case e of

  -- booleans
  And a b -> (prettyExp a) <> " and " <> (prettyExp b)
  Or a b -> (prettyExp a) <> " or " <> (prettyExp b)
  Impl a b -> (prettyExp a) <> " => " <> (prettyExp b)
  Eq a b -> (prettyExp a) <>  " == " <> (prettyExp b)
  NEq a b -> (prettyExp a) <> " =/= " <> (prettyExp b)
  Neg a -> "not " <> (prettyExp a)
  LE a b -> (prettyExp a) <> " < " <> (prettyExp b)
  LEQ a b -> (prettyExp a) <> " <= " <> (prettyExp b)
  GEQ a b -> (prettyExp a) <> " >= " <> (prettyExp b)
  GE a b -> (prettyExp a) <> " > " <> (prettyExp b)
  LitBool b -> if b then "true" else "false"
  BoolVar b -> b

  -- integers
  Add a b -> (prettyExp a) <> " + " <> (prettyExp b)
  Sub a b -> (prettyExp a) <> " - " <> (prettyExp b)
  Mul a b -> (prettyExp a) <> " * " <> (prettyExp b)
  Div a b -> (prettyExp a) <> " / " <> (prettyExp b)
  Mod a b -> (prettyExp a) <> " % " <> (prettyExp b)
  Exp a b -> (prettyExp a) <> " ^ " <> (prettyExp b)
  LitInt a -> show a
  IntVar a -> a
  IntEnv a -> prettyEnv a

  -- bytestrings
  Cat a b -> (prettyExp a) <> " ++ " <> (prettyExp b)
  Slice a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByVar a -> a
  ByStr a -> a
  ByLit a -> toString a
  ByEnv a -> prettyEnv a

  -- builtins
  NewAddr addr nonce -> "newAddr(" <> prettyExp addr <> ", " <> prettyExp nonce <> ")"

  --polymorphic
  ITE a b c -> "if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c
  TEntry a -> prettyItem a

prettyReturnExp :: ReturnExp -> String
prettyReturnExp e = case e of
  ExpInt e' -> prettyExp e'
  ExpBool e' -> prettyExp e'
  ExpBytes e' -> prettyExp e'

prettyItem :: TStorageItem t -> String
prettyItem item = case item of
  DirectInt contract name -> contract <> "." <> name
  DirectBool contract name -> contract <> "." <> name
  DirectBytes contract name -> contract <> "." <> name
  MappedInt contract name ixs -> contract <> "." <> name <> concat (NonEmpty.toList $ surround "[" "]" <$> (prettyReturnExp <$> ixs))
  MappedBool contract name ixs -> contract <> "." <> name <> concat (NonEmpty.toList $ surround "[" "]" <$> (prettyReturnExp <$> ixs))
  MappedBytes contract name ixs -> contract <> "." <> name <> concat (NonEmpty.toList $ surround "[" "]" <$> (prettyReturnExp <$> ixs))
  where
    surround :: String -> String -> String -> String
    surround l r str = l <> str <> r

prettyEnv :: EthEnv -> String
prettyEnv e = case e of
  Caller -> "CALLER"
  Callvalue -> "CALLVALUE"
  Calldepth -> "CALLDEPTH"
  Origin -> "ORIGIN"
  Blockhash -> "BLOCKHASH"
  Blocknumber -> "BLOCKNUMBER"
  Difficulty -> "DIFFICULTY"
  Chainid -> "CHAINID"
  Gaslimit -> "GASLIMIT"
  Coinbase -> "COINBASE"
  Timestamp -> "TIMESTAMP"
  Address -> "ADDRESS"
  Nonce -> "NONCE"
