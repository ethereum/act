{-# Language GADTs #-}

module Print where

import Data.ByteString.UTF8 (toString)

import Data.List
import Data.List.NonEmpty as NonEmpty (toList)

import Syntax
import RefinedAst

prettyBehaviour :: Behaviour -> String
prettyBehaviour (Behaviour name _ contract interface preconditions postconditions stateUpdates returns)
  =   "behaviour " <> name <> " of " <> contract
  >-< "interface " <> (show interface)
  <> prettyPre preconditions
  <> prettyStorage stateUpdates
  <> prettyRet returns
  <> prettyPost postconditions
  where
    prettyPre [] = ""
    prettyPre p = header "iff" >-< block (prettyExp <$> p)

    prettyStorage [] = ""
    prettyStorage s = header "storage" >-< block (prettyState <$> s)

    prettyState (Left loc) = prettyLocation loc
    prettyState (Right update) = prettyUpdate update

    prettyRet (Just ret) = header "returns" >-< "  " <> prettyReturnExp ret
    prettyRet Nothing = ""

    prettyPost [] = ""
    prettyPost p = header "ensures" >-< block (prettyExp <$> p)

    header s = "\n\n" <> s <> "\n"
    block l = "  " <> intercalate "\n  " l
    x >-< y = x <> "\n" <> y

prettyExp :: Exp t a -> String
prettyExp e = case e of

  -- booleans
  Or a b -> print2 "or" a b
  Eq a b -> print2 "==" a b
  LE a b -> print2 "<" a b
  GE a b -> print2 ">" a b
  LEQ a b -> print2 "<=" a b
  GEQ a b -> print2 ">=" a b
  And a b -> print2 "and" a b
  NEq a b -> print2 "=/=" a b
  Neg a -> "(not " <> prettyExp a <> ")"
  Impl a b -> print2 "=>" a b
  LitBool b -> if b then "true" else "false"
  BoolVar b -> b

  -- integers
  Add a b -> print2 "+" a b
  Sub a b -> print2 "-" a b
  Mul a b -> print2 "*" a b
  Div a b -> print2 "/" a b
  Mod a b -> print2 "%" a b
  Exp a b -> print2 "^" a b
  UIntMax a -> show $ uintmax a
  UIntMin a -> show $ uintmin a
  IntMax a -> show $ intmax a
  IntMin a -> show $ intmin a
  LitInt a -> show a
  IntVar a -> a
  IntEnv a -> prettyEnv a

  -- bytestrings
  Cat a b -> print2 "++" a b
  Slice a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByVar a -> a
  ByStr a -> a
  ByLit a -> toString a
  ByEnv a -> prettyEnv a

  -- builtins
  NewAddr addr nonce -> "newAddr(" <> prettyExp addr <> ", " <> prettyExp nonce <> ")"

  --polymorphic
  ITE a b c -> "(if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c <> ")"
  UTEntry a -> prettyItem a
  TEntry a t -> show t <> "(" <> prettyItem a <> ")"

  where
    print2 sym a b = "(" <> prettyExp a <> " " <> sym <> " " <> prettyExp b <> ")"

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

prettyLocation :: StorageLocation -> String
prettyLocation (IntLoc item) = prettyItem item
prettyLocation (BoolLoc item) = prettyItem item
prettyLocation (BytesLoc item) = prettyItem item

prettyUpdate :: StorageUpdate -> String
prettyUpdate (IntUpdate item e) = prettyItem item <> " => " <> prettyExp e
prettyUpdate (BoolUpdate item e) = prettyItem item <> " => " <> prettyExp e
prettyUpdate (BytesUpdate item e) = prettyItem item <> " => " <> prettyExp e

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
  This -> "THIS"
  Nonce -> "NONCE"
