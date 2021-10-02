{-# Language GADTs #-}

module Print where

import Data.ByteString.UTF8 (toString)

import Data.List

import Syntax
import Syntax.TimeAgnostic

prettyBehaviour :: Behaviour t -> String
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

    prettyState (Constant loc) = prettyLocation loc
    prettyState (Rewrite  rew) = prettyUpdate rew

    prettyRet (Just ret) = header "returns" >-< "  " <> prettyTypedExp ret
    prettyRet Nothing = ""

    prettyPost [] = ""
    prettyPost p = header "ensures" >-< block (prettyExp <$> p)

    header s = "\n\n" <> s <> "\n"
    block l = "  " <> intercalate "\n  " l
    x >-< y = x <> "\n" <> y

prettyExp :: Exp a t -> String
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
  IntEnv a -> prettyEnv a

  -- bytestrings
  Cat a b -> print2 "++" a b
  Slice a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByStr a -> a
  ByLit a -> toString a
  ByEnv a -> prettyEnv a

  -- builtins
  NewAddr addr nonce -> "newAddr(" <> prettyExp addr <> ", " <> prettyExp nonce <> ")"

  --polymorphic
  ITE a b c -> "(if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c <> ")"
  TEntry t a -> timeParens t $ prettyItem a
  Var _ x -> x
  where
    print2 sym a b = "(" <> prettyExp a <> " " <> sym <> " " <> prettyExp b <> ")"

prettyTypedExp :: TypedExp t -> String
prettyTypedExp (TExp _ e) = prettyExp e
--  TExp SBoolean e' -> prettyExp e'
--  TExp SByteStr e' -> prettyExp e'

prettyItem :: TStorageItem a t -> String
prettyItem item = contractFromItem item <> "." <> idFromItem item <> concatMap (brackets . prettyTypedExp) (ixsFromItem item)
  where
    brackets str = "[" <> str <> "]"

prettyLocation :: StorageLocation t -> String
prettyLocation (Loc _ item) = prettyItem item
--prettyLocation (BoolLoc item) = prettyItem item
--prettyLocation (BytesLoc item) = prettyItem item

prettyUpdate :: StorageUpdate t -> String
prettyUpdate (Update _ item e) = prettyItem item <> " => " <> prettyExp e
--prettyUpdate (BoolUpdate item e) = prettyItem item <> " => " <> prettyExp e
--prettyUpdate (BytesUpdate item e) = prettyItem item <> " => " <> prettyExp e

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
