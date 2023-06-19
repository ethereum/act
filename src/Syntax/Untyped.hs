-- data types for the parsed syntax.
-- Has the correct basic structure, but doesn't necessarily type check
-- It is also equipped with position information for extra debugging xp
{-# LANGUAGE OverloadedStrings #-}

module Syntax.Untyped (module Syntax.Untyped) where

import Data.Aeson
import Data.List (intercalate)
import Data.List.NonEmpty (toList, NonEmpty)

import EVM.ABI (AbiType)
import Lex

type Pn = AlexPosn

type Id = String

newtype Act = Main [Contract]
  deriving (Eq, Show)

data Contract = Contract Definition [Transition]
  deriving (Eq, Show)

data Definition = Definition Pn Id Interface [IffH] Creates Ensures Invariants
  deriving (Eq, Show)

data Transition = Transition Pn Id Id Interface [IffH] Cases Ensures
  deriving (Eq, Show)

type Ensures = [Expr]

type Invariants = [Expr]

data Interface = Interface Id [Decl]
  deriving (Eq)

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

data Cases
  = Direct Post
  | Branches [Case]
  deriving (Eq, Show)

data Case = Case Pn Expr Post
  deriving (Eq, Show)

data Post
  = Post [Storage] (Maybe Expr)
  deriving (Eq, Show)

newtype Creates = Creates [Assign]
  deriving (Eq, Show)

data Storage
  = Rewrite Entry Expr
  | Constant Entry
  deriving (Eq, Show)

data Assign = AssignVal StorageVar Expr | AssignMany StorageVar [Defn] | AssignStruct StorageVar [Defn]
  deriving (Eq, Show)
-- TODO AssignStruct is never used

data IffH = Iff Pn [Expr]
  deriving (Eq, Show)

data Entry
  = EVar Pn Id
  | EMapping Pn Entry [Expr]
  | EField Pn Entry Id
  deriving (Eq, Show)

data Defn = Defn Expr Expr
  deriving (Eq, Show)

data Expr
  = EAnd Pn Expr Expr
  | EOr Pn Expr Expr
  | ENot Pn Expr
  | EImpl Pn Expr Expr
  | EEq Pn Expr Expr
  | ENeq Pn Expr Expr
  | ELEQ Pn Expr Expr
  | ELT Pn Expr Expr
  | EGEQ Pn Expr Expr
  | EGT Pn Expr Expr
  | EAdd Pn Expr Expr
  | ESub Pn Expr Expr
  | EITE Pn Expr Expr Expr
  | EMul Pn Expr Expr
  | EDiv Pn Expr Expr
  | EMod Pn Expr Expr
  | EExp Pn Expr Expr
  | EUTEntry Entry
  | EPreEntry Entry
  | EPostEntry Entry
  | ECreate Pn Id [Expr]
  | ListConst Expr
  | ECat Pn Expr Expr
  | ESlice Pn Expr Expr Expr
  | ENewaddr Pn Expr Expr
  | ENewaddr2 Pn Expr Expr Expr
  | BYHash Pn Expr
  | BYAbiE Pn Expr
  | StringLit Pn String
  | WildExp Pn
  | EnvExp Pn EthEnv
  | IntLit Pn Integer
  | BoolLit Pn Bool
  | EInRange Pn AbiType Expr
  deriving (Eq, Show)

data EthEnv
  = Caller
  | Callvalue
  | Calldepth
  | Origin
  | Blockhash
  | Blocknumber
  | Difficulty
  | Chainid
  | Gaslimit
  | Coinbase
  | Timestamp
  | This
  | Nonce
  deriving (Show, Eq)


data ValueType
  = ContractType Id
  | PrimitiveType AbiType
  deriving Eq

instance Show ValueType where
  show (ContractType c) = c
  show (PrimitiveType t) = show t

data SlotType
  = StorageMapping (NonEmpty ValueType) ValueType
  | StorageValue ValueType
  deriving (Eq)

instance Show SlotType where
 show (StorageValue t) = show t
 show (StorageMapping s t) =
   foldr
   (\x y ->
       "mapping("
       <> show x
       <> " => "
       <> y
       <> ")")
   (show t) s

data StorageVar = StorageVar Pn SlotType Id
  deriving (Eq, Show)

data Decl = Decl AbiType Id
  deriving Eq

instance Show Decl where
  show (Decl t a) = show t <> " " <> a

instance ToJSON SlotType where
  toJSON (StorageValue t) = object ["type" .= show t]
  toJSON (StorageMapping ixTypes valType) = object [ "type" .= String "mapping"
                                                   , "ixTypes" .= show (toList ixTypes)
                                                   , "valType" .= show valType]

-- Create the string that is used to construct the function selector
makeIface :: Interface -> String
makeIface (Interface a decls) =
 a <> "(" <> intercalate "," (fmap (\(Decl typ _) -> show typ) decls) <> ")"
