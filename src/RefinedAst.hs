{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# Language DeriveAnyClass #-}
{-# Language MultiParamTypeClasses #-}

module RefinedAst where

import Data.Text (pack)
import Data.Map.Strict (Map)
import Data.List.NonEmpty hiding (fromList)
import Data.ByteString (ByteString)

import EVM.Solidity (SlotType(..))

import Syntax (Id, Interface, EthEnv)
import Data.Aeson
import Data.Aeson.Types
import Data.Vector (fromList)

-- AST post typechecking
data Claim = B Behaviour | I Invariant | S Storages deriving (Show)

newtype Storages = Storages { unStorages :: Map Id (Map Id SlotType) } deriving (Show)
data Invariant = Invariant Id (Exp Bool) deriving (Show)
data Behaviour = Behaviour
  {_name :: Id,
   _mode :: Mode,
   _creation :: Bool,
   _contract :: Id,
   _interface :: Interface,
   _preconditions :: Exp Bool,
   _postconditions :: Exp Bool,
   _stateUpdates :: [Either StorageLocation StorageUpdate],
   _returns :: Maybe ReturnExp
  }
  deriving (Show)

catInvs :: [Claim] -> [Invariant]
catInvs [] = []
catInvs ((I i):claims) = i:(catInvs claims)
catInvs (_:claims) = catInvs claims

catStores :: [Claim] -> [Storages]
catStores [] = []
catStores ((S s):claims) = s:(catStores claims)
catStores (_:claims) = catStores claims

catBehvs :: [Claim] -> [Behaviour]
catBehvs [] = []
catBehvs ((B b):claims) = b:(catBehvs claims)
catBehvs (_:claims) = catBehvs claims

data Mode
  = Pass
  | Fail
  | OOG
  deriving (Eq, Show)

--types understood by proving tools
data MType
  = Integer
  | Boolean
  | ByteStr
--  | Mapping (Map MType MType)
  deriving (Eq, Ord, Show, Read)

data StorageUpdate
  = IntUpdate (TStorageItem Integer) (Exp Integer)
  | BoolUpdate (TStorageItem Bool) (Exp Bool)
  | BytesUpdate (TStorageItem ByteString) (Exp ByteString)
  deriving (Show)

data StorageLocation
  = IntLoc (TStorageItem Integer)
  | BoolLoc (TStorageItem Bool)
  | BytesLoc (TStorageItem ByteString)
  deriving (Show, Eq)

data TStorageItem a where
  DirectInt    :: Id -> Id -> TStorageItem Integer
  DirectBool   :: Id -> Id -> TStorageItem Bool
  DirectBytes  :: Id -> Id -> TStorageItem ByteString
  MappedInt    :: Id -> Id -> NonEmpty ReturnExp -> TStorageItem Integer
  MappedBool   :: Id -> Id -> NonEmpty ReturnExp -> TStorageItem Bool
  MappedBytes  :: Id -> Id -> NonEmpty ReturnExp -> TStorageItem ByteString

deriving instance Show (TStorageItem a)
deriving instance Eq (TStorageItem a)

-- typed expressions
data Exp t where
  --booleans
  And  :: Exp Bool -> Exp Bool -> Exp Bool
  Or   :: Exp Bool -> Exp Bool -> Exp Bool
  Impl :: Exp Bool -> Exp Bool -> Exp Bool
  Eq  :: Exp Integer -> Exp Integer -> Exp Bool --TODO: make polymorphic (how to ToJSON.encode them?)
  NEq  :: Exp Integer -> Exp Integer -> Exp Bool
  Neg :: Exp Bool -> Exp Bool
  LE :: Exp Integer -> Exp Integer -> Exp Bool
  LEQ :: Exp Integer -> Exp Integer -> Exp Bool
  GEQ :: Exp Integer -> Exp Integer -> Exp Bool
  GE :: Exp Integer -> Exp Integer -> Exp Bool
  LitBool :: Bool -> Exp Bool
  BoolVar :: Id -> Exp Bool
  -- integers
  Add :: Exp Integer -> Exp Integer -> Exp Integer
  Sub :: Exp Integer -> Exp Integer -> Exp Integer
  Mul :: Exp Integer -> Exp Integer -> Exp Integer
  Div :: Exp Integer -> Exp Integer -> Exp Integer
  Mod :: Exp Integer -> Exp Integer -> Exp Integer
  Exp :: Exp Integer -> Exp Integer -> Exp Integer
  LitInt :: Integer -> Exp Integer
  IntVar :: Id -> Exp Integer
  IntEnv :: EthEnv -> Exp Integer
  -- bounds
  IntMin :: Int -> Exp Integer
  IntMax :: Int -> Exp Integer
  UIntMin :: Int -> Exp Integer
  UIntMax :: Int -> Exp Integer
  -- bytestrings
  Cat :: Exp ByteString -> Exp ByteString -> Exp ByteString
  Slice :: Exp ByteString -> Exp Integer -> Exp Integer -> Exp ByteString
  ByVar :: Id -> Exp ByteString
  ByStr :: String -> Exp ByteString
  ByLit :: ByteString -> Exp ByteString
  ByEnv :: EthEnv -> Exp ByteString
  -- builtins
  NewAddr :: Exp Integer -> Exp Integer -> Exp Integer

  --polymorphic
  ITE :: Exp Bool -> Exp t -> Exp t -> Exp t
  TEntry :: (TStorageItem t) -> Exp t

deriving instance Show (Exp t)
deriving instance Eq (Exp t)

instance Semigroup (Exp Bool) where
  a <> b = And a b

instance Monoid (Exp Bool) where
  mempty = LitBool True

data ReturnExp
  = ExpInt    (Exp Integer)
  | ExpBool   (Exp Bool)
  | ExpBytes  (Exp ByteString)
  deriving (Eq, Show)

-- intermediate json output helpers ---
instance ToJSON Claim where
  toJSON (S (Storages storages)) = object [ "kind" .= (String "Storages")
                                          , "storages" .= toJSON storages]
  toJSON (I (Invariant contract e)) = object [ "kind" .= (String "Invariant")
                                             , "expression" .= toJSON e
                                             , "contract" .= show contract ]
  toJSON (B (Behaviour {..})) = object  [ "kind" .= (String "Behaviour")
                                        , "name" .= _name
                                        , "contract" .= _contract
                                        , "mode" .= (String . pack $ show _mode)
                                        , "creation" .= _creation
                                        , "interface" .= (String . pack $ show _interface)
                                        , "preConditions" .= (toJSON _preconditions)
                                        , "postConditions" .= (toJSON _postconditions)
                                        , "stateUpdates" .= toJSON _stateUpdates
                                        , "returns" .= toJSON _returns]

instance ToJSON SlotType where
  toJSON (StorageValue t) = object ["type" .= show t]
  toJSON (StorageMapping ixTypes valType) = object [ "type" .= (String "mapping")
                                                   , "ixTypes" .= show (toList ixTypes)
                                                   , "valType" .= show valType]

instance ToJSON StorageLocation where
  toJSON (IntLoc a) = object ["location" .= toJSON a]
  toJSON (BoolLoc a) = object ["location" .= toJSON a]
  toJSON (BytesLoc a) = object ["location" .= toJSON a]

instance ToJSON StorageUpdate where
  toJSON (IntUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]
  toJSON (BoolUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]
  toJSON (BytesUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]

instance ToJSON (TStorageItem b) where
  toJSON (DirectInt a b) = object ["sort" .= (pack "int")
                                  , "name" .= (String $ pack a <> "." <> pack b)]
  toJSON (DirectBool a b) = object ["sort" .= (pack "bool")
                                   , "name" .= (String $ pack a <> "." <> pack b)]
  toJSON (DirectBytes a b) = object ["sort" .= (pack "bytes")
                                    , "name" .= (String $ pack a <> "." <> pack b)]
  toJSON (MappedInt a b c) = mapping a b c
  toJSON (MappedBool a b c) = mapping a b c
  toJSON (MappedBytes a b c) = mapping a b c

instance ToJSON ReturnExp where
   toJSON (ExpInt a) = object ["sort" .= (pack "int")
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= (String $ pack "bool")
                               ,"expression" .= toJSON a]
   toJSON (ExpBytes a) = object ["sort" .= (String $ pack "bytestring")
                               ,"expression" .= toJSON a]

instance ToJSON (Exp Integer) where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (Mul a b) = symbol "*" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON a
  toJSON (IntMin a) = toJSON $ intmin a
  toJSON (IntMax a) = toJSON $ intmax a
  toJSON (UIntMin a) = toJSON $ uintmin a
  toJSON (UIntMax a) = toJSON $ uintmax a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (TEntry a) = toJSON a
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp Bool) where
  toJSON (And a b)  = symbol "and" a b
  toJSON (LE a b)   = symbol "<" a b
  toJSON (GE a b)   = symbol ">" a b
  toJSON (Impl a b) = symbol "=>" a b
  toJSON (NEq a b)  = symbol "=/=" a b
  toJSON (Eq a b)   = symbol "==" a b
  toJSON (LEQ a b)  = symbol "<=" a b
  toJSON (GEQ a b)  = symbol ">=" a b
  toJSON (LitBool a) = String $ pack $ show a
  toJSON (Neg a) = object [  "symbol"   .= pack "not"
                          ,  "arity"    .= (Data.Aeson.Types.Number 1)
                          ,  "args"     .= (Array $ fromList [toJSON a])]
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp ByteString) where
  toJSON a = String $ pack $ show a


mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
mapping c a b = object [  "symbol"   .= pack "lookup"
                       ,  "arity"    .= (Data.Aeson.Types.Number 3)
                       ,  "args"     .= (Array $ fromList [toJSON c, toJSON a, toJSON b])]

symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= (Data.Aeson.Types.Number 2)
                      ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1
