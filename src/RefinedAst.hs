{-# OPTIONS_GHC -Wno-missing-signatures #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}

module RefinedAst where

import Data.Text (pack)
import Data.Typeable
import Data.Map.Strict (Map)
import Data.List.NonEmpty hiding (fromList)
import Data.ByteString (ByteString)

import EVM.Solidity (SlotType(..))

import Syntax (Id, Interface, EthEnv)
import Data.Aeson
import Data.Aeson.Types
import Data.Vector (fromList)

import Data.Comp.Multi.Term
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Show()

-- AST post typechecking
data Claim = C Constructor | B Behaviour | I Invariant | S Store deriving (Show, Eq)

type Store = Map Id (Map Id SlotType)

data Invariant = Invariant
  { _icontract :: Id
  , _ipreconditions :: [Exp Bool]
  , _predicate :: Exp Bool
  }
deriving instance Show Invariant
deriving instance Eq Invariant

data Constructor = Constructor
  { _cname :: Id,
    _cmode :: Mode,
    _cinterface :: Interface,
    _cpreconditions :: [Exp Bool],
    _cpostconditions :: [Exp Bool],
    _initialStorage :: [StorageUpdate],
    _cstateUpdates :: [Either StorageLocation StorageUpdate]
  }
deriving instance Show Constructor
deriving instance Eq Constructor

data Behaviour = Behaviour
  {_name :: Id,
   _mode :: Mode,
   _contract :: Id,
   _interface :: Interface,
   _preconditions :: [Exp Bool],
   _postconditions :: [Exp Bool],
   _stateUpdates :: [Either StorageLocation StorageUpdate],
   _returns :: Maybe ReturnExp
  }
deriving instance Show Behaviour
deriving instance Eq Behaviour

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
deriving instance Show StorageUpdate
deriving instance Eq StorageUpdate

data StorageLocation
  = IntLoc (TStorageItem Integer)
  | BoolLoc (TStorageItem Bool)
  | BytesLoc (TStorageItem ByteString)
deriving instance Show StorageLocation
deriving instance Eq StorageLocation

data TStorageItem a where
  DirectInt    :: Id -> Id -> TStorageItem Integer
  DirectBool   :: Id -> Id -> TStorageItem Bool
  DirectBytes  :: Id -> Id -> TStorageItem ByteString
  MappedInt    :: Id -> Id -> NonEmpty ReturnExp -> TStorageItem Integer
  MappedBool   :: Id -> Id -> NonEmpty ReturnExp -> TStorageItem Bool
  MappedBytes  :: Id -> Id -> NonEmpty ReturnExp -> TStorageItem ByteString
deriving instance Show (TStorageItem a)
deriving instance Eq (TStorageItem a)

data ReturnExp
  = ExpInt    (Exp Integer)
  | ExpBool   (Exp Bool)
  | ExpBytes  (Exp ByteString)
deriving instance Show ReturnExp
deriving instance Eq ReturnExp

-- typed expressions
data ExpF r t where
  -- booleans
  And  :: r Bool -> r Bool -> ExpF r Bool
  Or   :: r Bool -> r Bool -> ExpF r Bool
  Impl :: r Bool -> r Bool -> ExpF r Bool
  Neg :: r Bool -> ExpF r Bool
  LE :: r Integer -> r Integer -> ExpF r Bool
  LEQ :: r Integer -> r Integer -> ExpF r Bool
  GEQ :: r Integer -> r Integer -> ExpF r Bool
  GE :: r Integer -> r Integer -> ExpF r Bool
  LitBool :: Bool -> ExpF r Bool
  BoolVar :: Id -> ExpF r Bool
  BoolStore :: TStorageItem Bool -> ExpF r Bool
  -- integers
  Add :: r Integer -> r Integer -> ExpF r Integer
  Sub :: r Integer -> r Integer -> ExpF r Integer
  Mul :: r Integer -> r Integer -> ExpF r Integer
  Div :: r Integer -> r Integer -> ExpF r Integer
  Mod :: r Integer -> r Integer -> ExpF r Integer
  Exp :: r Integer -> r Integer -> ExpF r Integer
  LitInt :: Integer -> ExpF r Integer
  IntVar :: Id -> ExpF r Integer
  IntEnv :: EthEnv -> ExpF r Integer
  IntStore :: TStorageItem Integer -> ExpF r Integer
  -- bounds
  IntMin :: Int -> ExpF r Integer
  IntMax :: Int -> ExpF r Integer
  UIntMin :: Int -> ExpF r Integer
  UIntMax :: Int -> ExpF r Integer
  -- bytestrings
  Cat :: r ByteString -> r ByteString -> ExpF r ByteString
  Slice :: r ByteString -> r Integer -> r Integer -> ExpF r ByteString
  ByVar :: Id -> ExpF r ByteString
  ByStr :: String -> ExpF r ByteString
  ByLit :: ByteString -> ExpF r ByteString
  ByEnv :: EthEnv -> ExpF r ByteString
  ByStore :: TStorageItem ByteString -> ExpF r ByteString
  -- builtins
  NewAddr :: r Integer -> r Integer -> ExpF r Integer

  -- polymorphic
  Eq  :: (Typeable t, Show t) => r t -> r t -> ExpF r Bool
  NEq :: (Typeable t, Show t) => r t -> r t -> ExpF r Bool
  ITE :: r Bool -> r t -> r t -> ExpF r t

type Exp = Term ExpF

derive
  [makeEqHF, makeShowHF, makeHFunctor, makeHFoldable, makeHTraversable, smartConstructors, smartAConstructors]
  [''ExpF]

fixExp :: Exp t -> ExpF Exp t
fixExp = unTerm

makeExp :: ExpF Exp t -> Exp t
makeExp = Term

instance Semigroup (Exp Bool) where
  a <> b = iAnd a b

instance Monoid (Exp Bool) where
  mempty = iLitBool True

-- intermediate json output helpers ---
instance ToJSON Claim where
  toJSON (S storages) = object [ "kind" .= (String "Storages")
                                          , "storages" .= toJSON storages]
  toJSON (I (Invariant {..})) = object [ "kind" .= (String "Invariant")
                                       , "predicate" .= toJSON _predicate
                                       , "preconditions" .= toJSON _ipreconditions
                                       , "contract" .= _icontract]
  toJSON (C (Constructor {..})) = object  [ "kind" .= (String "Constructor")
                                          , "contract" .= _cname
                                          , "mode" .= (String . pack $ show _cmode)
                                          , "interface" .= (String . pack $ show _cinterface)
                                          , "preConditions" .= (toJSON _cpreconditions)
                                          , "postConditions" .= (toJSON _cpostconditions)
                                          , "storage" .= toJSON _initialStorage
                                          ]
  toJSON (B (Behaviour {..})) = object  [ "kind" .= (String "Behaviour")
                                        , "name" .= _name
                                        , "contract" .= _contract
                                        , "mode" .= (String . pack $ show _mode)
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

-- TODO possibly use cataK instead for consistency...but honestly why?
instance ToJSON (Exp t) where
  toJSON t@(Term e) = case e of
    Add a b -> symbol "+" a b
    Sub a b -> symbol "-" a b
    Exp a b -> symbol "^" a b
    Mul a b -> symbol "*" a b
    Div a b -> symbol "/" a b
    NewAddr a b -> symbol "newAddr" a b
    IntVar a -> String $ pack a
    LitInt a -> toJSON $ show a
    IntMin a -> toJSON $ show $ intmin a
    IntMax a -> toJSON $ show $ intmax a
    UIntMin a -> toJSON $ show $ uintmin a
    UIntMax a -> toJSON $ show $ uintmax a
    IntEnv a -> String $ pack $ show a
    IntStore a -> toJSON a
    ByStore _ -> String . pack . show $ t -- lol just fix the tests instead so we can use toJSON
    ITE a b c -> object [  "symbol"   .= pack "ite"
                        ,  "arity"    .= (Data.Aeson.Types.Number 3)
                        ,  "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c])]
    And a b  -> symbol "and" a b
    Or a b   -> symbol "or" a b
    LE a b   -> symbol "<" a b
    GE a b   -> symbol ">" a b
    Impl a b -> symbol "=>" a b
    NEq a b  -> symbol "=/=" a b
    Eq a b   -> symbol "==" a b
    LEQ a b  -> symbol "<=" a b
    GEQ a b  -> symbol ">=" a b
    LitBool a -> String $ pack $ show a
    BoolVar a -> toJSON a
    BoolStore a -> toJSON a
    Neg a -> object [  "symbol"   .= pack "not"
                    ,  "arity"    .= (Data.Aeson.Types.Number 1)
                    ,  "args"     .= (Array $ fromList [toJSON a])]
    _ -> String . pack . show $ t

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