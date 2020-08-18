{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# Language DeriveAnyClass #-}
module RefinedAst where
import Data.Text          (Text, pack, unpack)
import Data.List (filter)
import GHC.Generics
import Data.Map.Strict    (Map)
import Data.List.NonEmpty hiding (fromList)
import Data.ByteString       (ByteString)

import Syntax
import Data.Aeson
import Data.Aeson.Types
import Data.Vector (fromList)

-- AST post typechecking
data Claim = B Behaviour | I Invariant

data Invariant = Invariant Id (Exp Bool)
data Behaviour = Behaviour
  {_name :: Id,
   _mode :: Mode,
   _creation :: Bool,
   _contract :: Id,
   _interface :: Interface,
   _preconditions :: Exp Bool,
   _postconditions :: Exp Bool,
   _contracts :: [Id], -- can maybe be removed; should be equivalent to Map.keys(_stateupdates)
   _stateUpdates :: Map Id [Either StorageLocation StorageUpdate],
   _returns :: Maybe ReturnExp
  }

catInvs :: [Claim] -> [Invariant]
catInvs = fmap unwrapI . Data.List.filter isI
  where
    isI (B _) = False
    isI (I _) = True
    unwrapI (I i) = i

catBehvs :: [Claim] -> [Behaviour]
catBehvs = fmap unwrapB . Data.List.filter isB
  where
    isB (B _) = True
    isB (I _) = False
    unwrapB (B i) = i

conjunction :: [Invariant] -> Exp Bool
conjunction [] = LitBool True
conjunction (hd@(Invariant _ exp):tl) = And exp (conjunction tl)

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

--data T_List t
--data T_Tuple

data StorageUpdate
  = IntUpdate (TStorageItem Int) (Exp Int)
  | BoolUpdate (TStorageItem Bool) (Exp Bool)
  | BytesUpdate (TStorageItem ByteString) (Exp ByteString)
  deriving (Show)

data StorageLocation
  = IntLoc (TStorageItem Int)
  | BoolLoc (TStorageItem Bool)
  | BytesLoc (TStorageItem ByteString)
  deriving (Show)


data TStorageItem a where
  DirectInt    :: Id -> TStorageItem Int
  DirectBool   :: Id -> TStorageItem Bool
  DirectBytes  :: Id -> TStorageItem ByteString
  MappedInt    :: Id -> NonEmpty ReturnExp -> TStorageItem Int
  MappedBool   :: Id -> NonEmpty ReturnExp -> TStorageItem Bool
  MappedBytes  :: Id -> NonEmpty ReturnExp -> TStorageItem ByteString

deriving instance Show (TStorageItem a)
-- typed expressions
data Exp t where
  --booleans
  And  :: Exp Bool -> Exp Bool -> Exp Bool
  Or   :: Exp Bool -> Exp Bool -> Exp Bool
  Impl :: Exp Bool -> Exp Bool -> Exp Bool
  Eq  :: Exp Int -> Exp Int -> Exp Bool --TODO: make polymorphic (how to ToJSON.encode them?)
  NEq  :: Exp Int -> Exp Int -> Exp Bool
  Neg :: Exp Bool -> Exp Bool
  LE :: Exp Int -> Exp Int -> Exp Bool
  LEQ :: Exp Int -> Exp Int -> Exp Bool
  GEQ :: Exp Int -> Exp Int -> Exp Bool
  GE :: Exp Int -> Exp Int -> Exp Bool
  LitBool :: Bool -> Exp Bool
  BoolVar :: Id -> Exp Bool
  -- integers
  Add :: Exp Int -> Exp Int -> Exp Int
  Sub :: Exp Int -> Exp Int -> Exp Int
  Mul :: Exp Int -> Exp Int -> Exp Int
  Div :: Exp Int -> Exp Int -> Exp Int
  Mod :: Exp Int -> Exp Int -> Exp Int
  Exp :: Exp Int -> Exp Int -> Exp Int
  LitInt :: Integer -> Exp Int
  IntVar :: Id -> Exp Int
  IntEnv :: EthEnv -> Exp Int
  -- bytestrings
  Cat :: Exp ByteString -> Exp ByteString -> Exp ByteString
  Slice :: Exp ByteString -> Exp Int -> Exp Int -> Exp ByteString
  ByVar :: Id -> Exp ByteString
  ByStr :: String -> Exp ByteString
  ByLit :: ByteString -> Exp ByteString
  ByEnv :: EthEnv -> Exp ByteString
  -- builtins
  NewAddr :: Exp Int -> Exp Int -> Exp Int
  
  --polymorphic
  ITE :: Exp Bool -> Exp t -> Exp t -> Exp t
  TEntry :: (TStorageItem t) -> Exp t
  
deriving instance Show (Exp t)

instance Semigroup (Exp Bool) where
  a <> b = And a b

instance Monoid (Exp Bool) where
  mempty = LitBool True

data ReturnExp
  = ExpInt    (Exp Int)
  | ExpBool   (Exp Bool)
  | ExpBytes  (Exp ByteString)
  deriving (Show)

-- intermediate json output helpers ---
instance ToJSON Claim where
  toJSON (I (Invariant contract exp)) = object [ "kind" .= (String "Invariant")
                                               , "expression" .= toJSON exp
                                               , "contract" .= toJSON contract ]
  toJSON (B (Behaviour {..})) = object  [ "kind" .= (String "Behaviour")
                                        , "name" .= _name
                                        , "contract" .= _contract
                                        , "mode" .= (String . pack $ show _mode)
                                        , "creation" .= _creation
                                        , "interface" .= (String . pack $ show _interface)
                                        , "preConditions" .= (toJSON _preconditions)
                                        , "postConditions" .= (toJSON _postconditions)
                                        , "stateUpdates" .= toJSON _stateUpdates
                                        , "contracts" .= toJSON _contracts
                                        , "returns" .= toJSON _returns]

instance ToJSON StorageLocation where
  toJSON (IntLoc a) = object ["location" .= toJSON a]
  toJSON (BoolLoc a) = object ["location" .= toJSON a]
  toJSON (BytesLoc a) = object ["location" .= toJSON a]

instance ToJSON StorageUpdate where
  toJSON (IntUpdate a b) = object ["location" .= toJSON a ,"value"    .= toJSON b]
  toJSON (BoolUpdate a b) = object ["location" .= toJSON a ,"value"    .= toJSON b]
  toJSON (BytesUpdate a b) = object ["location" .= toJSON a ,"value"    .= toJSON b]

instance ToJSON (TStorageItem b) where
  toJSON (DirectInt a) = String $ pack a
  toJSON (DirectBool a) = String $ pack a
  toJSON (DirectBytes a) = String $ pack a
  toJSON (MappedInt a b) = symbol "lookup" a b
  toJSON (MappedBool a b) = symbol "lookup" a b
  toJSON (MappedBytes a b) = symbol "lookup" a b

instance ToJSON ReturnExp where
   toJSON (ExpInt a) = object ["sort" .= (pack "int")
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= (String $ pack "bool")
                               ,"expression" .= toJSON a]
   toJSON (ExpBytes a) = object ["sort" .= (String $ pack "bytestring")
                               ,"expression" .= toJSON a]
   -- toJSON (ExpTuple a) = object ["sort" .= (String $ pack "tuple")
   --                              ,"expression" .= toJSON a]


instance ToJSON (Exp Int) where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (Mul a b) = symbol "*" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON a
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
  toJSON (Neg a) = object [   "symbol"   .= pack "not"
                          ,  "arity"    .= (Data.Aeson.Types.Number 1)
                          ,  "args"     .= (Array $ fromList [toJSON a])]
  toJSON v = error $ "todo: json ast for: " <> show v

symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= (Data.Aeson.Types.Number 2)
                      ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]


instance ToJSON (Exp ByteString) where
  toJSON a = String $ pack $ show a
