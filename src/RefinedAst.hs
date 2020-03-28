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
import GHC.Generics
import Data.Map.Strict    (Map)
import qualified Data.Map.Strict      as Map
import Data.ByteString       (ByteString)

import Syntax
import Data.Aeson
import Data.Aeson.Types
import Data.Vector (fromList)
import Data.Char
import Data.List

-- AST post typechecking
data Behaviour = Behaviour
  {_name :: Id,
   _contract :: Id,
   _interface :: Interface,
   _preconditions :: Exp T_Bool,
   _postconditions :: Exp T_Bool,
--   _contracts :: SolcContract,
   _stateUpdates :: Map Id [StorageUpdate],
   _returns :: Maybe ReturnExp
  }

--types understood by proving tools
data MType 
  = Integer
  | Boolean
  | ByteStr
  | Mapping (Map MType MType)
  deriving (Eq, Ord, Show, Read)

-- meta types that work as GADT "tags"
data T_Int
data T_Bool
data T_Bytes
--data T_List t
data T_Tuple

data StorageUpdate
  = IntUpdate (TContainer () T_Int) (Exp T_Int)
  | BoolUpdate (TContainer () T_Bool) (Exp T_Bool)
  | BytesUpdate (TContainer () T_Bytes) (Exp T_Bytes)
  deriving (Show)

data TContainer s t where --
  DirectInt    :: Id -> TContainer () T_Int
  DirectBool   :: Id -> TContainer () T_Bool
  DirectBytes  :: Id -> TContainer () T_Bytes
  --constructors
  IntIndexed   :: TContainer a t -> TContainer (T_Int,a) t
  BoolIndexed  :: TContainer a t -> TContainer (T_Bool,a) t
  BytesIndexed :: TContainer a t -> TContainer (T_Bytes,a) t
  --destructor
  Lookup   :: TContainer (a,b) t -> Exp a -> TContainer b t
deriving instance Show (TContainer a t)

-- typed expressions
data Exp t where
  --booleans
  And  :: Exp T_Bool -> Exp T_Bool -> Exp T_Bool
  Or   :: Exp T_Bool -> Exp T_Bool -> Exp T_Bool
  Impl :: Exp T_Bool -> Exp T_Bool -> Exp T_Bool
  Eq  :: Exp T_Int -> Exp T_Int -> Exp T_Bool --TODO: make polymorphic
  NEq  :: Exp t -> Exp t -> Exp T_Bool
  Neg :: Exp T_Bool -> Exp T_Bool
  LE :: Exp T_Int -> Exp T_Int -> Exp T_Bool
  LEQ :: Exp T_Int -> Exp T_Int -> Exp T_Bool
  GEQ :: Exp T_Int -> Exp T_Int -> Exp T_Bool
  GE :: Exp T_Int -> Exp T_Int -> Exp T_Bool
  LitBool :: Bool -> Exp T_Bool
  BoolVar :: Id -> Exp T_Bool
  -- integers
  Add :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Sub :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Mul :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Div :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Mod :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Exp :: Exp T_Int -> Exp T_Int -> Exp T_Int
  LitInt :: Integer -> Exp T_Int
  IntVar :: Id -> Exp T_Int
  IntEnv :: EthEnv -> Exp T_Int
  -- bytestrings
  Cat :: Exp T_Bytes -> Exp T_Bytes -> Exp T_Bytes
  Slice :: Exp T_Bytes -> Exp T_Int -> Exp T_Int -> Exp T_Bytes
  ByVar :: Id -> Exp T_Bytes
  ByStr :: String -> Exp T_Bytes
  ByLit :: ByteString -> Exp T_Bytes
  --polymorphic
  ITE :: Exp T_Bool -> Exp t -> Exp t
  TEntry :: (TContainer () t) -> Exp t
  
deriving instance Show (Exp t)

data ReturnExp
  = ExpInt    (Exp T_Int)
  | ExpBool   (Exp T_Bool)
  | ExpBytes  (Exp T_Bytes)
  | ExpTuple  (Exp T_Tuple)
  deriving (Show)

-- intermediate json output helpers ---
instance ToJSON Behaviour where
  toJSON (Behaviour {..}) = object  [ "name" .= _name
                                    , "contract"  .= _contract
                                    , "interface"  .= (String . pack $ show _interface)
                                    , "preConditions"   .= (toJSON _preconditions)
                                    , "stateUpdates" .= toJSON _stateUpdates
                                    , "returns" .= toJSON _returns]


instance ToJSON StorageUpdate where
  toJSON (IntUpdate a b) = object ["location" .= toJSON a
                                  ,"value"    .= toJSON b]

instance ToJSON (TContainer a b) where
  toJSON (DirectInt a) = String $ pack a
  toJSON (DirectBool a) = String $ pack a
  toJSON (DirectBytes a) = String $ pack a
  toJSON (Lookup (IntIndexed a) b) = object ["symbol" .= pack "lookup",
                                             "arity"  .= (Number 2),
                                             "args"   .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (Lookup (BoolIndexed a) b) = object ["symbol" .= pack "lookup",
                                              "arity"  .= (Number 2),
                                              "args"   .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (Lookup (BytesIndexed a) b) = object ["symbol" .= pack "lookup",
                                               "arity"  .= (Number 2),
                                               "args"   .= (Array $ fromList [toJSON a, toJSON b])]

instance ToJSON ReturnExp where
   toJSON (ExpInt a) = object ["sort" .= (pack "int")
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= (String $ pack "bool")
                               ,"expression" .= toJSON a]
   -- toJSON (ExpTuple a) = object ["sort" .= (String $ pack "tuple")
   --                              ,"expression" .= toJSON a]


instance ToJSON (Exp T_Int) where
  toJSON (Add a b) = object [   "symbol"   .= pack "+"
                             ,  "arity"    .= (Number 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (TEntry a) = toJSON a
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp T_Bool) where
  toJSON (And a b) = object [   "symbol"   .= pack "and"
                             ,  "arity"    .= (Number 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (LE a b) = object [   "symbol"   .= pack "<"
                             ,  "arity"    .= (Number 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (Eq a b) = object [   "symbol"   .= pack "="
                             ,  "arity"    .= (Number 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (LEQ a b) = object [   "symbol"   .= pack "<="
                             ,  "arity"    .= (Number 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (LitBool a) = String $ pack $ show a
  toJSON (Neg a) = object [   "symbol"   .= pack "not"
                             ,  "arity"    .= (Number 1)
                             ,  "args"     .= (Array $ fromList [toJSON a])]
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp T_Bytes) where
  toJSON a = String $ pack $ show a
