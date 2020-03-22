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
import Data.Bits
import Data.Char

import Data.Text          (Text, pack)
import Data.Vector        (Vector)
import Data.Word          (Word32, Word8)
import Data.Sequence        (Seq)

import Numeric (readHex, showHex)
-- AST post typechecking
data Behaviour = Behaviour
  {_name :: Id,
   _contract :: Id,
   _interface :: (Id, [Decl]),
   _preconditions :: [Exp T_Bool],
   _postconditions :: [Exp T_Bool],
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
--  deriving (Eq, Ord, Show, Read)

--type Claim = (Map Contract [OldStorageUpdate], Maybe (TypedExp))

-- the type var a holds the type of the return expression
--data Claim = Claim (Map Text [StorageUpdate]) (Maybe (ReturnExp))
--  deriving (Eq, Ord, Show, Read)

--type OldStorageUpdate = (Entry, TypedExp)


-- meta types that work as GADT "tags"
--data MType = Int T_Int | Bool T_Bool | Mapp Mapping k a
data T_Int
data T_Bool
data T_Bytes
data T_List t
data T_Tuple
data Mapping a b

--token = [("totalSupply", Integer), ("balanceOf", Map Integer Integer)]

--updates = [("totalSupply", VarInt
data StorageUpdate
  = IntUpdate (TEntry T_Int) (Exp T_Int)
  | BoolUpdate (TEntry T_Bool) (Exp T_Bool)
  | BytesUpdate (TEntry T_Bytes) (Exp T_Bytes)
--  deriving (Eq, Ord, Show, Read)

--totalSupply[msg.sender] => Exp T_Int

--Map Id MType

data TContainer t where --
  DirectInt    :: TContainer T_Int
  DirectBool   :: TContainer T_Bool
  DirectBytes  :: TContainer T_Bytes
  IntIndexed   :: TContainer T_Int -> TContainer t -> TContainer (Mapping T_Int t)
  BoolIndexed  :: TContainer T_Int -> TContainer t -> TContainer (Mapping T_Int t)
  BytesIndexed :: TContainer T_Int -> TContainer t -> TContainer (Mapping T_Int t)
deriving instance Show (TContainer t)

--   Direct ::  Id -> Container t
-- --  Mapping :: Id -> Container (a -> b)
-- deriving instance Show (Container t)

data TEntry t where
  Simple :: TContainer t -> TEntry t
  Lookup :: TContainer (Mapping a b) -> Exp a -> TEntry b
deriving instance Show (TEntry t)

-- data TEntry a where
--   IntEntry  :: TEntry 'Integer
--   BoolEntry :: TEntry 'Boolean
--   LookEntry :: 'Mapp a b c -> Exp b -> TEntry c
-- data MType typ where 
--   Integer  :: MType T_Int
--   Boolean  :: MType T_Bool
--   MapContainer  :: TEntry a -> TEntry b -> TEntry (Mapping a b)
-- --  MapEntry     :: forall k a. Id -> TEntry (Mapping k a)
--   TLookup    :: (TEntry (Mapping k a)) -> (Exp k) -> TEntry a

--deriving instance Show (TEntry t)
--  Struct  :: (TEntry (Mapping k a)) -> (TExp k) -> TEntry a

-- data TExp typ where
--   Int  :: IExp -> TExp T_Int
--   Bool :: BExp -> TExp T_Bool
--   List :: [TExp t] -> TExp (T_List t)
--  deriving (Show)

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
  
deriving instance Show (Exp t)

data ReturnExp
  = ExpInt    (Exp T_Int)
  | ExpBool   (Exp T_Bool)
  | ExpBytes  (Exp T_Bytes)
  | ExpTuple  (Exp T_Tuple)
  deriving (Show)

--instance ToJSON (Exp ('T_Int)) where

instance ToJSON Behaviour where
  toJSON (Behaviour {..}) = object  [ "name" .= _name
                                    , "contract"  .= _contract
                                    , "interface"  .= (pack $ show (fst _interface) <> show (snd _interface))
                                    , "preConditions"   .= (Array $ fromList $ fmap toJSON _preconditions)
                                    , "returns" .= toJSON _returns]


instance ToJSON ReturnExp where
   toJSON (ExpInt a) = object ["sort" .= (pack "int")
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= (String $ pack "bool")
                               ,"expression" .= toJSON a]
   -- toJSON (ExpTuple a) = object ["sort" .= (String $ pack "tuple")
   --                              ,"expression" .= toJSON a]


instance ToJSON (Exp T_Int) where
  toJSON (Add a b) = object [   "symbol"   .= (String $ pack "+")
                             ,  "arity"    .= (Number $ 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp T_Bool) where
  toJSON (And a b) = object [   "symbol"   .= pack "and"
                             ,  "arity"    .= (Number $ 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (LE a b) = object [   "symbol"   .= pack "<"
                             ,  "arity"    .= (Number $ 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (Eq a b) = object [   "symbol"   .= pack "="
                             ,  "arity"    .= (Number $ 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON (LEQ a b) = object [   "symbol"   .= pack "<="
                             ,  "arity"    .= (Number $ 2)
                             ,  "args"     .= (Array $ fromList [toJSON a, toJSON b])]
  toJSON v = error $ "todo: json ast for: " <> show v
