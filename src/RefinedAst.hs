{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# Language DeriveAnyClass #-}
module RefinedAst where
import Data.Text          (Text, pack, unpack)
import GHC.Generics
import Data.Map.Strict    (Map)
import Data.List.NonEmpty hiding (fromList)
import Data.ByteString       (ByteString)

import Syntax
import Data.Aeson
import Data.Aeson.Types
import Data.Vector (fromList)

-- AST post typechecking
data Behaviour = Behaviour
  {_name :: Id,
   _mode :: Mode,
   _creation :: Bool,
   _contract :: Id,
   _interface :: Interface,
   _preconditions :: ExpBool,
   _postconditions :: ExpBool,
   _contracts :: [Id], -- can maybe be removed; should be equivalent to Map.keys(_stateupdates)
   _stateUpdates :: Map Id [Either StorageLocation StorageUpdate],
   _returns :: Maybe ReturnExp
  }

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
  = IntUpdate StorageInt ExpInt
  | BoolUpdate StorageBool ExpBool
  | BytesUpdate StorageBytes ExpBytes
  deriving (Show)

data StorageLocation
  = IntLoc StorageInt
  | BoolLoc StorageBool
  | BytesLoc StorageBytes
  deriving (Show)

data StorageInt
  = DirectInt Id
  | MappedInt Id (NonEmpty ReturnExp)
  deriving Show

data StorageBool
  = DirectBool Id
  | MappedBool Id (NonEmpty ReturnExp)
  deriving Show

data StorageBytes
  = DirectBytes Id
  | MappedBytes Id (NonEmpty ReturnExp)
  deriving Show

-- typed expressions
data ExpInt
  = Add ExpInt ExpInt
  | Sub ExpInt ExpInt
  | Mul ExpInt ExpInt
  | Div ExpInt ExpInt
  | Mod ExpInt ExpInt
  | Exp ExpInt ExpInt
  | LitInt Integer
  | IntVar Id
  | IntEnv EthEnv
  | NewAddr ExpInt ExpInt
  | ITE ExpBool ExpInt ExpInt
  | IntEntry StorageInt
  deriving Show

data ExpBool
  = And  ExpBool ExpBool
  | Or   ExpBool ExpBool
  | Impl ExpBool ExpBool
  | Eq   ExpInt  ExpInt
  | NEq  ExpInt  ExpInt
  | Neg  ExpBool
  | LE   ExpInt ExpInt
  | LEQ  ExpInt ExpInt
  | GEQ  ExpInt ExpInt
  | GE   ExpInt ExpInt
  | LitBool Bool
  | BoolVar Id
  | BoolEntry StorageBool
  deriving Show

data ExpBytes
  = Cat ExpBytes ExpBytes
  | Slice ExpBytes ExpInt ExpInt
  | ByVar Id
  | ByStr String
  | ByLit ByteString
  | ByEnv EthEnv
  | BytesEntry StorageBytes
  deriving Show  

instance Semigroup (ExpBool) where
  a <> b = And a b

instance Monoid (ExpBool) where
  mempty = LitBool True

data ReturnExp
  = RInt   ExpInt
  | RBool  ExpBool
  | RBytes ExpBytes
  deriving (Show)

-- intermediate json output helpers ---
instance ToJSON Behaviour where
  toJSON (Behaviour {..}) = object
    [ "name" .= _name
    , "contract"  .= _contract
    , "mode" .= (String . pack $ show _mode)
    , "creation" .= _creation
    , "interface"  .= (String . pack $ show _interface)
    , "preConditions"   .= (toJSON _preconditions)
    , "stateUpdates" .= toJSON _stateUpdates
    , "contracts" .= toJSON _contracts
    , "returns" .= toJSON _returns
    ]
  

instance ToJSON StorageLocation where
  toJSON (IntLoc a) = object ["location" .= toJSON a]


instance ToJSON StorageUpdate where
  toJSON (IntUpdate a b) = object ["location" .= toJSON a
                                  ,"value"    .= toJSON b]

instance ToJSON StorageInt where
  toJSON (DirectInt a) = String $ pack a
  toJSON (MappedInt a b) = symbol "lookup" a b 

instance ToJSON StorageBool where
  toJSON (DirectBool a) = String $ pack a
  toJSON (MappedBool a b) = symbol "lookup" a b 

instance ToJSON StorageBytes where
  toJSON (DirectBytes a) = String $ pack a
  toJSON (MappedBytes a b) = symbol "lookup" a b 

instance ToJSON ReturnExp where
   toJSON (RInt a) = object ["sort" .= (pack "int")
                              ,"expression" .= toJSON a]
   toJSON (RBool a) = object ["sort" .= (String $ pack "bool")
                               ,"expression" .= toJSON a]
   -- toJSON (ExpTuple a) = object ["sort" .= (String $ pack "tuple")
   --                              ,"expression" .= toJSON a]


instance ToJSON ExpInt where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (IntEntry a) = toJSON a
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON ExpBool where
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


instance ToJSON ExpBytes where
  toJSON a = String $ pack $ show a
