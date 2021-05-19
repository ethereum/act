{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# LANGUAGE MonadComprehensions #-}

module RefinedAst where

import Control.Applicative (empty)

import Data.List (genericDrop,genericTake)
import Data.Text (pack)
import Data.Type.Equality
import Data.Typeable
import Data.Map.Strict (Map)
import Data.List.NonEmpty hiding (fromList)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.String (fromString)

import EVM.Solidity (SlotType(..))

import Syntax (Id, Interface, EthEnv)
import Data.Aeson
import Data.Aeson.Types
import Data.Vector (fromList)


-- AST post typechecking
data Claim = C Constructor | B Behaviour | I Invariant | S Store deriving (Show, Eq)

data Transition = Ctor Constructor | Behv Behaviour deriving (Show, Eq)

type Store = Map Id (Map Id SlotType)

-- | Represents a contract level invariant along with some associated metadata.
-- The invariant is defined in the context of the constructor, but must also be
-- checked against each behaviour in the contract, and thus may reference variables
-- that are not present in a given behaviour (constructor args, or storage
-- variables that are not referenced in the behaviour), so we additionally
-- attach some constraints over the variables referenced by the predicate in
-- the `_ipreconditions` and `_istoragebounds` fields. These fields are
-- seperated as the constraints derived from the types of the storage
-- references must be treated differently in the constructor specific queries
-- (as the storage variables have no prestate in the constructor...), wheras
-- the constraints derived from the types of the environment variables and
-- calldata args (stored in _ipreconditions) have a uniform semantics over both
-- the constructor and behaviour claims.
data Invariant = Invariant
  { _icontract :: Id
  , _ipreconditions :: [Exp Untimed Bool]
  , _istoragebounds :: [Exp Untimed Bool]
  , _predicate :: Exp Untimed Bool
  } deriving (Show, Eq)

data Constructor = Constructor
  { _cname :: Id
  , _cmode :: Mode
  , _cinterface :: Interface
  , _cpreconditions :: [Exp Untimed Bool]
  , _cpostconditions :: [Exp Timed Bool]
  , _initialStorage :: [StorageUpdate]
  , _cstateUpdates :: [Either StorageLocation StorageUpdate]
  } deriving (Show, Eq)

data Behaviour = Behaviour
  { _name :: Id
  , _mode :: Mode
  , _contract :: Id
  , _interface :: Interface
  , _preconditions :: [Exp Untimed Bool]
  , _postconditions :: [Exp Timed Bool]
  , _stateUpdates :: [Either StorageLocation StorageUpdate]
  , _returns :: Maybe ReturnExp
  } deriving (Show, Eq)

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
  deriving (Eq, Ord, Show, Read)

data StorageUpdate
  = IntUpdate (TStorageItem Integer) (Exp Untimed Integer)
  | BoolUpdate (TStorageItem Bool) (Exp Untimed Bool)
  | BytesUpdate (TStorageItem ByteString) (Exp Untimed ByteString)
  deriving (Show, Eq)

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
data Exp time t where
  -- booleans
  And  :: Exp time Bool -> Exp time Bool -> Exp time Bool
  Or   :: Exp time Bool -> Exp time Bool -> Exp time Bool
  Impl :: Exp time Bool -> Exp time Bool -> Exp time Bool
  Neg :: Exp time Bool -> Exp time Bool
  LE :: Exp time Integer -> Exp time Integer -> Exp time Bool
  LEQ :: Exp time Integer -> Exp time Integer -> Exp time Bool
  GEQ :: Exp time Integer -> Exp time Integer -> Exp time Bool
  GE :: Exp time Integer -> Exp time Integer -> Exp time Bool
  LitBool :: Bool -> Exp time Bool
  TBoolVar :: Timed -> Id -> Exp Timed Bool
  UTBoolVar :: Id -> Exp Untimed Bool
  -- integers
  Add :: Exp time Integer -> Exp time Integer -> Exp time Integer
  Sub :: Exp time Integer -> Exp time Integer -> Exp time Integer
  Mul :: Exp time Integer -> Exp time Integer -> Exp time Integer
  Div :: Exp time Integer -> Exp time Integer -> Exp time Integer
  Mod :: Exp time Integer -> Exp time Integer -> Exp time Integer
  Exp :: Exp time Integer -> Exp time Integer -> Exp time Integer
  LitInt :: Integer -> Exp time Integer
  TIntVar :: Timed -> Id -> Exp Timed Integer
  UTIntVar :: Id -> Exp Untimed Integer
  IntEnv :: EthEnv -> Exp time Integer
  -- bounds
  IntMin :: Int -> Exp time Integer
  IntMax :: Int -> Exp time Integer
  UIntMin :: Int -> Exp time Integer
  UIntMax :: Int -> Exp time Integer
  -- bytestrings
  Cat :: Exp time ByteString -> Exp time ByteString -> Exp time ByteString
  Slice :: Exp time ByteString -> Exp time Integer -> Exp time Integer -> Exp time ByteString
  TByVar :: Timed -> Id -> Exp Timed ByteString
  UTByVar :: Id -> Exp Untimed ByteString
  ByStr :: String -> Exp time ByteString
  ByLit :: ByteString -> Exp time ByteString
  ByEnv :: EthEnv -> Exp time ByteString
  -- builtins
  NewAddr :: Exp time Integer -> Exp time Integer -> Exp time Integer

  -- polymorphic
  Eq  :: (Eq t, Typeable t, ToJSON (Exp time t)) => Exp time t -> Exp time t -> Exp time Bool
  NEq :: (Eq t, Typeable t, ToJSON (Exp time t)) => Exp time t -> Exp time t -> Exp time Bool
  ITE :: Exp time Bool -> Exp time t -> Exp time t -> Exp time t
  UTEntry :: TStorageItem t -> Exp Untimed t
  TEntry :: Timed -> TStorageItem t -> Exp Timed t

deriving instance Show (Exp time t)

data Untimed
  deriving Typeable
data Timed = Pre | Post
  deriving (Eq, Typeable)

instance Show Timed where
  show Pre  = "pre"
  show Post = "post"

instance Eq (Exp time t) where
  And a b == And c d = a == c && b == d
  Or a b == Or c d = a == c && b == d
  Impl a b == Impl c d = a == c && b == d
  Neg a == Neg b = a == b
  LE a b == LE c d = a == c && b == d
  LEQ a b == LEQ c d = a == c && b == d
  GEQ a b == GEQ c d = a == c && b == d
  GE a b == GE c d = a == c && b == d
  LitBool a == LitBool b = a == b
  UTBoolVar a == UTBoolVar b = a == b
  TBoolVar t a == TBoolVar t' b = a == b && t == t'

  Add a b == Add c d = a == c && b == d
  Sub a b == Sub c d = a == c && b == d
  Mul a b == Mul c d = a == c && b == d
  Div a b == Div c d = a == c && b == d
  Mod a b == Mod c d = a == c && b == d
  Exp a b == Exp c d = a == c && b == d
  LitInt a == LitInt b = a == b
  UTIntVar a == UTIntVar b = a == b
  TIntVar t a == TIntVar t' b = a == b && t == t'
  IntEnv a == IntEnv b = a == b

  IntMin a == IntMin b = a == b
  IntMax a == IntMax b = a == b
  UIntMin a == UIntMin b = a == b
  UIntMax a == UIntMax b = a == b

  Cat a b == Cat c d = a == c && b == d
  Slice a b c == Slice d e f = a == d && b == e && c == f
  UTByVar a == UTByVar b = a == b
  TByVar t a == TByVar t' b = a == b && t == t'
  ByStr a == ByStr b = a == b
  ByLit a == ByLit b = a == b
  ByEnv a == ByEnv b = a == b

  NewAddr a b == NewAddr c d = a == c && b == d

  Eq (a :: Exp time t1) (b :: Exp time t1) == Eq (c :: Exp time t2) (d :: Exp time t2) =
    case eqT @t1 @t2 of
      Just Refl -> a == c && b == d
      Nothing -> False
  NEq (a :: Exp time t1) (b :: Exp time t1) == NEq (c :: Exp time t2) (d :: Exp time t2) =
    case eqT @t1 @t2 of
      Just Refl -> a == c && b == d
      Nothing -> False
  ITE a b c == ITE d e f = a == d && b == e && c == f
  UTEntry a == UTEntry b = a == b
  TEntry t a == TEntry t' b = a == b && t == t'

  _ == _ = False

instance Semigroup (Exp time Bool) where
  a <> b = And a b

instance Monoid (Exp time Bool) where
  mempty = LitBool True

data ReturnExp
  = ExpInt    (Exp Untimed Integer)
  | ExpBool   (Exp Untimed Bool)
  | ExpBytes  (Exp Untimed ByteString)
  deriving (Eq, Show)

-- | Simplifies concrete expressions into literals.
-- Returns `Nothing` if the expression contains symbols.
eval :: Exp t a -> Maybe a
eval e = case e of
  And  a b    -> [a' && b' | a' <- eval a, b' <- eval b]
  Or   a b    -> [a' || b' | a' <- eval a, b' <- eval b]
  Impl a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  Neg  a      -> not <$> eval a
  LE   a b    -> [a' <  b' | a' <- eval a, b' <- eval b]
  LEQ  a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  GE   a b    -> [a' >  b' | a' <- eval a, b' <- eval b]
  GEQ  a b    -> [a' >= b' | a' <- eval a, b' <- eval b]
  LitBool a   -> pure a
  BoolVar _   -> empty

  Add a b     -> [a' + b'     | a' <- eval a, b' <- eval b]
  Sub a b     -> [a' - b'     | a' <- eval a, b' <- eval b]
  Mul a b     -> [a' * b'     | a' <- eval a, b' <- eval b]
  Div a b     -> [a' `div` b' | a' <- eval a, b' <- eval b]
  Mod a b     -> [a' `mod` b' | a' <- eval a, b' <- eval b]
  Exp a b     -> [a' ^ b'     | a' <- eval a, b' <- eval b]
  LitInt a    -> pure a
  IntVar _    -> empty
  IntEnv _    -> empty
  IntMin  a   -> pure . negate $ 2 ^ (a - 1)
  IntMax  a   -> pure $ 2 ^ (a - 1) - 1
  UIntMin _   -> pure 0
  UIntMax a   -> pure $ 2 ^ a - 1

  Cat s t     -> [s' <> t' | s' <- eval s, t' <- eval t]
  Slice s a b -> [BS.pack . genericDrop a' . genericTake b' $ s'
                           | s' <- BS.unpack <$> eval s
                           , a' <- eval a
                           , b' <- eval b]
  ByVar _     -> empty
  ByStr s     -> pure . fromString $ s
  ByLit s     -> pure s
  ByEnv _     -> empty

  NewAddr _ _ -> empty

  Eq a b      -> [a' == b' | a' <- eval a, b' <- eval b]
  NEq a b     -> [a' /= b' | a' <- eval a, b' <- eval b]
  ITE a b c   -> eval a >>= \cond -> if cond then eval b else eval c
  UTEntry _   -> empty
  PreEntry _  -> empty
  PostEntry _ -> empty

-- intermediate json output helpers ---
instance ToJSON Claim where
  toJSON (S storages) = object [ "kind" .= String "Storages"
                               , "storages" .= toJSON storages]
  toJSON (I (Invariant {..})) = object [ "kind" .= String "Invariant"
                                       , "predicate" .= toJSON _predicate
                                       , "preconditions" .= toJSON _ipreconditions
                                       , "storagebounds" .= toJSON _istoragebounds
                                       , "contract" .= _icontract]
  toJSON (C (Constructor {..})) = object  [ "kind" .= String "Constructor"
                                          , "contract" .= _cname
                                          , "mode" .= (String . pack $ show _cmode)
                                          , "interface" .= (String . pack $ show _cinterface)
                                          , "preConditions" .= toJSON _cpreconditions
                                          , "postConditions" .= toJSON _cpostconditions
                                          , "storage" .= toJSON _initialStorage
                                          ]
  toJSON (B (Behaviour {..})) = object  [ "kind" .= String "Behaviour"
                                        , "name" .= _name
                                        , "contract" .= _contract
                                        , "mode" .= (String . pack $ show _mode)
                                        , "interface" .= (String . pack $ show _interface)
                                        , "preConditions" .= toJSON _preconditions
                                        , "postConditions" .= toJSON _postconditions
                                        , "stateUpdates" .= toJSON _stateUpdates
                                        , "returns" .= toJSON _returns]

instance ToJSON SlotType where
  toJSON (StorageValue t) = object ["type" .= show t]
  toJSON (StorageMapping ixTypes valType) = object [ "type" .= String "mapping"
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
  toJSON (DirectInt a b) = object ["sort" .= pack "int"
                                  , "name" .= String (pack a <> "." <> pack b)]
  toJSON (DirectBool a b) = object ["sort" .= pack "bool"
                                   , "name" .= String (pack a <> "." <> pack b)]
  toJSON (DirectBytes a b) = object ["sort" .= pack "bytes"
                                    , "name" .= String (pack a <> "." <> pack b)]
  toJSON (MappedInt a b c) = mapping a b c
  toJSON (MappedBool a b c) = mapping a b c
  toJSON (MappedBytes a b c) = mapping a b c

instance ToJSON ReturnExp where
   toJSON (ExpInt a) = object ["sort" .= pack "int"
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= String (pack "bool")
                               ,"expression" .= toJSON a]
   toJSON (ExpBytes a) = object ["sort" .= String (pack "bytestring")
                               ,"expression" .= toJSON a]

instance ToJSON (Exp time Integer) where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (Mul a b) = symbol "*" a b
  toJSON (Div a b) = symbol "/" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  toJSON (UTIntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON $ show a
  toJSON (IntMin a) = toJSON $ show $ intmin a
  toJSON (IntMax a) = toJSON $ show $ intmax a
  toJSON (UIntMin a) = toJSON $ show $ uintmin a
  toJSON (UIntMax a) = toJSON $ show $ uintmax a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (UTEntry a) = toJSON a
  toJSON (TEntry t a) = unary (show t) a
  toJSON (ITE a b c) = object [  "symbol"   .= pack "ite"
                              ,  "arity"    .= Data.Aeson.Types.Number 3
                              ,  "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c])]
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp time Bool) where
  toJSON (And a b)  = symbol "and" a b
  toJSON (Or a b)   = symbol "or" a b
  toJSON (LE a b)   = symbol "<" a b
  toJSON (GE a b)   = symbol ">" a b
  toJSON (Impl a b) = symbol "=>" a b
  toJSON (NEq a b)  = symbol "=/=" a b
  toJSON (Eq a b)   = symbol "==" a b
  toJSON (LEQ a b)  = symbol "<=" a b
  toJSON (GEQ a b)  = symbol ">=" a b
  toJSON (LitBool a) = String $ pack $ show a
  toJSON (UTBoolVar a) = toJSON a
  toJSON (TBoolVar t a) = unary (show t) a
  toJSON (Neg a) = object [  "symbol"   .= pack "not"
                          ,  "arity"    .= Data.Aeson.Types.Number 1
                          ,  "args"     .= Array (fromList [toJSON a])]
  toJSON v = error $ "todo: json ast for: " <> show v

instance ToJSON (Exp time ByteString) where
  toJSON a = String $ pack $ show a


mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
mapping c a b = object [  "symbol"   .= pack "lookup"
                       ,  "arity"    .= Data.Aeson.Types.Number 3
                       ,  "args"     .= Array (fromList [toJSON c, toJSON a, toJSON b])]

symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= Data.Aeson.Types.Number 2
                      ,  "args"     .= Array (fromList [toJSON a, toJSON b])]

unary :: (Show s, ToJSON a) => s -> a -> Value
unary s a = object [ "symbol" .= show s
                   , "arity"  .= Data.Aeson.Types.Number 1
                   , "args"   .= toJSON a]

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1
