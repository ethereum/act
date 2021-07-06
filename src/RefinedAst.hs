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
{-# Language DataKinds #-}

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
  , _returns :: Maybe (ReturnExp Timed)
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
  = IntUpdate (TStorageItem Untimed Integer) (Exp Untimed Integer)
  | BoolUpdate (TStorageItem Untimed Bool) (Exp Untimed Bool)
  | BytesUpdate (TStorageItem Untimed ByteString) (Exp Untimed ByteString)
  deriving (Show, Eq)

data StorageLocation
  = IntLoc (TStorageItem Untimed Integer)
  | BoolLoc (TStorageItem Untimed Bool)
  | BytesLoc (TStorageItem Untimed ByteString)
  deriving (Show, Eq)

data TStorageItem t a where
  DirectInt    :: Id -> Id -> TStorageItem t Integer
  DirectBool   :: Id -> Id -> TStorageItem t Bool
  DirectBytes  :: Id -> Id -> TStorageItem t ByteString
  MappedInt    :: Id -> Id -> NonEmpty (ReturnExp t) -> TStorageItem t Integer
  MappedBool   :: Id -> Id -> NonEmpty (ReturnExp t) -> TStorageItem t Bool
  MappedBytes  :: Id -> Id -> NonEmpty (ReturnExp t) -> TStorageItem t ByteString

deriving instance Show (TStorageItem t a)
deriving instance Eq (TStorageItem t a)

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- In a `Timed` expression, all storage entries need to be `TEntry`, which contain either one of
-- `Pre, Post :: When`. In an `Untimed` expression, only `UTEntry` can occur, which does not contain
-- a `When`.

-- It is recommended that backends always input `Exp Timed a` to their codegens (or `Exp Untimed a`
-- if postconditions and return values are irrelevant), as this makes it easier to generate
-- consistent variable names. `Untimed` expressions can be given a specific timing using `as`,
-- e.g. `expr \`as\` Pre`.
data Exp (t :: Timing) (a :: *) where
  -- booleans
  And  :: Exp t Bool -> Exp t Bool -> Exp t Bool
  Or   :: Exp t Bool -> Exp t Bool -> Exp t Bool
  Impl :: Exp t Bool -> Exp t Bool -> Exp t Bool
  Neg :: Exp t Bool -> Exp t Bool
  LE :: Exp t Integer -> Exp t Integer -> Exp t Bool
  LEQ :: Exp t Integer -> Exp t Integer -> Exp t Bool
  GEQ :: Exp t Integer -> Exp t Integer -> Exp t Bool
  GE :: Exp t Integer -> Exp t Integer -> Exp t Bool
  LitBool :: Bool -> Exp t Bool
  BoolVar :: Id -> Exp t Bool
  -- integers
  Add :: Exp t Integer -> Exp t Integer -> Exp t Integer
  Sub :: Exp t Integer -> Exp t Integer -> Exp t Integer
  Mul :: Exp t Integer -> Exp t Integer -> Exp t Integer
  Div :: Exp t Integer -> Exp t Integer -> Exp t Integer
  Mod :: Exp t Integer -> Exp t Integer -> Exp t Integer
  Exp :: Exp t Integer -> Exp t Integer -> Exp t Integer
  LitInt :: Integer -> Exp t Integer
  IntVar :: Id -> Exp t Integer
  IntEnv :: EthEnv -> Exp t Integer
  -- bounds
  IntMin :: Int -> Exp t Integer
  IntMax :: Int -> Exp t Integer
  UIntMin :: Int -> Exp t Integer
  UIntMax :: Int -> Exp t Integer
  -- bytestrings
  Cat :: Exp t ByteString -> Exp t ByteString -> Exp t ByteString
  Slice :: Exp t ByteString -> Exp t Integer -> Exp t Integer -> Exp t ByteString
  ByVar :: Id -> Exp t ByteString
  ByStr :: String -> Exp t ByteString
  ByLit :: ByteString -> Exp t ByteString
  ByEnv :: EthEnv -> Exp t ByteString
  -- builtins
  NewAddr :: Exp t Integer -> Exp t Integer -> Exp t Integer

  -- polymorphic
  Eq  :: (Eq a, Typeable a) => Exp t a -> Exp t a -> Exp t Bool
  NEq :: (Eq a, Typeable a) => Exp t a -> Exp t a -> Exp t Bool
  ITE :: Exp t Bool -> Exp t a -> Exp t a -> Exp t a
  UTEntry :: TStorageItem t a -> Exp Untimed a
  TEntry :: TStorageItem t a -> When -> Exp Timed a

deriving instance Show (Exp t a)

-- | This will never be used as is. Its only purpose is to use with -XDataKinds, to ensure
-- type safety of the `Exp` type.
data Timing = Timed | Untimed

-- | This is used to tag all entries in `Timed` expressions.
data When = Pre | Post
  deriving Eq

instance Show When where
  show Pre  = "pre"
  show Post = "post"

instance Eq (Exp t a) where
  And a b == And c d = a == c && b == d
  Or a b == Or c d = a == c && b == d
  Impl a b == Impl c d = a == c && b == d
  Neg a == Neg b = a == b
  LE a b == LE c d = a == c && b == d
  LEQ a b == LEQ c d = a == c && b == d
  GEQ a b == GEQ c d = a == c && b == d
  GE a b == GE c d = a == c && b == d
  LitBool a == LitBool b = a == b
  BoolVar a == BoolVar b = a == b

  Add a b == Add c d = a == c && b == d
  Sub a b == Sub c d = a == c && b == d
  Mul a b == Mul c d = a == c && b == d
  Div a b == Div c d = a == c && b == d
  Mod a b == Mod c d = a == c && b == d
  Exp a b == Exp c d = a == c && b == d
  LitInt a == LitInt b = a == b
  IntVar a == IntVar b = a == b
  IntEnv a == IntEnv b = a == b

  IntMin a == IntMin b = a == b
  IntMax a == IntMax b = a == b
  UIntMin a == UIntMin b = a == b
  UIntMax a == UIntMax b = a == b

  Cat a b == Cat c d = a == c && b == d
  Slice a b c == Slice d e f = a == d && b == e && c == f
  ByVar a == ByVar b = a == b
  ByStr a == ByStr b = a == b
  ByLit a == ByLit b = a == b
  ByEnv a == ByEnv b = a == b

  NewAddr a b == NewAddr c d = a == c && b == d

  Eq (a :: Exp t x) (b :: Exp t x) == Eq (c :: Exp t y) (d :: Exp t y) =
    case eqT @x @y of
      Just Refl -> a == c && b == d
      Nothing -> False
  NEq (a :: Exp t x) (b :: Exp t x) == NEq (c :: Exp t y) (d :: Exp t y) =
    case eqT @x @y of
      Just Refl -> a == c && b == d
      Nothing -> False
  ITE a b c == ITE d e f = a == d && b == e && c == f
  UTEntry a == UTEntry b = a == b
  TEntry t a == TEntry t' b = a == b && t == t'

  _ == _ = False

instance Semigroup (Exp t Bool) where
  a <> b = And a b

instance Monoid (Exp t Bool) where
  mempty = LitBool True

-- | Give an `Untimed` expression a specific timing, i.e. `Pre` or `Post`.
-- Useful to generate consistent storage reference names.
as :: Exp Untimed a -> When -> Exp Timed a
e `as` time = go e
  where
    go :: Exp Untimed a -> Exp Timed a
    go expr = case expr of
      And  x y -> And (go x) (go y)
      Or   x y -> Or (go x) (go y)
      Impl x y -> Impl (go x) (go y)
      Neg x -> Neg (go x)
      LE x y -> LE (go x) (go y)
      LEQ x y -> LEQ (go x) (go y)
      GEQ x y -> GEQ (go x) (go y)
      GE x y -> GE (go x) (go y)
      LitBool x -> LitBool x
      BoolVar x -> BoolVar x
      -- integers
      Add x y -> Add (go x) (go y)
      Sub x y -> Sub (go x) (go y)
      Mul x y -> Mul (go x) (go y)
      Div x y -> Div (go x) (go y)
      Mod x y -> Mod (go x) (go y)
      Exp x y -> Exp (go x) (go y)
      LitInt x -> LitInt x
      IntVar x -> IntVar x
      IntEnv x -> IntEnv x
      -- younds
      IntMin x -> IntMin x
      IntMax x -> IntMax x
      UIntMin x -> UIntMin x
      UIntMax x -> UIntMax x
      -- yytestrings
      Cat x y -> Cat (go x) (go y)
      Slice x y z -> Slice (go x) (go y) (go z)
      ByVar x -> ByVar x
      ByStr x -> ByStr x
      ByLit x -> ByLit x
      ByEnv x -> ByEnv x
      -- yuiltins
      NewAddr x y -> NewAddr (go x) (go y)

      -- polymorphic
      Eq  x y -> Eq  (go x) (go y)
      NEq x y -> NEq (go x) (go y)
      ITE x y z -> ITE (go x) (go y) (go z)
      UTEntry x -> TEntry x time

data ReturnExp t
  = ExpInt    (Exp t Integer)
  | ExpBool   (Exp t Bool)
  | ExpBytes  (Exp t ByteString)
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
  TEntry _ _  -> empty
  UTEntry _   -> empty

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

instance ToJSON (TStorageItem t a) where
  toJSON (DirectInt a b) = object ["sort" .= pack "int"
                                  , "name" .= String (pack a <> "." <> pack b)]
  toJSON (DirectBool a b) = object ["sort" .= pack "bool"
                                   , "name" .= String (pack a <> "." <> pack b)]
  toJSON (DirectBytes a b) = object ["sort" .= pack "bytes"
                                    , "name" .= String (pack a <> "." <> pack b)]
  toJSON (MappedInt a b c) = mapping a b c
  toJSON (MappedBool a b c) = mapping a b c
  toJSON (MappedBytes a b c) = mapping a b c

instance ToJSON (ReturnExp t) where
   toJSON (ExpInt a) = object ["sort" .= pack "int"
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= String (pack "bool")
                               ,"expression" .= toJSON a]
   toJSON (ExpBytes a) = object ["sort" .= String (pack "bytestring")
                                ,"expression" .= toJSON a]

instance Typeable a => ToJSON (Exp t a) where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (Mul a b) = symbol "*" a b
  toJSON (Div a b) = symbol "/" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON $ show a
  toJSON (IntMin a) = toJSON $ show $ intmin a
  toJSON (IntMax a) = toJSON $ show $ intmax a
  toJSON (UIntMin a) = toJSON $ show $ uintmin a
  toJSON (UIntMax a) = toJSON $ show $ uintmax a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (UTEntry a) = toJSON a
  toJSON (TEntry a t) = unary (show t) a
  toJSON (ITE a b c) = object [  "symbol"   .= pack "ite"
                              ,  "arity"    .= Data.Aeson.Types.Number 3
                              ,  "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c])]
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
  toJSON (BoolVar a) = toJSON a
  toJSON (Neg a) = object [  "symbol"   .= pack "not"
                          ,  "arity"    .= Data.Aeson.Types.Number 1
                          ,  "args"     .= Array (fromList [toJSON a])]

  toJSON (Cat a b) = symbol "cat" a b
  toJSON (Slice s a b) = object [ "symbol" .= pack "slice"
                                , "arity"  .= Data.Aeson.Types.Number 3
                                , "args"   .= Array (fromList [toJSON s, toJSON a, toJSON b])
                                ]
  toJSON (ByVar a) = toJSON a
  toJSON (ByStr a) = toJSON a
  toJSON (ByLit a) = String . pack $ show a
  toJSON (ByEnv a) = String . pack $ show a
  toJSON v = error $ "todo: json ast for: " <> show v

mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
mapping c a b = object [  "symbol"   .= pack "lookup"
                       ,  "arity"    .= Data.Aeson.Types.Number 3
                       ,  "args"     .= Array (fromList [toJSON c, toJSON a, toJSON b])]

symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= Data.Aeson.Types.Number 2
                      ,  "args"     .= Array (fromList [toJSON a, toJSON b])]

unary :: ToJSON a => String -> a -> Value
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
