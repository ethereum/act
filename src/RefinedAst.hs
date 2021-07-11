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
{-# LANGUAGE InstanceSigs #-}

module RefinedAst where

import Control.Applicative (empty)

import Data.Char (toLower)
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
  , _returns :: Maybe (TypedExp Timed)
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

-- | References to items in storage, either as a map lookup or as a reading of
-- a simple variable. The third argument is a list of indices; it has entries iff
-- the item is referenced as a map lookup. The type is parametrized on a
-- timing `t` and a type `a`. `t` can be either `Timed` or `Untimed` and
-- indicates whether any indices that reference items in storage explicitly
-- refer to the pre-/post-state, or not. `a` is the type of the item that is
-- referenced.
data TStorageItem (t :: Timing) (a :: *) where
  IntItem    :: Id -> Id -> [TypedExp t] -> TStorageItem t Integer
  BoolItem   :: Id -> Id -> [TypedExp t] -> TStorageItem t Bool
  BytesItem  :: Id -> Id -> [TypedExp t] -> TStorageItem t ByteString
deriving instance Show (TStorageItem t a)
deriving instance Eq (TStorageItem t a)

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- All storage entries within an `Exp t a` contain a value of type `Time t`.
-- If `t ~ Timed`, the only possible such values are `Pre, Post :: Time Timed`, so each storage entry
-- will refer to either the prestate or the poststate.
-- In `t ~ Untimed`, the only possible such value is `Neither :: Time Untimed`, so all storage entries
-- will not explicitly refer any particular state.

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
  TEntry :: TStorageItem t a -> Time t -> Exp t a
deriving instance Show (Exp t a)

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
  TEntry a t == TEntry b u = a == b && t == u
  _ == _ = False

instance Semigroup (Exp t Bool) where
  a <> b = And a b

instance Monoid (Exp t Bool) where
  mempty = LitBool True

-- | Expressions for which the return type is known.
data TypedExp t
  = ExpInt   (Exp t Integer)
  | ExpBool  (Exp t Bool)
  | ExpBytes (Exp t ByteString)
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

  Add a b     -> [a' + b'     | a' <- eval a, b' <- eval b]
  Sub a b     -> [a' - b'     | a' <- eval a, b' <- eval b]
  Mul a b     -> [a' * b'     | a' <- eval a, b' <- eval b]
  Div a b     -> [a' `div` b' | a' <- eval a, b' <- eval b]
  Mod a b     -> [a' `mod` b' | a' <- eval a, b' <- eval b]
  Exp a b     -> [a' ^ b'     | a' <- eval a, b' <- eval b]
  LitInt a    -> pure a
  IntMin  a   -> pure . negate $ 2 ^ (a - 1)
  IntMax  a   -> pure $ 2 ^ (a - 1) - 1
  UIntMin _   -> pure 0
  UIntMax a   -> pure $ 2 ^ a - 1

  Cat s t     -> [s' <> t' | s' <- eval s, t' <- eval t]
  Slice s a b -> [BS.pack . genericDrop a' . genericTake b' $ s'
                           | s' <- BS.unpack <$> eval s
                           , a' <- eval a
                           , b' <- eval b]
  ByStr s     -> pure . fromString $ s
  ByLit s     -> pure s

  Eq a b      -> [a' == b' | a' <- eval a, b' <- eval b]
  NEq a b     -> [a' /= b' | a' <- eval a, b' <- eval b]
  ITE a b c   -> eval a >>= \cond -> if cond then eval b else eval c
  _           -> empty

--------------------------
-- * Timing machinery * --
--------------------------

-- | This will never be used as-is. Its only purpose is to use with -XDataKinds,
-- to ensure type safety of the `Exp` and `TStorageItem` types.
data Timing = Timed | Untimed

-- | Encodes choice between explicitly referring to the pre-/post-state, or not.
data Time t where
  Pre     :: Time Timed
  Post    :: Time Timed
  Neither :: Time Untimed
deriving instance Eq (Time t)
deriving instance Show (Time t)

-- | In cases when the only choice is between the pre-/post-state, this alias can be used.
type When = Time Timed

-- | True iff the input is `Pre` or `Post`.
isTimed :: Time t -> Bool
isTimed Neither = False
isTimed _       = True

-- | If the supplied time is `Pre`, this returns `pre(input)` (and analogously for `Post`).
-- Otherwise returns the untouched `String`.
timeParens :: Time t -> String -> String
timeParens t s | isTimed t = toLower <$> show t <> "(" <> s <> ")"
               | otherwise = s

-- | Types that are parametrized on a `Timing` and a normal type.
-- The most notable example is `Exp :: Timing -> * -> *`.
class Timeable c where
  -- | Takes an `Untimed` `Timeable` thing and points it towards the supplied time.
  setTime :: When -> c Untimed a -> c Timed a
  setTime = forceTime

  -- | Takes an `Untimed` `Timeable` thing and points it towards the prestate.
  setPre :: c Untimed a -> c Timed a
  setPre = forceTime Pre

  -- | Takes an `Untimed` `Timeable` thing and points it towards the poststate.
  setPost :: c Untimed a -> c Timed a
  setPost = forceTime Post

  -- | This is `setTime` with the arguments flipped.
  -- Allows writing e.g. "c `as` Pre".
  as :: c Untimed a -> When -> c Timed a
  as = flip forceTime

  -- | Dangerous! Do not use this during code generation, as doing so
  -- may damage your AST by replacing valid `Post` entries with `Pre`
  -- or vice versa. Instead, use `as`, which provides "the same"
  -- functionality but restricted to be type safe.
  -- If we had an explicit export list, this wouldn't be exported.
  forceTime :: Time t -> c t0 a -> c t a

instance Timeable Exp where
  forceTime time expr = case expr of
    And  x y -> And (forceTime time x) (forceTime time y)
    Or   x y -> Or (forceTime time x) (forceTime time y)
    Impl x y -> Impl (forceTime time x) (forceTime time y)
    Neg x -> Neg (forceTime time x)
    LE x y -> LE (forceTime time x) (forceTime time y)
    LEQ x y -> LEQ (forceTime time x) (forceTime time y)
    GEQ x y -> GEQ (forceTime time x) (forceTime time y)
    GE x y -> GE (forceTime time x) (forceTime time y)
    LitBool x -> LitBool x
    BoolVar x -> BoolVar x
    -- integers
    Add x y -> Add (forceTime time x) (forceTime time y)
    Sub x y -> Sub (forceTime time x) (forceTime time y)
    Mul x y -> Mul (forceTime time x) (forceTime time y)
    Div x y -> Div (forceTime time x) (forceTime time y)
    Mod x y -> Mod (forceTime time x) (forceTime time y)
    Exp x y -> Exp (forceTime time x) (forceTime time y)
    LitInt x -> LitInt x
    IntVar x -> IntVar x
    IntEnv x -> IntEnv x
    -- younds
    IntMin x -> IntMin x
    IntMax x -> IntMax x
    UIntMin x -> UIntMin x
    UIntMax x -> UIntMax x
    -- yytestrings
    Cat x y -> Cat (forceTime time x) (forceTime time y)
    Slice x y z -> Slice (forceTime time x) (forceTime time y) (forceTime time z)
    ByVar x -> ByVar x
    ByStr x -> ByStr x
    ByLit x -> ByLit x
    ByEnv x -> ByEnv x
    -- yuiltins
    NewAddr x y -> NewAddr (forceTime time x) (forceTime time y)

    -- polymorphic
    Eq  x y -> Eq  (forceTime time x) (forceTime time y)
    NEq x y -> NEq (forceTime time x) (forceTime time y)
    ITE x y z -> ITE (forceTime time x) (forceTime time y) (forceTime time z)
    TEntry item _ -> TEntry (forceTime time item) time

instance Timeable TStorageItem where
  forceTime :: forall t t0 a. Time t -> TStorageItem t0 a -> TStorageItem t a
  forceTime time item = case item of
    IntItem   c x ixs -> IntItem   c x $ forceTyped <$> ixs
    BoolItem  c x ixs -> BoolItem  c x $ forceTyped <$> ixs
    BytesItem c x ixs -> BytesItem c x $ forceTyped <$> ixs
    where
      forceTyped :: TypedExp t0 -> TypedExp t
      forceTyped e = case e of
        ExpInt   e' -> ExpInt   $ forceTime time e'
        ExpBool  e' -> ExpBool  $ forceTime time e'
        ExpBytes e' -> ExpBytes $ forceTime time e'

-- | Give a specific timing to a `TypedExp Untimed`, analogously to `setTime`.
-- (Unfortunately `TypedExp` cannot be given a `Timeable` instance so we need
-- to keep this as a standalone function. Ideas for how to make this cleaner
-- would be nice.)
setTyped :: When -> TypedExp Untimed -> TypedExp Timed
setTyped time e = case e of
  ExpInt   e' -> ExpInt   $ e' `as` time
  ExpBool  e' -> ExpBool  $ e' `as` time
  ExpBytes e' -> ExpBytes $ e' `as` time

------------------------
-- * JSON machinery * --
------------------------

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
  toJSON (IntItem a b []) = object ["sort" .= pack "int"
                                  , "name" .= String (pack a <> "." <> pack b)]
  toJSON (BoolItem a b []) = object ["sort" .= pack "bool"
                                   , "name" .= String (pack a <> "." <> pack b)]
  toJSON (BytesItem a b []) = object ["sort" .= pack "bytes"
                                    , "name" .= String (pack a <> "." <> pack b)]
  toJSON (IntItem a b c) = mapping a b c
  toJSON (BoolItem a b c) = mapping a b c
  toJSON (BytesItem a b c) = mapping a b c

instance ToJSON (TypedExp t) where
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
  toJSON (TEntry a Neither) = toJSON a
  toJSON (TEntry a t) = object [ "symbol" .= show t
                               , "arity"  .= Data.Aeson.Types.Number 1
                               , "args"   .= toJSON a]
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

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1
