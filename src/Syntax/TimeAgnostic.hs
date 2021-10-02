{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators, MultiParamTypeClasses, PatternSynonyms, ViewPatterns #-}

{-|
Module      : Syntax.TimeAgnostic
Description : AST data types where implicit timings may or may not have been made explicit.

This module only exists to increase code reuse; the types defined here won't
be used directly, but will be instantiated with different timing parameters
at different steps in the AST refinement process. This way we don't have to
update mirrored types, instances and functions in lockstep.

Some terms in here are always 'Timed'. This indicates that their timing must
*always* be explicit. For the rest, all timings must be implicit in source files
(i.e. 'Untimed'), but will be made explicit (i.e. 'Timed') during refinement.
-}

module Syntax.TimeAgnostic (module Syntax.TimeAgnostic) where

import Control.Applicative (empty)

import Data.Aeson
import Data.Aeson.Types
import qualified Data.ByteString as BS
import Data.List (genericTake,genericDrop)
import Data.Map.Strict (Map)
import Data.Singletons
import Data.String (fromString)
import Data.Text (pack)
import Data.Typeable
import Data.Vector (fromList)

import EVM.Solidity (SlotType(..))

-- Reexports
import Syntax.Types   as Syntax.TimeAgnostic
import Syntax.Timing  as Syntax.TimeAgnostic
import Syntax.Untyped as Syntax.TimeAgnostic (Id, Interface(..), EthEnv(..), Decl(..))

-- AST post typechecking
data Claim t
  = C (Constructor t)
  | B (Behaviour t)
  | I (Invariant t)
  | S Store
deriving instance Show (InvariantPred t) => Show (Claim t)
deriving instance Eq   (InvariantPred t) => Eq   (Claim t)

data Transition t
  = Ctor (Constructor t)
  | Behv (Behaviour t)
  deriving (Show, Eq)

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
data Invariant t = Invariant
  { _icontract :: Id
  , _ipreconditions :: [Exp Bool t]
  , _istoragebounds :: [Exp Bool t]
  , _predicate :: InvariantPred t
  }
deriving instance Show (InvariantPred t) => Show (Invariant t)
deriving instance Eq   (InvariantPred t) => Eq   (Invariant t)

-- | Invariant predicates are either a single predicate without explicit timing or
-- two predicates which explicitly reference the pre- and the post-state, respectively.
-- Furthermore, if we know the predicate type we can always deduce the timing, not
-- only vice versa.
type family InvariantPred (t :: Timing) = (pred :: *) | pred -> t where
  InvariantPred Untimed = Exp Bool Untimed
  InvariantPred Timed   = (Exp Bool Timed, Exp Bool Timed)

data Constructor t = Constructor
  { _cname :: Id
  , _cmode :: Mode
  , _cinterface :: Interface
  , _cpreconditions :: [Exp Bool t]
  , _cpostconditions :: [Exp Bool Timed]
  , _initialStorage :: [StorageUpdate t]
  , _cstateUpdates :: [Rewrite t]
  } deriving (Show, Eq)

data Behaviour t = Behaviour
  { _name :: Id
  , _mode :: Mode
  , _contract :: Id
  , _interface :: Interface
  , _preconditions :: [Exp Bool t]
  , _postconditions :: [Exp Bool Timed]
  , _stateUpdates :: [Rewrite t]
  , _returns :: Maybe (TypedExp Timed)
  } deriving (Show, Eq)

data Mode
  = Pass
  | Fail
  | OOG
  deriving (Eq, Show)

data Rewrite t
  = Constant (StorageLocation t)
  | Rewrite (StorageUpdate t)
  deriving (Show, Eq)

data StorageUpdate t
  = forall a. Typeable a => Update (Sing a) (TStorageItem a t) (Exp a t)
deriving instance Show (StorageUpdate t)

_Update :: Typeable a => TStorageItem a t -> Exp a t -> StorageUpdate t
_Update item expr = Update (getType item) item expr

instance Eq (StorageUpdate t) where
  Update Sing i1 e1 == Update Sing i2 e2 = eqS i1 i2 && eqS e1 e2

data StorageLocation t
  = forall a. Loc (Sing a) (TStorageItem a t)
deriving instance Show (StorageLocation t)

_Loc :: TStorageItem a t -> StorageLocation t
_Loc item = Loc (getType item) item

instance Eq (StorageLocation t) where
  Loc Sing i1 == Loc Sing i2 = eqS i1 i2
--deriving instance Eq (StorageLocation t)
--    IntLoc (TStorageItem Integer t)
--  | BoolLoc (TStorageItem Bool t)
--  | BytesLoc (TStorageItem ByteString t)
--  deriving (Show, Eq)

-- | References to items in storage, either as a map lookup or as a reading of
-- a simple variable. The third argument is a list of indices; it has entries iff
-- the item is referenced as a map lookup. The type is parametrized on a
-- timing `t` and a type `a`. `t` can be either `Timed` or `Untimed` and
-- indicates whether any indices that reference items in storage explicitly
-- refer to the pre-/post-state, or not. `a` is the type of the item that is
-- referenced.
data TStorageItem (a :: *) (t :: Timing) where
  Item :: Sing a -> Id -> Id -> [TypedExp t] -> TStorageItem a t
deriving instance Show (TStorageItem a t)
deriving instance Eq (TStorageItem a t)

_Item :: SingI a => Id -> Id -> [TypedExp t] -> TStorageItem a t
_Item = Item sing

instance HasType (TStorageItem a t) a where
  getType (Item t _ _ _) = t

-- | Expressions for which the return type is known.
data TypedExp t
  = forall a. Typeable a => TExp (Sing a) (Exp a t)
deriving instance Show (TypedExp t)
--deriving instance Eq (TypedExp t)

-- We could remove the 'SingI' constraint here if we also removed it from the
-- 'HasType' instance for 'Exp'. But it's tedious and noisy and atm unnecessary.
_TExp :: (Typeable a, SingI a) => Exp a t -> TypedExp t
_TExp expr = undefined -- TExp (getType expr) expr

instance Eq (TypedExp t) where
  TExp Sing e1 == TExp Sing e2 = eqS e1 e2
--    TExp SInteger   (Exp Integer t)
--  | TExp SBoolean  (Exp Bool t)
--  | TExp SByteStr (Exp ByteString t)
--  deriving (Eq, Show)

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- All storage entries within an `Exp a t` contain a value of type `Time t`.
-- If `t ~ Timed`, the only possible such values are `Pre, Post :: Time Timed`, so each storage entry
-- will refer to either the prestate or the poststate.
-- In `t ~ Untimed`, the only possible such value is `Neither :: Time Untimed`, so all storage entries
-- will not explicitly refer any particular state.
data Exp (a :: *) (t :: Timing) where
  -- booleans
  And  :: Exp Bool t -> Exp Bool t -> Exp Bool t
  Or   :: Exp Bool t -> Exp Bool t -> Exp Bool t
  Impl :: Exp Bool t -> Exp Bool t -> Exp Bool t
  Neg :: Exp Bool t -> Exp Bool t
  LE :: Exp Integer t -> Exp Integer t -> Exp Bool t
  LEQ :: Exp Integer t -> Exp Integer t -> Exp Bool t
  GEQ :: Exp Integer t -> Exp Integer t -> Exp Bool t
  GE :: Exp Integer t -> Exp Integer t -> Exp Bool t
  LitBool :: Bool -> Exp Bool t
  -- integers
  Add :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Sub :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Mul :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Div :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Mod :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Exp :: Exp Integer t -> Exp Integer t -> Exp Integer t
  LitInt :: Integer -> Exp Integer t
  --IntVar :: Id -> Exp Integer t
  IntEnv :: EthEnv -> Exp Integer t
  -- bounds
  IntMin :: Int -> Exp Integer t
  IntMax :: Int -> Exp Integer t
  UIntMin :: Int -> Exp Integer t
  UIntMax :: Int -> Exp Integer t
  -- bytestrings
  Cat :: Exp ByteString t -> Exp ByteString t -> Exp ByteString t
  Slice :: Exp ByteString t -> Exp Integer t -> Exp Integer t -> Exp ByteString t
  --ByVar :: Id -> Exp ByteString t
  ByStr :: String -> Exp ByteString t
  ByLit :: ByteString -> Exp ByteString t
  ByEnv :: EthEnv -> Exp ByteString t
  -- builtins
  NewAddr :: Exp Integer t -> Exp Integer t -> Exp Integer t

  -- polymorphic
  Eq  :: (Eq a, Typeable a) => Exp a t -> Exp a t -> Exp Bool t
  NEq :: (Eq a, Typeable a) => Exp a t -> Exp a t -> Exp Bool t
  ITE :: Exp Bool t -> Exp a t -> Exp a t -> Exp a t
  Var :: Sing a -> Id -> Exp a t
  TEntry :: Time t -> TStorageItem a t -> Exp a t
deriving instance Show (Exp a t)

instance Eq (Exp a t) where
  And a b == And c d = a == c && b == d
  Or a b == Or c d = a == c && b == d
  Impl a b == Impl c d = a == c && b == d
  Neg a == Neg b = a == b
  LE a b == LE c d = a == c && b == d
  LEQ a b == LEQ c d = a == c && b == d
  GEQ a b == GEQ c d = a == c && b == d
  GE a b == GE c d = a == c && b == d
  LitBool a == LitBool b = a == b
  --BoolVar a == BoolVar b = a == b

  Add a b == Add c d = a == c && b == d
  Sub a b == Sub c d = a == c && b == d
  Mul a b == Mul c d = a == c && b == d
  Div a b == Div c d = a == c && b == d
  Mod a b == Mod c d = a == c && b == d
  Exp a b == Exp c d = a == c && b == d
  LitInt a == LitInt b = a == b
  --IntVar a == IntVar b = a == b
  IntEnv a == IntEnv b = a == b

  IntMin a == IntMin b = a == b
  IntMax a == IntMax b = a == b
  UIntMin a == UIntMin b = a == b
  UIntMax a == UIntMax b = a == b

  Cat a b == Cat c d = a == c && b == d
  Slice a b c == Slice d e f = a == d && b == e && c == f
  --ByVar a == ByVar b = a == b
  ByStr a == ByStr b = a == b
  ByLit a == ByLit b = a == b
  ByEnv a == ByEnv b = a == b

  NewAddr a b == NewAddr c d = a == c && b == d

  Eq (a :: Exp x t) (b :: Exp x t) == Eq (c :: Exp y t) (d :: Exp y t) =
    case eqT @x @y of
      Just Refl -> a == c && b == d
      Nothing -> False
  NEq (a :: Exp x t) (b :: Exp x t) == NEq (c :: Exp y t) (d :: Exp y t) =
    case eqT @x @y of
      Just Refl -> a == c && b == d
      Nothing -> False
  ITE a b c == ITE d e f = a == d && b == e && c == f
  TEntry a t == TEntry b u = a == b && t == u
  Var _ a == Var _ b = a == b
  _ == _ = False

-- We could make this explicit which would remove the need for the SingI instance.
instance SingI a => HasType (Exp a t) a where
  getType _ = sing

instance Semigroup (Exp Bool t) where
  a <> b = And a b

instance Monoid (Exp Bool t) where
  mempty = LitBool True

instance Timable StorageLocation where
  setTime time (Loc typ item) = Loc typ $ setTime time item

instance Timable TypedExp where
  setTime time (TExp typ expr) = TExp typ $ setTime time expr

instance Timable (Exp a) where
  setTime time expr = case expr of
    -- booleans
    And  x y -> And (go x) (go y)
    Or   x y -> Or (go x) (go y)
    Impl x y -> Impl (go x) (go y)
    Neg x -> Neg (go x)
    LE x y -> LE (go x) (go y)
    LEQ x y -> LEQ (go x) (go y)
    GEQ x y -> GEQ (go x) (go y)
    GE x y -> GE (go x) (go y)
    LitBool x -> LitBool x
    -- integers
    Add x y -> Add (go x) (go y)
    Sub x y -> Sub (go x) (go y)
    Mul x y -> Mul (go x) (go y)
    Div x y -> Div (go x) (go y)
    Mod x y -> Mod (go x) (go y)
    Exp x y -> Exp (go x) (go y)
    LitInt x -> LitInt x
    IntEnv x -> IntEnv x
    -- bounds
    IntMin x -> IntMin x
    IntMax x -> IntMax x
    UIntMin x -> UIntMin x
    UIntMax x -> UIntMax x
    -- bytestrings
    Cat x y -> Cat (go x) (go y)
    Slice x y z -> Slice (go x) (go y) (go z)
    ByStr x -> ByStr x
    ByLit x -> ByLit x
    ByEnv x -> ByEnv x
    -- builtins
    NewAddr x y -> NewAddr (go x) (go y) 
    -- polymorphic
    Eq  x y -> Eq  (go x) (go y)
    NEq x y -> NEq (go x) (go y)
    ITE x y z -> ITE (go x) (go y) (go z)
    TEntry _ item -> TEntry time (go item)
    Var t x -> Var t x
    where
      go :: Timable c => c Untimed -> c Timed
      go = setTime time

instance Timable (TStorageItem a) where
  setTime time (Item typ c x ixs) = Item typ c x $ setTime time <$> ixs

------------------------
-- * JSON instances * --
------------------------

-- TODO dual instances are ugly! But at least it works for now.
-- It was difficult to construct a function with type:
-- `InvPredicate t -> Either (Exp Bool Timed,Exp Bool Timed) (Exp Bool Untimed)`
instance ToJSON (Claim Timed) where
  toJSON (S storages)          = storeJSON storages
  toJSON (I inv@Invariant{..}) = invariantJSON inv _predicate
  toJSON (C ctor)              = toJSON ctor
  toJSON (B behv)              = toJSON behv

instance ToJSON (Claim Untimed) where
  toJSON (S storages)          = storeJSON storages
  toJSON (I inv@Invariant{..}) = invariantJSON inv _predicate
  toJSON (C ctor)              = toJSON ctor
  toJSON (B behv)              = toJSON behv 

storeJSON :: Store -> Value
storeJSON storages = object [ "kind" .= String "Storages"
                            , "storages" .= toJSON storages]

invariantJSON :: ToJSON pred => Invariant t -> pred -> Value
invariantJSON Invariant{..} predicate = object [ "kind" .= String "Invariant"
                                               , "predicate" .= toJSON predicate
                                               , "preconditions" .= toJSON _ipreconditions
                                               , "storagebounds" .= toJSON _istoragebounds
                                               , "contract" .= _icontract]

instance ToJSON (Constructor t) where
  toJSON Constructor{..} = object [ "kind" .= String "Constructor"
                                  , "contract" .= _cname
                                  , "mode" .= (String . pack $ show _cmode)
                                  , "interface" .= (String . pack $ show _cinterface)
                                  , "preConditions" .= toJSON _cpreconditions
                                  , "postConditions" .= toJSON _cpostconditions
                                  , "storage" .= toJSON _initialStorage
                                  ]

instance ToJSON (Behaviour t) where
  toJSON Behaviour{..} = object [ "kind" .= String "Behaviour"
                                , "name" .= _name
                                , "contract" .= _contract
                                , "mode" .= (String . pack $ show _mode)
                                , "interface" .= (String . pack $ show _interface)
                                , "preConditions" .= toJSON _preconditions
                                , "postConditions" .= toJSON _postconditions
                                , "stateUpdates" .= toJSON _stateUpdates
                                , "returns" .= toJSON _returns]

instance ToJSON (Rewrite t) where
  toJSON (Constant a) = object [ "Constant" .= toJSON a ]
  toJSON (Rewrite a) = object [ "Rewrite" .= toJSON a ]

instance ToJSON (StorageLocation t) where
  toJSON (Loc _ a) = object ["location" .= toJSON a]

instance ToJSON (StorageUpdate t) where
  toJSON (Update _ a b) = object ["location" .= toJSON a ,"value" .= toJSON b]

instance ToJSON (TStorageItem a t) where
  toJSON (Item SInteger a b []) = object ["sort" .= pack "int"
                                  , "name" .= String (pack a <> "." <> pack b)]
  toJSON (Item SBoolean a b []) = object ["sort" .= pack "bool"
                                   , "name" .= String (pack a <> "." <> pack b)]
  toJSON (Item SByteStr a b []) = object ["sort" .= pack "bytes"
                                    , "name" .= String (pack a <> "." <> pack b)]
  toJSON (Item SInteger a b c) = mapping a b c
  toJSON (Item SBoolean a b c) = mapping a b c
  toJSON (Item SByteStr a b c) = mapping a b c

mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
mapping c a b = object [  "symbol"   .= pack "lookup"
                       ,  "arity"    .= Data.Aeson.Types.Number 3
                       ,  "args"     .= Array (fromList [toJSON c, toJSON a, toJSON b])]

instance ToJSON (TypedExp t) where
  toJSON (TExp typ a) = object ["sort"       .= pack (show typ)
                               ,"expression" .= toJSON a]

instance Typeable a => ToJSON (Exp a t) where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (Mul a b) = symbol "*" a b
  toJSON (Div a b) = symbol "/" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  --toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON $ show a
  toJSON (IntMin a) = toJSON $ show $ intmin a
  toJSON (IntMax a) = toJSON $ show $ intmax a
  toJSON (UIntMin a) = toJSON $ show $ uintmin a
  toJSON (UIntMax a) = toJSON $ show $ uintmax a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (TEntry t a) = object [ pack (show t) .= toJSON a ]
  toJSON (Var _ a) = toJSON a
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
  --toJSON (BoolVar a) = toJSON a
  toJSON (Neg a) = object [  "symbol"   .= pack "not"
                          ,  "arity"    .= Data.Aeson.Types.Number 1
                          ,  "args"     .= Array (fromList [toJSON a])]

  toJSON (Cat a b) = symbol "cat" a b
  toJSON (Slice s a b) = object [ "symbol" .= pack "slice"
                                , "arity"  .= Data.Aeson.Types.Number 3
                                , "args"   .= Array (fromList [toJSON s, toJSON a, toJSON b])
                                ]
  --toJSON (ByVar a) = toJSON a
  toJSON (ByStr a) = toJSON a
  toJSON (ByLit a) = String . pack $ show a
  toJSON (ByEnv a) = String . pack $ show a
  toJSON v = error $ "todo: json ast for: " <> show v

symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= Data.Aeson.Types.Number 2
                      ,  "args"     .= Array (fromList [toJSON a, toJSON b])]

-- | Simplifies concrete expressions into literals.
-- Returns `Nothing` if the expression contains symbols.
eval :: Exp a t -> Maybe a
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
  IntMin  a   -> pure $ intmin  a
  IntMax  a   -> pure $ intmax  a
  UIntMin a   -> pure $ uintmin a
  UIntMax a   -> pure $ uintmax a

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

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1

_Var :: SingI a => Id -> Exp a t
_Var name = Var sing name

castTime :: (Typeable t, Typeable u) => Exp a u -> Maybe (Exp a t)
castTime = gcast

castType :: (Typeable a, Typeable x) => Exp x t -> Maybe (Exp a t)
castType = gcast0

-- | Analogous to `gcast1` and `gcast2` from `Data.Typeable`. We *could* technically use `cast` instead
-- but then we would catch too many errors at once, so we couldn't emit informative error messages.
gcast0 :: forall t t' a. (Typeable t, Typeable t') => t a -> Maybe (t' a)
gcast0 x = fmap (\Refl -> x) (eqT :: Maybe (t :~: t'))
