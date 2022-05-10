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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
import qualified Data.Aeson.Key as Key
import qualified Data.ByteString as BS
import Data.List (genericTake,genericDrop)
import Data.Map.Strict (Map)
import Data.Singletons (SingI(..))
import Data.String (fromString)
import Data.Text (pack)
import Data.Typeable
import Data.Vector (fromList)
import Data.Kind

import EVM.Solidity (SlotType(..))

-- Reexports
import Parse          as Syntax.TimeAgnostic (nowhere)
import Syntax.Types   as Syntax.TimeAgnostic
import Syntax.Timing  as Syntax.TimeAgnostic
import Syntax.Untyped as Syntax.TimeAgnostic (Id, Pn, Interface(..), EthEnv(..), Decl(..))

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
type family InvariantPred (t :: Timing) = (pred :: Type) | pred -> t where
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

data StorageUpdate (t :: Timing) where
  Update :: SType a -> TStorageItem a t -> Exp a t -> StorageUpdate t
deriving instance Show (StorageUpdate t)

_Update :: TStorageItem a t -> Exp a t -> StorageUpdate t
_Update item expr = Update (getType item) item expr

instance Eq (StorageUpdate t) where
  Update SType i1 e1 == Update SType i2 e2 = eqS i1 i2 && eqS e1 e2

data StorageLocation (t :: Timing) where
  Loc :: SType a -> TStorageItem a t -> StorageLocation t
deriving instance Show (StorageLocation t)

_Loc :: TStorageItem a t -> StorageLocation t
_Loc item = Loc (getType item) item

instance Eq (StorageLocation t) where
  Loc SType i1 == Loc SType i2 = eqS i1 i2

-- | References to items in storage, either as a map lookup or as a reading of
-- a simple variable. The third argument is a list of indices; it has entries iff
-- the item is referenced as a map lookup. The type is parametrized on a
-- timing `t` and a type `a`. `t` can be either `Timed` or `Untimed` and
-- indicates whether any indices that reference items in storage explicitly
-- refer to the pre-/post-state, or not. `a` is the type of the item that is
-- referenced.
data TStorageItem (a :: Type) (t :: Timing) where
  Item :: SType a -> Id -> Id -> [TypedExp t] -> TStorageItem a t
deriving instance Show (TStorageItem a t)
deriving instance Eq (TStorageItem a t)

_Item :: SingI a => Id -> Id -> [TypedExp t] -> TStorageItem a t
_Item = Item sing

instance HasType (TStorageItem a t) a where
  getType (Item t _ _ _) = t

-- | Expressions for which the return type is known.
data TypedExp t
  = forall a. TExp (SType a) (Exp a t)
deriving instance Show (TypedExp t)

-- We could remove the 'SingI' constraint here if we also removed it from the
-- 'HasType' instance for 'Exp'. But it's tedious and noisy and atm unnecessary.
_TExp :: SingI a => Exp a t -> TypedExp t
_TExp expr = TExp (getType expr) expr

instance Eq (TypedExp t) where
  TExp SType e1 == TExp SType e2 = eqS e1 e2

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- All storage entries within an `Exp a t` contain a value of type `Time t`.
-- If `t ~ Timed`, the only possible such values are `Pre, Post :: Time Timed`, so each storage entry
-- will refer to either the prestate or the poststate.
-- In `t ~ Untimed`, the only possible such value is `Neither :: Time Untimed`, so all storage entries
-- will not explicitly refer any particular state.
data Exp (a :: Type) (t :: Timing) where
  -- booleans
  And  :: Pn -> Exp Bool t -> Exp Bool t -> Exp Bool t
  Or   :: Pn -> Exp Bool t -> Exp Bool t -> Exp Bool t
  Impl :: Pn -> Exp Bool t -> Exp Bool t -> Exp Bool t
  Neg :: Pn -> Exp Bool t -> Exp Bool t
  LE :: Pn -> Exp Integer t -> Exp Integer t -> Exp Bool t
  LEQ :: Pn -> Exp Integer t -> Exp Integer t -> Exp Bool t
  GEQ :: Pn -> Exp Integer t -> Exp Integer t -> Exp Bool t
  GE :: Pn -> Exp Integer t -> Exp Integer t -> Exp Bool t
  LitBool :: Pn -> Bool -> Exp Bool t
  -- integers
  Add :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t
  Sub :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t
  Mul :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t
  Div :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t
  Mod :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t
  Exp :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t
  LitInt :: Pn -> Integer -> Exp Integer t
  IntEnv :: Pn -> EthEnv -> Exp Integer t
  -- bounds
  IntMin :: Pn -> Int -> Exp Integer t
  IntMax :: Pn -> Int -> Exp Integer t
  UIntMin :: Pn -> Int -> Exp Integer t
  UIntMax :: Pn -> Int -> Exp Integer t
  -- bytestrings
  Cat :: Pn -> Exp ByteString t -> Exp ByteString t -> Exp ByteString t
  Slice :: Pn -> Exp ByteString t -> Exp Integer t -> Exp Integer t -> Exp ByteString t
  ByStr :: Pn -> String -> Exp ByteString t
  ByLit :: Pn -> ByteString -> Exp ByteString t
  ByEnv :: Pn -> EthEnv -> Exp ByteString t
  -- builtins
  NewAddr :: Pn -> Exp Integer t -> Exp Integer t -> Exp Integer t

  -- polymorphic
  Eq  :: (Eq a, Typeable a) => Pn -> Exp a t -> Exp a t -> Exp Bool t
  NEq :: (Eq a, Typeable a) => Pn -> Exp a t -> Exp a t -> Exp Bool t
  ITE :: Pn -> Exp Bool t -> Exp a t -> Exp a t -> Exp a t
  Var :: Pn -> SType a -> Id -> Exp a t
  TEntry :: Pn -> Time t -> TStorageItem a t -> Exp a t
deriving instance Show (Exp a t)

-- Equality modulo source file position.
instance Eq (Exp a t) where
  And _ a b == And _ c d = a == c && b == d
  Or _ a b == Or _ c d = a == c && b == d
  Impl _ a b == Impl _ c d = a == c && b == d
  Neg _ a == Neg _ b = a == b
  LE _ a b == LE _ c d = a == c && b == d
  LEQ _ a b == LEQ _ c d = a == c && b == d
  GEQ _ a b == GEQ _ c d = a == c && b == d
  GE _ a b == GE _ c d = a == c && b == d
  LitBool _ a == LitBool _ b = a == b

  Add _ a b == Add _ c d = a == c && b == d
  Sub _ a b == Sub _ c d = a == c && b == d
  Mul _ a b == Mul _ c d = a == c && b == d
  Div _ a b == Div _ c d = a == c && b == d
  Mod _ a b == Mod _ c d = a == c && b == d
  Exp _ a b == Exp _ c d = a == c && b == d
  LitInt _ a == LitInt _ b = a == b
  IntEnv _ a == IntEnv _ b = a == b

  IntMin _ a == IntMin _ b = a == b
  IntMax _ a == IntMax _ b = a == b
  UIntMin _ a == UIntMin _ b = a == b
  UIntMax _ a == UIntMax _ b = a == b

  Cat _ a b == Cat _ c d = a == c && b == d
  Slice _ a b c == Slice _ d e f = a == d && b == e && c == f
  ByStr _ a == ByStr _ b = a == b
  ByLit _ a == ByLit _ b = a == b
  ByEnv _ a == ByEnv _ b = a == b

  NewAddr _ a b == NewAddr _ c d = a == c && b == d

  Eq _ (a :: Exp x t) (b :: Exp x t) == Eq _ (c :: Exp y t) (d :: Exp y t) =
    case eqT @x @y of
      Just Refl -> a == c && b == d
      Nothing -> False
  NEq _ (a :: Exp x t) (b :: Exp x t) == NEq _ (c :: Exp y t) (d :: Exp y t) =
    case eqT @x @y of
      Just Refl -> a == c && b == d
      Nothing -> False
  ITE _ a b c == ITE _ d e f = a == d && b == e && c == f
  TEntry _ a t == TEntry _ b u = a == b && t == u
  Var _ _ a == Var _ _ b = a == b
  _ == _ = False

-- We could make this explicit which would remove the need for the SingI instance.
instance SingI a => HasType (Exp a t) a where
  getType _ = sing

instance Semigroup (Exp Bool t) where
  a <> b = And nowhere a b

instance Monoid (Exp Bool t) where
  mempty = LitBool nowhere True

instance Timable StorageLocation where
  setTime time (Loc typ item) = Loc typ $ setTime time item

instance Timable TypedExp where
  setTime time (TExp typ expr) = TExp typ $ setTime time expr

instance Timable (Exp a) where
  setTime time expr = case expr of
    -- booleans
    And p x y -> And p (go x) (go y)
    Or   p x y -> Or p (go x) (go y)
    Impl p x y -> Impl p (go x) (go y)
    Neg p x -> Neg p(go x)
    LE p x y -> LE p (go x) (go y)
    LEQ p x y -> LEQ p (go x) (go y)
    GEQ p x y -> GEQ p (go x) (go y)
    GE p x y -> GE p (go x) (go y)
    LitBool p x -> LitBool p x
    -- integers
    Add p x y -> Add p (go x) (go y)
    Sub p x y -> Sub p (go x) (go y)
    Mul p x y -> Mul p (go x) (go y)
    Div p x y -> Div p (go x) (go y)
    Mod p x y -> Mod p (go x) (go y)
    Exp p x y -> Exp p (go x) (go y)
    LitInt p x -> LitInt p x
    IntEnv p x -> IntEnv p x
    -- bounds
    IntMin p x -> IntMin p x
    IntMax p x -> IntMax p x
    UIntMin p x -> UIntMin p x
    UIntMax p x -> UIntMax p x
    -- bytestrings
    Cat p x y -> Cat p (go x) (go y)
    Slice p x y z -> Slice p (go x) (go y) (go z)
    ByStr p x -> ByStr p x
    ByLit p x -> ByLit p x
    ByEnv p x -> ByEnv p x
    -- builtins
    NewAddr p x y -> NewAddr p (go x) (go y)
    -- polymorphic
    Eq  p x y -> Eq p (go x) (go y)
    NEq p x y -> NEq p (go x) (go y)
    ITE p x y z -> ITE p (go x) (go y) (go z)
    TEntry p _ item -> TEntry p time (go item)
    Var p t x -> Var p t x
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
  toJSON (Update SType a b) = object ["location" .= toJSON a ,"value" .= toJSON b]

instance ToJSON (TStorageItem a t) where
  toJSON (Item t a b []) = object ["sort" .= pack (show t)
                                  , "name" .= String (pack a <> "." <> pack b)]
  toJSON (Item _ a b c)  = mapping a b c

mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
mapping c a b = object [  "symbol"   .= pack "lookup"
                       ,  "arity"    .= Data.Aeson.Types.Number 3
                       ,  "args"     .= Array (fromList [toJSON c, toJSON a, toJSON b])]

instance ToJSON (TypedExp t) where
  toJSON (TExp typ a) = object ["sort"       .= pack (show typ)
                               ,"expression" .= toJSON a]

instance ToJSON (Exp a t) where
  toJSON (Add _ a b) = symbol "+" a b
  toJSON (Sub _ a b) = symbol "-" a b
  toJSON (Exp _ a b) = symbol "^" a b
  toJSON (Mul _ a b) = symbol "*" a b
  toJSON (Div _ a b) = symbol "/" a b
  toJSON (NewAddr _ a b) = symbol "newAddr" a b
  toJSON (LitInt _ a) = toJSON $ show a
  toJSON (IntMin _ a) = toJSON $ show $ intmin a
  toJSON (IntMax _ a) = toJSON $ show $ intmax a
  toJSON (UIntMin _ a) = toJSON $ show $ uintmin a
  toJSON (UIntMax _ a) = toJSON $ show $ uintmax a
  toJSON (IntEnv _ a) = String $ pack $ show a
  toJSON (ITE _ a b c) = object [  "symbol"   .= pack "ite"
                                ,  "arity"    .= Data.Aeson.Types.Number 3
                                ,  "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c])]
  toJSON (And _ a b)  = symbol "and" a b
  toJSON (Or _ a b)   = symbol "or" a b
  toJSON (LE _ a b)   = symbol "<" a b
  toJSON (GE _ a b)   = symbol ">" a b
  toJSON (Impl _ a b) = symbol "=>" a b
  toJSON (NEq _ a b)  = symbol "=/=" a b
  toJSON (Eq _ a b)   = symbol "==" a b
  toJSON (LEQ _ a b)  = symbol "<=" a b
  toJSON (GEQ _ a b)  = symbol ">=" a b
  toJSON (LitBool _ a) = String $ pack $ show a
  toJSON (Neg _ a) = object [  "symbol"   .= pack "not"
                            ,  "arity"    .= Data.Aeson.Types.Number 1
                            ,  "args"     .= Array (fromList [toJSON a])]

  toJSON (Cat _ a b) = symbol "cat" a b
  toJSON (Slice _ s a b) = object [ "symbol" .= pack "slice"
                                , "arity"  .= Data.Aeson.Types.Number 3
                                , "args"   .= Array (fromList [toJSON s, toJSON a, toJSON b])
                                ]
  toJSON (ByStr _ a) = toJSON a
  toJSON (ByLit _ a) = String . pack $ show a
  toJSON (ByEnv _ a) = String . pack $ show a

  toJSON (TEntry _ t a) = object [ Key.fromString (show t) .= toJSON a ]
  toJSON (Var _ _ a) = toJSON a

  toJSON v = error $ "todo: json ast for: " <> show v

symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= Data.Aeson.Types.Number 2
                      ,  "args"     .= Array (fromList [toJSON a, toJSON b])]

-- | Simplifies concrete expressions into literals.
-- Returns `Nothing` if the expression contains symbols.
eval :: Exp a t -> Maybe a
eval e = case e of
  And  _ a b    -> [a' && b' | a' <- eval a, b' <- eval b]
  Or   _ a b    -> [a' || b' | a' <- eval a, b' <- eval b]
  Impl _ a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  Neg  _ a      -> not <$> eval a
  LE   _ a b    -> [a' <  b' | a' <- eval a, b' <- eval b]
  LEQ  _ a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  GE   _ a b    -> [a' >  b' | a' <- eval a, b' <- eval b]
  GEQ  _ a b    -> [a' >= b' | a' <- eval a, b' <- eval b]
  LitBool _ a   -> pure a

  Add _ a b     -> [a' + b'     | a' <- eval a, b' <- eval b]
  Sub _ a b     -> [a' - b'     | a' <- eval a, b' <- eval b]
  Mul _ a b     -> [a' * b'     | a' <- eval a, b' <- eval b]
  Div _ a b     -> [a' `div` b' | a' <- eval a, b' <- eval b]
  Mod _ a b     -> [a' `mod` b' | a' <- eval a, b' <- eval b]
  Exp _ a b     -> [a' ^ b'     | a' <- eval a, b' <- eval b]
  LitInt  _ a   -> pure a
  IntMin  _ a   -> pure $ intmin  a
  IntMax  _ a   -> pure $ intmax  a
  UIntMin _ a   -> pure $ uintmin a
  UIntMax _ a   -> pure $ uintmax a

  Cat _ s t     -> [s' <> t' | s' <- eval s, t' <- eval t]
  Slice _ s a b -> [BS.pack . genericDrop a' . genericTake b' $ s'
                            | s' <- BS.unpack <$> eval s
                            , a' <- eval a
                            , b' <- eval b]
  ByStr _ s     -> pure . fromString $ s
  ByLit _ s     -> pure s

  Eq  _ a b     -> [a' == b' | a' <- eval a, b' <- eval b]
  NEq _ a b     -> [a' /= b' | a' <- eval a, b' <- eval b]
  ITE _ a b c   -> eval a >>= \cond -> if cond then eval b else eval c
  _             -> empty

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1

_Var :: SingI a => Id -> Exp a t
_Var name = Var nowhere sing name

castTime :: (Typeable t, Typeable u) => Exp a u -> Maybe (Exp a t)
castTime = gcast

castType :: (Typeable a, Typeable x) => Exp x t -> Maybe (Exp a t)
castType = gcast0

-- | Analogous to `gcast1` and `gcast2` from `Data.Typeable`. We *could* technically use `cast` instead
-- but then we would catch too many errors at once, so we couldn't emit informative error messages.
gcast0 :: forall t t' a. (Typeable t, Typeable t') => t a -> Maybe (t' a)
gcast0 x = fmap (\Refl -> x) (eqT :: Maybe (t :~: t'))
