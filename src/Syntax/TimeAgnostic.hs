{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}


{-|
Module      : Syntax.TimeAgnostic
Description : AST data types which are agnostic to the timing used.

This module only exists to increase code reuse; the types defined here won't
be used directly, but will be instantiated with different timing parameters
at different steps in the AST refinement process. This way we don't have to
update mirrored types, instances and functions in lockstep.
-}
module Syntax.TimeAgnostic (module Syntax.TimeAgnostic) where

import Control.Applicative (empty)

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.List (genericDrop,genericTake,nub)
import Data.Map.Strict (Map)
import Data.String (fromString)
import Data.Typeable

import EVM.ABI (AbiType(..))
import EVM.Solidity (SlotType(..))

--import Syntax.Timing as Syntax.TimeAgnostic hiding (forceTime) -- These two avoid reexporting `forceTime`
--import Syntax.Timing (forceTime)                    -- without using an unmaintainable export list.
import Syntax.Timing -- as Syntax.TimeAgnostic

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
type family InvariantPred t where
  InvariantPred Untimed = Exp Bool Untimed
  InvariantPred Timed   = (Exp Bool Timed, Exp Bool Timed)

invExp :: InvariantPred Timed -> Exp Bool Timed
invExp = uncurry (<>)

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

--types understood by proving tools
data MType
  = Integer
  | Boolean
  | ByteStr
  deriving (Eq, Ord, Show, Read)

data Rewrite t
  = Constant (StorageLocation t)
  | Rewrite (StorageUpdate t)
  deriving (Show, Eq)

data StorageUpdate t
  = IntUpdate (TStorageItem Integer t) (Exp Integer t)
  | BoolUpdate (TStorageItem Bool t) (Exp Bool t)
  | BytesUpdate (TStorageItem ByteString t) (Exp ByteString t)
  deriving (Show, Eq)

data StorageLocation t
  = IntLoc (TStorageItem Integer t)
  | BoolLoc (TStorageItem Bool t)
  | BytesLoc (TStorageItem ByteString t)
  deriving (Show, Eq)

-- | References to items in storage, either as a map lookup or as a reading of
-- a simple variable. The third argument is a list of indices; it has entries iff
-- the item is referenced as a map lookup. The type is parametrized on a
-- timing `t` and a type `a`. `t` can be either `Timed` or `Untimed` and
-- indicates whether any indices that reference items in storage explicitly
-- refer to the pre-/post-state, or not. `a` is the type of the item that is
-- referenced.
data TStorageItem (a :: *) (t :: Timing) where
  IntItem    :: Id -> Id -> [TypedExp t] -> TStorageItem Integer t
  BoolItem   :: Id -> Id -> [TypedExp t] -> TStorageItem Bool t
  BytesItem  :: Id -> Id -> [TypedExp t] -> TStorageItem ByteString t
deriving instance Show (TStorageItem a t)
deriving instance Eq (TStorageItem a t)

-- | Expressions for which the return type is known.
data TypedExp t
  = ExpInt   (Exp Integer t)
  | ExpBool  (Exp Bool t)
  | ExpBytes (Exp ByteString t)
  deriving (Eq, Show)

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- All storage entries within an `Exp a t` contain a value of type `Time t`.
-- If `t ~ Timed`, the only possible such values are `Pre, Post :: Time Timed`, so each storage entry
-- will refer to either the prestate or the poststate.
-- In `t ~ Untimed`, the only possible such value is `Neither :: Time Untimed`, so all storage entries
-- will not explicitly refer any particular state.

-- It is recommended that backends always input `Exp Timed a` to their codegens (or `Exp Untimed a`
-- if postconditions and return values are irrelevant), as this makes it easier to generate
-- consistent variable names. `Untimed` expressions can be given a specific timing using `as`,
-- e.g. ``expr `as` Pre``.
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
  BoolVar :: Id -> Exp Bool t
  -- integers
  Add :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Sub :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Mul :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Div :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Mod :: Exp Integer t -> Exp Integer t -> Exp Integer t
  Exp :: Exp Integer t -> Exp Integer t -> Exp Integer t
  LitInt :: Integer -> Exp Integer t
  IntVar :: Id -> Exp Integer t
  IntEnv :: EthEnv -> Exp Integer t
  -- bounds
  IntMin :: Int -> Exp Integer t
  IntMax :: Int -> Exp Integer t
  UIntMin :: Int -> Exp Integer t
  UIntMax :: Int -> Exp Integer t
  -- bytestrings
  Cat :: Exp ByteString t -> Exp ByteString t -> Exp ByteString t
  Slice :: Exp ByteString t -> Exp Integer t -> Exp Integer t -> Exp ByteString t
  ByVar :: Id -> Exp ByteString t
  ByStr :: String -> Exp ByteString t
  ByLit :: ByteString -> Exp ByteString t
  ByEnv :: EthEnv -> Exp ByteString t
  -- builtins
  NewAddr :: Exp Integer t -> Exp Integer t -> Exp Integer t

  -- polymorphic
  Eq  :: (Eq a, Typeable a) => Exp a t -> Exp a t -> Exp Bool t
  NEq :: (Eq a, Typeable a) => Exp a t -> Exp a t -> Exp Bool t
  ITE :: Exp Bool t -> Exp a t -> Exp a t -> Exp a t
  TEntry :: TStorageItem a t -> Time t -> Exp a t
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
  _ == _ = False

instance Semigroup (Exp Bool t) where
  a <> b = And a b

instance Monoid (Exp Bool t) where
  mempty = LitBool True

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

-- instance Timeable Claim where
--   forceTime time claim = case claim of
--     C cstor -> C $ forceTime time cstor
--     B behvr -> B $ forceTime time behvr
--     I invar -> I $ forceTime time invar
--     S store -> S store

-- instance Timeable Transition where
--   forceTime time trans = case trans of
--     Ctor ctor -> Ctor $ forceTime time ctor
--     Behv behv -> Behv $ forceTime time behv

-- instance Timeable Invariant where
--   forceTime time inv@Invariant{..} = inv
--     { _ipreconditions = forceTime time <$> _ipreconditions
--     , _istoragebounds = forceTime time <$> _istoragebounds
--     , _predicate      = forceTime time _predicate
--     }

-- instance Timeable InvariantPred where
--   forceTime time invexp = either mkDouble mkSingle (proveTiming time)
--     where
--       mkDouble Refl = case invexp of
--         d@Double{} -> d
--         Single{..} -> Double { _prestate = setPre _agnostic, _poststate = setPost _agnostic }
--       mkSingle Refl = case invexp of
--         s@Single{} -> s
--         Double{..} -> Single { _agnostic = forceTime Neither _prestate }

-- instance Timeable Constructor where
--   forceTime time ctor@Constructor{..} = ctor
--     { _cpreconditions = forceTime time <$> _cpreconditions
--     , _initialStorage = forceTime time <$> _initialStorage
--     , _cstateUpdates  = forceTime time <$> _cstateUpdates
--     }

-- instance Timeable Behaviour where
--   forceTime time behv@Behaviour{..} = behv
--     { _preconditions = forceTime time <$> _preconditions
--     , _stateUpdates  = forceTime time <$> _stateUpdates
--     }

-- instance Timeable Rewrite where
--   forceTime time (Constant location) = Constant $ forceTime time location
--   forceTime time (Rewrite  update)   = Rewrite  $ forceTime time update

-- instance Timeable StorageUpdate where
--   forceTime time update = case update of
--     IntUpdate item expr -> IntUpdate (forceTime time item) (forceTime time expr)
--     BoolUpdate item expr -> BoolUpdate (forceTime time item) (forceTime time expr)
--     BytesUpdate item expr -> BytesUpdate (forceTime time item) (forceTime time expr)

-- instance Timeable StorageLocation where
--   forceTime time location = case location of
--     IntLoc item -> IntLoc $ forceTime time item
--     BoolLoc item -> BoolLoc $ forceTime time item
--     BytesLoc item -> BytesLoc $ forceTime time item

-- instance Timeable TypedExp where
--   forceTime time texp = case texp of
--     ExpInt exp -> ExpInt $ forceTime time exp
--     ExpBool exp -> ExpBool $ forceTime time exp
--     ExpBytes exp -> ExpBytes $ forceTime time exp

-- instance Timeable (Exp a) where
--   forceTime time expr = case expr of
--     And  x y -> And (forceTime time x) (forceTime time y)
--     Or   x y -> Or (forceTime time x) (forceTime time y)
--     Impl x y -> Impl (forceTime time x) (forceTime time y)
--     Neg x -> Neg (forceTime time x)
--     LE x y -> LE (forceTime time x) (forceTime time y)
--     LEQ x y -> LEQ (forceTime time x) (forceTime time y)
--     GEQ x y -> GEQ (forceTime time x) (forceTime time y)
--     GE x y -> GE (forceTime time x) (forceTime time y)
--     LitBool x -> LitBool x
--     BoolVar x -> BoolVar x
--     -- integers
--     Add x y -> Add (forceTime time x) (forceTime time y)
--     Sub x y -> Sub (forceTime time x) (forceTime time y)
--     Mul x y -> Mul (forceTime time x) (forceTime time y)
--     Div x y -> Div (forceTime time x) (forceTime time y)
--     Mod x y -> Mod (forceTime time x) (forceTime time y)
--     Exp x y -> Exp (forceTime time x) (forceTime time y)
--     LitInt x -> LitInt x
--     IntVar x -> IntVar x
--     IntEnv x -> IntEnv x
--     -- younds
--     IntMin x -> IntMin x
--     IntMax x -> IntMax x
--     UIntMin x -> UIntMin x
--     UIntMax x -> UIntMax x
--     -- yytestrings
--     Cat x y -> Cat (forceTime time x) (forceTime time y)
--     Slice x y z -> Slice (forceTime time x) (forceTime time y) (forceTime time z)
--     ByVar x -> ByVar x
--     ByStr x -> ByStr x
--     ByLit x -> ByLit x
--     ByEnv x -> ByEnv x
--     -- yuiltins
--     NewAddr x y -> NewAddr (forceTime time x) (forceTime time y)

--     -- polymorphic
--     Eq  x y -> Eq  (forceTime time x) (forceTime time y)
--     NEq x y -> NEq (forceTime time x) (forceTime time y)
--     ITE x y z -> ITE (forceTime time x) (forceTime time y) (forceTime time z)
--     TEntry item _ -> TEntry (forceTime time item) time

-- instance Timeable (TStorageItem a) where
--   forceTime time item = case item of
--     IntItem   c x ixs -> IntItem   c x $ forceTime time <$> ixs
--     BoolItem  c x ixs -> BoolItem  c x $ forceTime time <$> ixs
--     BytesItem c x ixs -> BytesItem c x $ forceTime time <$> ixs

-------------------------
-- * Data extraction * --
-------------------------

-- locsFromBehaviour :: Behaviour t -> [StorageLocation Untimed]
-- locsFromBehaviour (Behaviour _ _ _ _ preconds postconds rewrites returns) = nub $
--   concatMap locsFromExp preconds
--   <> concatMap locsFromExp postconds
--   <> concatMap locsFromRewrite rewrites
--   <> maybe [] locsFromTypedExp (forceTime Neither <$> returns)

-- locsFromConstructor :: Constructor t -> [StorageLocation Untimed]
-- locsFromConstructor (Constructor _ _ _ pre post initialStorage rewrites) = nub $
--   concatMap locsFromExp pre
--   <> concatMap locsFromExp post
--   <> concatMap locsFromRewrite rewrites
--   <> concatMap locsFromRewrite (Rewrite <$> initialStorage)

-- locsFromRewrite :: Rewrite t -> [StorageLocation Untimed]
-- locsFromRewrite update = nub $ case update of
--   Constant loc -> [forceTime Neither loc]
--   Rewrite (IntUpdate item e) -> locsFromItem item <> locsFromExp e
--   Rewrite (BoolUpdate item e) -> locsFromItem item <> locsFromExp e
--   Rewrite (BytesUpdate item e) -> locsFromItem item <> locsFromExp e

locsFromTypedExp :: TypedExp t -> [StorageLocation t]
locsFromTypedExp (ExpInt e) = locsFromExp e
locsFromTypedExp (ExpBool e) = locsFromExp e
locsFromTypedExp (ExpBytes e) = locsFromExp e

locsFromExp :: Exp a t -> [StorageLocation t]
locsFromExp = nub . go
  where
    go :: Exp a t -> [StorageLocation t]
    go e = case e of
      And a b   -> go a <> go b
      Or a b    -> go a <> go b
      Impl a b  -> go a <> go b
      Eq a b    -> go a <> go b
      LE a b    -> go a <> go b
      LEQ a b   -> go a <> go b
      GE a b    -> go a <> go b
      GEQ a b   -> go a <> go b
      NEq a b   -> go a <> go b
      Neg a     -> go a
      Add a b   -> go a <> go b
      Sub a b   -> go a <> go b
      Mul a b   -> go a <> go b
      Div a b   -> go a <> go b
      Mod a b   -> go a <> go b
      Exp a b   -> go a <> go b
      Cat a b   -> go a <> go b
      Slice a b c -> go a <> go b <> go c
      ByVar _ -> []
      ByStr _ -> []
      ByLit _ -> []
      LitInt _  -> []
      IntMin _  -> []
      IntMax _  -> []
      UIntMin _ -> []
      UIntMax _ -> []
      IntVar _  -> []
      LitBool _ -> []
      BoolVar _ -> []
      NewAddr a b -> go a <> go b
      IntEnv _ -> []
      ByEnv _ -> []
      ITE x y z -> go x <> go y <> go z
      TEntry a _ -> locsFromItem a

locsFromItem :: TStorageItem a t -> [StorageLocation t]
locsFromItem t = case t of
  IntItem   contract name ixs -> (IntLoc   $ IntItem   contract name ixs) : ixLocs ixs
  BoolItem  contract name ixs -> (BoolLoc  $ BoolItem  contract name ixs) : ixLocs ixs
  BytesItem contract name ixs -> (BytesLoc $ BytesItem contract name ixs) : ixLocs ixs
  where
    ixLocs :: [TypedExp t] -> [StorageLocation t]
    ixLocs = concatMap locsFromTypedExp

ethEnvFromBehaviour :: Behaviour t -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds postconds rewrites returns) = nub $
  concatMap ethEnvFromExp preconds
  <> concatMap ethEnvFromExp postconds
  <> concatMap ethEnvFromRewrite rewrites
  <> maybe [] ethEnvFromTypedExp returns

ethEnvFromConstructor :: Constructor t -> [EthEnv]
ethEnvFromConstructor (Constructor _ _ _ pre post initialStorage rewrites) = nub $
  concatMap ethEnvFromExp pre
  <> concatMap ethEnvFromExp post
  <> concatMap ethEnvFromRewrite rewrites
  <> concatMap ethEnvFromRewrite (Rewrite <$> initialStorage)

ethEnvFromRewrite :: Rewrite t -> [EthEnv]
ethEnvFromRewrite rewrite = case rewrite of
  Constant (IntLoc item) -> ethEnvFromItem item
  Constant (BoolLoc item) -> ethEnvFromItem item
  Constant (BytesLoc item) -> ethEnvFromItem item
  Rewrite (IntUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
  Rewrite (BoolUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
  Rewrite (BytesUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TStorageItem a t -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromItem

ethEnvFromTypedExp :: TypedExp t -> [EthEnv]
ethEnvFromTypedExp (ExpInt e) = ethEnvFromExp e
ethEnvFromTypedExp (ExpBool e) = ethEnvFromExp e
ethEnvFromTypedExp (ExpBytes e) = ethEnvFromExp e

ethEnvFromExp :: Exp a t -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp a t -> [EthEnv]
    go e = case e of
      And a b   -> go a <> go b
      Or a b    -> go a <> go b
      Impl a b  -> go a <> go b
      Eq a b    -> go a <> go b
      LE a b    -> go a <> go b
      LEQ a b   -> go a <> go b
      GE a b    -> go a <> go b
      GEQ a b   -> go a <> go b
      NEq a b   -> go a <> go b
      Neg a     -> go a
      Add a b   -> go a <> go b
      Sub a b   -> go a <> go b
      Mul a b   -> go a <> go b
      Div a b   -> go a <> go b
      Mod a b   -> go a <> go b
      Exp a b   -> go a <> go b
      Cat a b   -> go a <> go b
      Slice a b c -> go a <> go b <> go c
      ITE a b c -> go a <> go b <> go c
      ByVar _ -> []
      ByStr _ -> []
      ByLit _ -> []
      LitInt _  -> []
      IntVar _  -> []
      LitBool _ -> []
      BoolVar _ -> []
      IntMin _ -> []
      IntMax _ -> []
      UIntMin _ -> []
      UIntMax _ -> []
      NewAddr a b -> go a <> go b
      IntEnv a -> [a]
      ByEnv a -> [a]
      TEntry a _ -> ethEnvFromItem a

locFromRewrite :: Rewrite t -> StorageLocation t
locFromRewrite = onRewrite id locFromUpdate

locFromUpdate :: StorageUpdate t -> StorageLocation t
locFromUpdate update = case update of
  IntUpdate item _ -> IntLoc item
  BoolUpdate item _ -> BoolLoc item
  BytesUpdate item _ -> BytesLoc item

metaType :: AbiType -> MType
metaType (AbiUIntType _)     = Integer
metaType (AbiIntType  _)     = Integer
metaType AbiAddressType      = Integer
metaType AbiBoolType         = Boolean
metaType (AbiBytesType _)    = ByteStr
metaType AbiBytesDynamicType = ByteStr
metaType AbiStringType       = ByteStr
--metaType (AbiArrayDynamicType a) =
--metaType (AbiArrayType        Int AbiType
--metaType (AbiTupleType        (Vector AbiType)
metaType _ = error "Syntax.TimeAgnostic.metaType: TODO"

ixsFromItem :: TStorageItem a t -> [TypedExp t]
ixsFromItem (IntItem   _ _ ixs) = ixs
ixsFromItem (BoolItem  _ _ ixs) = ixs
ixsFromItem (BytesItem _ _ ixs) = ixs

onRewrite :: (StorageLocation t -> a) -> (StorageUpdate t -> a) -> Rewrite t -> a
onRewrite f _ (Constant  a) = f a
onRewrite _ g (Rewrite a) = g a

-- ------------------------
-- -- * JSON machinery * --
-- ------------------------

-- instance ToJSON (Claim t) where
--   toJSON (S storages) = object [ "kind" .= String "Storages"
--                                , "storages" .= toJSON storages]
--   toJSON (I (Invariant {..})) = object [ "kind" .= String "Invariant"
--                                        , "predicate" .= toJSON _predicate
--                                        , "preconditions" .= toJSON _ipreconditions
--                                        , "storagebounds" .= toJSON _istoragebounds
--                                        , "contract" .= _icontract]
--   toJSON (C (Constructor {..})) = object  [ "kind" .= String "Constructor"
--                                           , "contract" .= _cname
--                                           , "mode" .= (String . pack $ show _cmode)
--                                           , "interface" .= (String . pack $ show _cinterface)
--                                           , "preConditions" .= toJSON _cpreconditions
--                                           , "postConditions" .= toJSON _cpostconditions
--                                           , "storage" .= toJSON _initialStorage
--                                           ]
--   toJSON (B (Behaviour {..})) = object  [ "kind" .= String "Behaviour"
--                                         , "name" .= _name
--                                         , "contract" .= _contract
--                                         , "mode" .= (String . pack $ show _mode)
--                                         , "interface" .= (String . pack $ show _interface)
--                                         , "preConditions" .= toJSON _preconditions
--                                         , "postConditions" .= toJSON _postconditions
--                                         , "stateUpdates" .= toJSON _stateUpdates
--                                         , "returns" .= toJSON _returns]

-- instance ToJSON (InvariantPred t) where
--   toJSON (Single e) = toJSON e
--   toJSON (Double e _) = toJSON (forceTime Neither e)

-- instance ToJSON SlotType where
--   toJSON (StorageValue t) = object ["type" .= show t]
--   toJSON (StorageMapping ixTypes valType) = object [ "type" .= String "mapping"
--                                                    , "ixTypes" .= show (toList ixTypes)
--                                                    , "valType" .= show valType]

-- instance ToJSON (Rewrite t) where
--   toJSON (Constant a) = object [ "Constant" .= toJSON a ]
--   toJSON (Rewrite a) = object [ "Rewrite" .= toJSON a ]

-- instance ToJSON (StorageLocation t) where
--   toJSON (IntLoc a) = object ["location" .= toJSON a]
--   toJSON (BoolLoc a) = object ["location" .= toJSON a]
--   toJSON (BytesLoc a) = object ["location" .= toJSON a]

-- instance ToJSON (StorageUpdate t) where
--   toJSON (IntUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]
--   toJSON (BoolUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]
--   toJSON (BytesUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]

-- instance ToJSON (TStorageItem a t) where
--   toJSON (IntItem a b []) = object ["sort" .= pack "int"
--                                   , "name" .= String (pack a <> "." <> pack b)]
--   toJSON (BoolItem a b []) = object ["sort" .= pack "bool"
--                                    , "name" .= String (pack a <> "." <> pack b)]
--   toJSON (BytesItem a b []) = object ["sort" .= pack "bytes"
--                                     , "name" .= String (pack a <> "." <> pack b)]
--   toJSON (IntItem a b c) = mapping a b c
--   toJSON (BoolItem a b c) = mapping a b c
--   toJSON (BytesItem a b c) = mapping a b c

-- instance ToJSON (TypedExp t) where
--    toJSON (ExpInt a) = object ["sort" .= pack "int"
--                               ,"expression" .= toJSON a]
--    toJSON (ExpBool a) = object ["sort" .= String (pack "bool")
--                                ,"expression" .= toJSON a]
--    toJSON (ExpBytes a) = object ["sort" .= String (pack "bytestring")
--                                 ,"expression" .= toJSON a]

-- instance Typeable a => ToJSON (Exp a t) where
--   toJSON (Add a b) = symbol "+" a b
--   toJSON (Sub a b) = symbol "-" a b
--   toJSON (Exp a b) = symbol "^" a b
--   toJSON (Mul a b) = symbol "*" a b
--   toJSON (Div a b) = symbol "/" a b
--   toJSON (NewAddr a b) = symbol "newAddr" a b
--   toJSON (IntVar a) = String $ pack a
--   toJSON (LitInt a) = toJSON $ show a
--   toJSON (IntMin a) = toJSON $ show $ intmin a
--   toJSON (IntMax a) = toJSON $ show $ intmax a
--   toJSON (UIntMin a) = toJSON $ show $ uintmin a
--   toJSON (UIntMax a) = toJSON $ show $ uintmax a
--   toJSON (IntEnv a) = String $ pack $ show a
--   toJSON (TEntry a Neither) = toJSON a
--   toJSON (TEntry a t) = object [ "symbol" .= show t
--                                , "arity"  .= Data.Aeson.Types.Number 1
--                                , "args"   .= toJSON a]
--   toJSON (ITE a b c) = object [  "symbol"   .= pack "ite"
--                               ,  "arity"    .= Data.Aeson.Types.Number 3
--                               ,  "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c])]
--   toJSON (And a b)  = symbol "and" a b
--   toJSON (Or a b)   = symbol "or" a b
--   toJSON (LE a b)   = symbol "<" a b
--   toJSON (GE a b)   = symbol ">" a b
--   toJSON (Impl a b) = symbol "=>" a b
--   toJSON (NEq a b)  = symbol "=/=" a b
--   toJSON (Eq a b)   = symbol "==" a b
--   toJSON (LEQ a b)  = symbol "<=" a b
--   toJSON (GEQ a b)  = symbol ">=" a b
--   toJSON (LitBool a) = String $ pack $ show a
--   toJSON (BoolVar a) = toJSON a
--   toJSON (Neg a) = object [  "symbol"   .= pack "not"
--                           ,  "arity"    .= Data.Aeson.Types.Number 1
--                           ,  "args"     .= Array (fromList [toJSON a])]

--   toJSON (Cat a b) = symbol "cat" a b
--   toJSON (Slice s a b) = object [ "symbol" .= pack "slice"
--                                 , "arity"  .= Data.Aeson.Types.Number 3
--                                 , "args"   .= Array (fromList [toJSON s, toJSON a, toJSON b])
--                                 ]
--   toJSON (ByVar a) = toJSON a
--   toJSON (ByStr a) = toJSON a
--   toJSON (ByLit a) = String . pack $ show a
--   toJSON (ByEnv a) = String . pack $ show a
--   toJSON v = error $ "todo: json ast for: " <> show v

-- mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
-- mapping c a b = object [  "symbol"   .= pack "lookup"
--                        ,  "arity"    .= Data.Aeson.Types.Number 3
--                        ,  "args"     .= Array (fromList [toJSON c, toJSON a, toJSON b])]

-- symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
-- symbol s a b = object [  "symbol"   .= pack s
--                       ,  "arity"    .= Data.Aeson.Types.Number 2
--                       ,  "args"     .= Array (fromList [toJSON a, toJSON b])]

-- intmin :: Int -> Integer
-- intmin a = negate $ 2 ^ (a - 1)

-- intmax :: Int -> Integer
-- intmax a = 2 ^ (a - 1) - 1

-- uintmin :: Int -> Integer
-- uintmin _ = 0

-- uintmax :: Int -> Integer
-- uintmax a = 2 ^ a - 1

castTime :: (Typeable t, Typeable t0) => Exp a t0 -> Maybe (Exp a t)
castTime = gcast

castType :: (Typeable a, Typeable x) => Exp x t -> Maybe (Exp a t)
castType = gcast0

-- | Analogous to `gcast1` and `gcast2` from `Data.Typeable`. We *could* technically use `cast` instead
-- but then we would catch too many errors at once, so we couldn't emit informative error messages.
gcast0 :: forall t t' a. (Typeable t, Typeable t') => t a -> Maybe (t' a)
gcast0 x = fmap (\Refl -> x) (eqT :: Maybe (t :~: t'))
