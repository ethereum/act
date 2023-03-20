{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Enrich (enrich, mkStorageBounds) where

import Data.Maybe
import Data.List (nub)
import qualified Data.Map.Strict as Map (lookup)

import EVM.Solidity (SlotType(..))

import Syntax
import Syntax.Annotated
import Type (bound, defaultStore)

-- | Adds extra preconditions to non constructor behaviours based on the types of their variables
enrich :: [Claim] -> [Claim]
enrich claims = [S store]
                <> (I <$> ((\i -> enrichInvariant store (definition i) i) <$> invariants))
                <> (C <$> (enrichConstructor store <$> constructors))
                <> (B <$> (enrichBehaviour store <$> behaviours))
  where
    store = head [s | S s <- claims]
    behaviours = [b | B b <- claims]
    invariants = [i | I i <- claims]
    constructors = [c | C c <- claims]
    definition (Invariant c _ _ _) = head [c' | c' <- constructors, _cmode c' == Pass, _cname c' == c]

-- |Adds type bounds for calldata , environment vars, and external storage vars as preconditions
enrichConstructor :: Store -> Constructor -> Constructor
enrichConstructor store ctor@(Constructor _ _ (Interface _ decls) pre _ _ storageUpdates) =
  ctor { _cpreconditions = pre' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds store storageUpdates
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
enrichBehaviour :: Store -> Behaviour -> Behaviour
enrichBehaviour store behv@(Behaviour _ _ _ (Interface _ decls) pre _ stateUpdates _) =
  behv { _preconditions = pre' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds store stateUpdates
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)

-- | Adds type bounds for calldata, environment vars, and storage vars
enrichInvariant :: Store -> Constructor -> Invariant -> Invariant
enrichInvariant store (Constructor _ _ (Interface _ decls) _ _ _ _) inv@(Invariant _ preconds storagebounds (predicate,_)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
      storagebounds' = storagebounds
                       <> mkStorageBounds store (Constant <$> locsFromExp predicate)

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean)
    mkBound e = case lookup e defaultStore of
      Just AInteger -> Just $ bound (toAbiType e) (IntEnv nowhere e)
      _ -> Nothing

    toAbiType :: EthEnv -> AbiType
    toAbiType env = case env of
      Caller -> AbiAddressType
      Callvalue -> AbiUIntType 256
      Calldepth -> AbiUIntType 10
      Origin -> AbiAddressType
      Blockhash -> AbiBytesType 32
      Blocknumber -> AbiUIntType 256
      Difficulty -> AbiUIntType 256
      Chainid -> AbiUIntType 256
      Gaslimit -> AbiUIntType 256
      Coinbase -> AbiAddressType
      Timestamp -> AbiUIntType 256
      This -> AbiAddressType
      Nonce -> AbiUIntType 256

-- | extracts bounds from the AbiTypes of Integer values in storage
mkStorageBounds :: Store -> [Rewrite] -> [Exp ABoolean]
mkStorageBounds store refs = catMaybes $ mkBound <$> refs
  where
    mkBound :: Rewrite -> Maybe (Exp ABoolean)
    mkBound (Constant (Loc SInteger item)) = Just $ fromItem item
    mkBound (Rewrite (Update SInteger item _)) = Just $ fromItem item
    mkBound _ = Nothing

    fromItem :: TStorageItem AInteger -> Exp ABoolean
    fromItem item@(Item _ contract name _) = bound (abiType $ slotType contract name) (TEntry nowhere Pre item)

    slotType :: Id -> Id -> SlotType
    slotType contract name = let
        vars = fromMaybe (error $ contract <> " not found in " <> show store) $ Map.lookup contract store
      in fromMaybe (error $ name <> " not found in " <> show vars) $ Map.lookup name vars

    abiType :: SlotType -> AbiType
    abiType (StorageMapping _ typ) = typ
    abiType (StorageValue typ) = typ

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl typ name) -> case fromAbiType typ of
  AInteger -> [bound typ (_Var name)]
  _ -> []
