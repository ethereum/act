{-# LANGUAGE GADTs #-}

module Enrich (enrich, mkStorageBounds) where

import Data.Maybe
import Data.List (nub)
import qualified Data.Map.Strict as Map (lookup)

import EVM.ABI (AbiType(..))
import EVM.Solidity (SlotType(..))

import RefinedAst
import Type (bound, defaultStore)
import Syntax (EthEnv(..), Id, Decl(..), Interface(..))
import Extract

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
    definition (Invariant c _ _ _) = head $ filter (\b -> Pass == _cmode b && _cname b == c) [c' | C c' <- claims]

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
enrichInvariant store (Constructor _ _ (Interface _ decls) _ _ _ _) inv@(Invariant _ preconds storagebounds predicate) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
      storagebounds' = storagebounds
                       <> mkStorageBounds store (Left <$> locsFromExp predicate)

mkEthEnvBounds :: [EthEnv] -> [Exp Bool]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp Bool)
    mkBound e = case lookup e defaultStore of
      Just (Integer) -> Just $ bound (toAbiType e) (IntEnv e)
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
mkStorageBounds :: Store -> [Either StorageLocation StorageUpdate] -> [Exp Bool]
mkStorageBounds store refs
  = catMaybes $ mkBound <$> refs
  where
    mkBound :: Either StorageLocation StorageUpdate -> Maybe (Exp Bool)
    mkBound (Left (IntLoc item)) = Just $ fromItem item
    mkBound (Right (IntUpdate item _)) = Just $ fromItem item
    mkBound _ = Nothing

    fromItem :: TStorageItem Integer -> Exp Bool
    fromItem item@(DirectInt contract name) = bound (abiType $ slotType contract name) (TEntry item)
    fromItem item@(MappedInt contract name _) = bound (abiType $ slotType contract name) (TEntry item)

    slotType :: Id -> Id -> SlotType
    slotType contract name = let
        vars = fromMaybe (error $ contract <> " not found in " <> show store) $ Map.lookup contract store
      in fromMaybe (error $ name <> " not found in " <> show vars) $ Map.lookup name vars

    abiType :: SlotType -> AbiType
    abiType (StorageMapping _ typ) = typ
    abiType (StorageValue typ) = typ

mkCallDataBounds :: [Decl] -> [Exp Bool]
mkCallDataBounds =
    concatMap
      ( \(Decl typ name) -> case metaType typ of
          Integer -> [bound typ (IntVar name)]
          _ -> []
      )
