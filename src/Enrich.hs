{-# LANGUAGE GADTs #-}

module Enrich (enrich, mkStorageBounds) where

import Data.Maybe
import Data.List (nub)
import qualified Data.Map.Strict as Map (lookup)

import EVM.ABI (AbiType(..))
import EVM.Solidity (SlotType(..))

import RefinedAst
import Type (bound, defaultStore, metaType)
import Syntax (EthEnv(..), Id, Decl(..), Interface(..))

-- | Adds extra preconditions to non constructor behaviours based on the types of their variables
enrich :: [Claim] -> [Claim]
enrich claims = [S store]
                <> (I <$> invariants)
                <> (C <$> (enrichConstructor store <$> constructors))
                <> (B <$> (enrichBehaviour store <$> behaviours))
  where
    store = head $ [s | S s <- claims]
    behaviours = [b | B b <- claims]
    invariants = [i | I i <- claims]
    constructors = [c | C c <- claims]

-- |Adds type bounds for calldata / environment vars / external storage vars as preconditions, additionally forces all
-- local storage vars to be zero
enrichConstructor :: Store -> Constructor -> Constructor
enrichConstructor store ctor@(Constructor _ _ (Interface _ decls) pre _ initialStorage storageUpdates) =
  ctor { _cpreconditions = pre' }
    where
      pre' = pre
             <> (mkCallDataBounds decls)
             <> (forceZero initialStorage)
             <> (mkStorageBounds store storageUpdates)
             <> (mkEthEnvBounds $ ethEnvFromConstructor ctor)

-- |Adds type bounds for calldata / environment vars / storage vars as preconditions
enrichBehaviour :: Store -> Behaviour -> Behaviour
enrichBehaviour store behv@(Behaviour _ _ _ (Interface _ decls) pre _ stateUpdates _) =
  behv { _preconditions = pre' }
    where
      pre' = pre
             <> (mkCallDataBounds decls)
             <> (mkStorageBounds store stateUpdates)
             <> (mkEthEnvBounds $ ethEnvFromBehaviour behv)

ethEnvFromBehaviour :: Behaviour -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds postconds stateUpdates returns) =
  (concatMap ethEnvFromExp preconds)
  <> (concatMap ethEnvFromExp postconds)
  <> (concatMap ethEnvFromStateUpdate stateUpdates)
  <> (maybe [] ethEnvFromReturnExp returns)

ethEnvFromConstructor :: Constructor -> [EthEnv]
ethEnvFromConstructor (Constructor _ _ _ pre post initialStorage stateUpdates) =
  (concatMap ethEnvFromExp pre)
  <> (concatMap ethEnvFromExp post)
  <> (concatMap ethEnvFromStateUpdate stateUpdates)
  <> (concatMap ethEnvFromStateUpdate (Right <$> initialStorage))

ethEnvFromStateUpdate :: Either StorageLocation StorageUpdate -> [EthEnv]
ethEnvFromStateUpdate update = case update of
  Left (IntLoc item) -> ethEnvFromItem item
  Left (BoolLoc item) -> ethEnvFromItem item
  Left (BytesLoc item) -> ethEnvFromItem item
  Right (IntUpdate item e) -> ethEnvFromItem item <> ethEnvFromExp e
  Right (BoolUpdate item e) -> ethEnvFromItem item <> ethEnvFromExp e
  Right (BytesUpdate item e) -> ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TStorageItem a -> [EthEnv]
ethEnvFromItem item = case item of
  MappedInt _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  MappedBool _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  MappedBytes _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  _ -> []

ethEnvFromReturnExp :: ReturnExp -> [EthEnv]
ethEnvFromReturnExp (ExpInt e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBool e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBytes e) = ethEnvFromExp e

ethEnvFromExp :: Exp a -> [EthEnv]
ethEnvFromExp e = case e of
  And a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Or a b    -> ethEnvFromExp a <> ethEnvFromExp b
  Impl a b  -> ethEnvFromExp a <> ethEnvFromExp b
  Eq a b    -> ethEnvFromExp a <> ethEnvFromExp b
  LE a b    -> ethEnvFromExp a <> ethEnvFromExp b
  LEQ a b   -> ethEnvFromExp a <> ethEnvFromExp b
  GE a b    -> ethEnvFromExp a <> ethEnvFromExp b
  GEQ a b   -> ethEnvFromExp a <> ethEnvFromExp b
  NEq a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Neg a     -> ethEnvFromExp a
  Add a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Sub a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Mul a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Div a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Mod a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Exp a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Cat a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Slice a b c -> ethEnvFromExp a <> ethEnvFromExp b <> ethEnvFromExp c
  ITE a b c -> ethEnvFromExp a <> ethEnvFromExp b <> ethEnvFromExp c
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
  NewAddr a b -> ethEnvFromExp a <> ethEnvFromExp b
  IntEnv a -> [a]
  ByEnv a -> [a]
  TEntry a  -> ethEnvFromItem a

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

-- | constrain the locations referenced to be zero
forceZero :: [StorageUpdate] -> [Exp Bool]
forceZero = mapMaybe mkBound
  where
    mkBound :: StorageUpdate -> Maybe (Exp Bool)
    mkBound (IntUpdate item _) = Just $ Eq (TEntry item) (LitInt 0)
    mkBound (BoolUpdate item _) = Just $ Eq (TEntry item) (LitBool False)
    mkBound (BytesUpdate item _) = Just $ Eq (TEntry item) (ByLit mempty)

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
