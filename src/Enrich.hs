{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Enrich (enrich, mkStorageBounds) where

import Data.Maybe
import Data.List (nub)

import Syntax
import Syntax.Annotated
import Type (bound, defaultStore)

-- | Adds extra preconditions to non constructor behaviours based on the types of their variables
enrich :: Act -> Act
enrich (Act store contracts) = Act store (enrichContract <$> contracts)
  where
    enrichContract (Contract ctors behvs) = Contract (enrichConstructor <$> ctors) (enrichBehaviour <$> behvs)

-- |Adds type bounds for calldata , environment vars, and external storage vars as preconditions
enrichConstructor :: Constructor -> Constructor
enrichConstructor ctor@(Constructor _ _ (Interface _ decls) pre _ invs _ storageUpdates) =
  ctor { _cpreconditions = pre'
       , _invariants = invs' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds storageUpdates
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
      invs' = enrichInvariant ctor <$> invs

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
enrichBehaviour :: Behaviour -> Behaviour
enrichBehaviour behv@(Behaviour _ _ _ (Interface _ decls) pre _ stateUpdates _) =
  behv { _preconditions = pre' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds stateUpdates
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)

-- | Adds type bounds for calldata, environment vars, and storage vars
enrichInvariant :: Constructor -> Invariant -> Invariant
enrichInvariant (Constructor _ _ (Interface _ decls) _ _ _ _ _) inv@(Invariant _ preconds storagebounds (predicate,_)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
      storagebounds' = storagebounds
                       <> mkStorageBounds (Constant <$> locsFromExp predicate)

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean)
    mkBound e = case lookup e defaultStore of
      Just AInteger -> Just $ bound (PrimitiveType $ toAbiType e) (IntEnv nowhere e)
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
mkStorageBounds :: [Rewrite] -> [Exp ABoolean]
mkStorageBounds refs = catMaybes $ mkBound <$> refs
  where
    mkBound :: Rewrite -> Maybe (Exp ABoolean)
    mkBound (Constant (Loc SInteger item)) = Just $ fromItem item
    mkBound (Rewrite (Update SInteger item _)) = Just $ fromItem item
    mkBound _ = Nothing

    fromItem :: TStorageItem AInteger -> Exp ABoolean
    fromItem item@(Item _ vt _) = bound vt (TEntry nowhere Pre item)

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl typ name) -> case fromAbiType typ of
  AInteger -> [bound (PrimitiveType typ) (_Var name)]
  _ -> []
