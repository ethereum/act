{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Act.Bounds (addBounds) where

import Data.Maybe
import Data.List (nub)

import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.Type (globalEnv)


{-|

Module      : Bounds
Description : This pass adds integer add integer type bounds as preconditions
and postconditions.
-}

-- | Adds preconditions and postconditions to constructors and behaviors that
-- ensure that integer calldata and storage variables are within the range
-- specified by their types.
addBounds :: Act -> Act
addBounds (Act store contracts) = Act store (addBoundsContract <$> contracts)
  where
    addBoundsContract (Contract ctors behvs) = Contract (addBoundsConstructor ctors) (addBoundsBehaviour <$> behvs)

-- | Adds type bounds for calldata, environment vars, and external storage vars
-- as preconditions
addBoundsConstructor :: Constructor -> Constructor
addBoundsConstructor ctor@(Constructor _ (Interface _ decls) _ pre post invs stateUpdates) =
  ctor { _cpreconditions = pre'
       , _cpostconditions = post'
       , _invariants = invs' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
             <> mkStorageBoundsLoc (nub $ concatMap locsFromExp pre <> concatMap locsFromUpdateRHS stateUpdates)
      invs' = addBoundsInvariant ctor <$> invs
      post' = post <> mkStorageBounds stateUpdates Post

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
addBoundsBehaviour :: Behaviour -> Behaviour
addBoundsBehaviour behv@(Behaviour _ _ (Interface _ decls) _ pre cases post stateUpdates _) =
  behv { _preconditions = pre', _postconditions = post' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkStorageBounds stateUpdates Pre
             <> mkStorageBoundsLoc (nub $ concatMap locsFromExp (pre <> cases) <> concatMap locsFromUpdateRHS stateUpdates)
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)
      post' = post
              <> mkStorageBounds stateUpdates Post

-- | Adds type bounds for calldata, environment vars, and storage vars
addBoundsInvariant :: Constructor -> Invariant -> Invariant
addBoundsInvariant (Constructor _ (Interface _ decls) _ _ _ _ _) inv@(Invariant _ preconds storagebounds (PredTimed predicate _)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
      storagebounds' = storagebounds
                       <> mkStorageBoundsLoc (locsFromExp predicate)

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean)
    mkBound e = case lookup e globalEnv of
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

-- | Extracts bounds from the AbiTypes of Integer variables in storage
mkStorageBounds :: [StorageUpdate] -> When -> [Exp ABoolean]
mkStorageBounds refs t = concatMap mkBound refs
  where
    mkBound :: StorageUpdate -> [Exp ABoolean]
    mkBound (Update SInteger item _) = [mkItemBounds t item]
    mkBound _ = []

mkItemBounds :: When -> TItem AInteger Storage -> Exp ABoolean
mkItemBounds whn item@(Item _ (PrimitiveType vt) _) = bound vt (SVarRef nowhere whn item)
mkItemBounds _ (Item _ (ContractType _) _) = LitBool nowhere True

mkStorageBoundsLoc :: [StorageLocation] -> [Exp ABoolean]
mkStorageBoundsLoc refs = concatMap mkBound refs
  where
    mkBound :: StorageLocation -> [Exp ABoolean]
    mkBound (Loc SInteger item) = [mkItemBounds Pre item]
    mkBound _ = []

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl typ name) -> case fromAbiType typ of
  AInteger -> [bound typ (_Var typ name)]
  _ -> []
