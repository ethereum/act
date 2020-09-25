{-# Language RecordWildCards #-}
module HEVM where

import Prelude hiding (lookup)
import Syntax
import RefinedAst

import Data.Text
import Data.Maybe
import Data.Map
import Data.SBV.Control
import Data.SBV
import Control.Lens
import K
import Prove

import EVM hiding (Query)
import EVM.Solidity
import EVM.SymExec
import EVM.Symbolic
import EVM.Types

type SolcJson = Map Text SolcContract


proveBehaviour :: SolcJson -> Behaviour -> Query (Either (VM, [VM]) VM)
proveBehaviour sources behaviour = do
  vm <- initialVm sources behaviour
  mkVmContext sources behaviour vm
  let postC = specRelation sources behaviour
  verify vm Nothing Nothing (Just postC)

interfaceCalldata :: Interface -> Query Buffer
interfaceCalldata (Interface methodName vars) = error "TODO"

initialVm :: SolcJson -> Behaviour -> Query VM
initialVm sources b@Behaviour{..} = do
  let
    thisSource = fromMaybe (error ("Bytecode not found for: " <> show _contract <> ".\nSources available: " <> show (keys sources))) (lookup (pack _contract) sources)
  cd <- interfaceCalldata _interface
  caller' <- SAddr <$> freshVar_
  value' <- sw256 <$> freshVar_
  store <- Symbolic <$> freshArray_ (if _creation then Just 0 else Nothing)
  return $ loadSymVM
    (RuntimeCode $ view runtimeCode thisSource)
    store
    (if _creation then InitialS else SymbolicS)
    caller'
    value'
    (cd, literal $ fromIntegral $ len cd)

storageSlot :: StorageItem -> StorageLocation -> SymWord
storageSlot StorageItem{..} _ = error "TODO: storage locations"

-- preConditions :: Behaviour -> Ctx -> [SBool]
-- preConditions sources b@Behaviour{..} vm = error "TODO"

specRelation :: SolcJson -> Behaviour -> Postcondition
specRelation = error ""
-- specRelation sources Behaviour{..} (pre, post) = error "TODO"
  
mkVmContext :: SolcJson -> Behaviour -> VM -> Query (Ctx, Ctx)
mkVmContext solcjson Behaviour{..} vm = do
  error "TODO"
