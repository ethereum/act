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

import EVM hiding (Query)
import EVM.Solidity
import EVM.SymExec
import EVM.Symbolic
import EVM.Types

type SolcJson = Map Text SolcContract

proveBehaviour :: SolcJson -> Behaviour -> Query (Either (VM, [VM]) VM)
proveBehaviour sources behaviour = do
  vm <- initialVm sources behaviour
  let postC = specRelation sources behaviour
  verify vm Nothing Nothing (Just postC)


interfaceCalldata :: Interface -> Query Buffer
interfaceCalldata (Interface methodName vars) = _

initialVm :: SolcJson -> Behaviour -> Query VM
initialVm sources b@Behaviour{..} = do
  let
    thisSource = fromMaybe (error ("Bytecode not found for: " <> show _contract <> ".\nSources available: " <> show (keys sources))) (lookup (pack _contract) sources)
  cd <- interfaceCalldata _interface
  caller' <- SAddr <$> freshVar_
  value' <- sw256 <$> freshVar_
  store <- Symbolic <$> freshArray_ (if _creation then Just 0 else Nothing)
  let vm = loadSymVM
             (RuntimeCode $ view runtimeCode thisSource)
             store
             (if _creation then InitialS else SymbolicS)
             caller'
             value'
             (cd, literal $ fromIntegral $ len cd)
  return $ over pathConditions (<> (preConditions sources b vm)) vm

storageSlot :: StorageItem -> StorageLocation -> SymWord
storageSlot StorageItem{..} _ = error "TODO: storage locations"


preConditions :: SolcJson -> Behaviour -> VM -> [SBool]
preConditions sources b@Behaviour{..} vm = _

specRelation :: SolcJson -> Behaviour -> Postcondition
specRelation sources Behaviour{..} (pre, post) = _
  
