{-# Language RecordWildCards #-}
{-# Language DataKinds #-}
module HEVM where

import Prelude hiding (lookup)
import Syntax
import RefinedAst hiding (S)

import Data.Text (Text, pack) -- hiding (length, drop, splitOn, null, breakOn, findIndex, splitAt)
import Data.Maybe
import Data.List hiding (lookup)
import Data.Map hiding (drop, null, findIndex, splitAt)
import Data.SBV.Control
import Data.SBV
import Control.Lens
import qualified Data.Vector as Vec

import K
import Prove
import Type

import EVM hiding (Query)
import EVM.Solidity
import EVM.ABI
import EVM.Concrete
import EVM.SymExec
import EVM.Symbolic
import EVM.Types

type SolcJson = Map Text SolcContract

proveBehaviour :: SolcJson -> Behaviour -> Symbolic (Either (VM, [VM]) VM)
proveBehaviour sources behaviour = do
  vm <- initialVm sources behaviour
  -- make context for trivial invariant
  let ctx = mkVmContext sources behaviour
--      preC vm = 
      postC (pre,post) = mkPostCondition behaviour (ctx pre post)
  query $ verify vm Nothing Nothing (Just postC)

interfaceCalldata :: Interface -> Symbolic Buffer
interfaceCalldata (Interface methodName vars) = error "TODO"

initialVm :: SolcJson -> Behaviour -> Symbolic VM
initialVm sources b@Behaviour{..} = do
  let
    thisSource = fromMaybe (error ("Bytecode not found for: " <> show _contract <> ".\nSources available: " <> show (keys sources))) (lookup (pack _contract) sources)
  cd <- interfaceCalldata _interface
  caller' <- SAddr <$> sWord_
  value' <- sw256 <$> sWord_
  store <- Symbolic <$> newArray_ (if _creation then Just 0 else Nothing)
  return $ loadSymVM
    (RuntimeCode $ view runtimeCode thisSource)
    store
    (if _creation then InitialS else SymbolicS)
    caller'
    value'
    (cd, literal $ fromIntegral $ len cd)

storageSlot :: StorageItem -> StorageLocation -> SymWord
storageSlot StorageItem{..} _ = error "TODO: storage locations"

-- assumes preconditions as well
mkPostCondition :: Behaviour -> (Ctx, Maybe SMType) -> SBool
mkPostCondition
  (Behaviour name mode creation contract interface preCond postCond updates returns)
  (ctx@(Ctx c m args store' env), actualReturn) =
  let storageConstraints = mkConstraint ctx <$> updates
      preCond' = symExpBool ctx Pre preCond
      postCond' = symExpBool ctx Pre postCond
      ret = symExp ctx Pre <$> returns
  in preCond' .=>
      (postCond' .&&
       ret .== actualReturn)
--  let preCond = _

--  storageConstraints = mkStorageConstraints ctx (_stateUpdates behv) locs

mkVmContext :: SolcJson -> Behaviour -> VM -> VM -> (Ctx, Maybe SMType)
mkVmContext solcjson (Behaviour method _ _ c1 (Interface _ decls) _ _ updates returns) pre post =
  let args = fromList $ flip fmap decls $
        \d@(Decl _ id) -> (id, locateCalldata d decls (fst $ view (state . calldata) pre))
--  _ <-  updates (lookup (storageSlot <$> updates))
      store = fromList $ flip fmap updates (locateStorage (pre, post))
      env = error "TODO"
      ret = error "TODO" -- returnexp
  in (Ctx c1 method args store env, ret)

locateStorage :: (VM,VM) -> Either StorageLocation StorageUpdate -> (Id, (SMType, SMType))
locateStorage (pre, post) (Right _) = error ""
locateStorage (pre, post) (Left _) = error ""

locateCalldata :: Decl -> [Decl] -> Buffer -> SMType
locateCalldata d@(Decl typ id) decls calldata = error ""
  -- if any (\(Decl typ _) -> abiKind typ /= Static) decls
  -- then error "dynamic calldata args currently unsupported"
  -- else
  --   let
  --     -- every argument is static right now; length is always 32
  --     offset = w256 $ fromIntegral $ 4 + 32 * (fromMaybe
  --                               (error ("internal error: could not find calldata var: " ++
  --                                id ++ " in interface declaration"))
  --                               (findIndex (== d) decls))
  --   in case metaType typ of
  --     -- all integers are 32 bytes
  --     Integer -> let S _ w = readSWord offset calldata
  --                in SymInteger $ sFromIntegral w
  --     -- interpret all nonzero values as boolean true
  --     Boolean -> SymBool $ readSWord offset calldata ./= 0
  --     _ -> error "TODO: support bytes"
