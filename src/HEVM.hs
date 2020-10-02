{-# Language RecordWildCards #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
module HEVM where

import Prelude hiding (lookup)
import Syntax
import RefinedAst hiding (S)

import Data.Text (Text, pack) -- hiding (length, drop, splitOn, null, breakOn, findIndex, splitAt)
import Data.Maybe
import Data.List hiding (lookup)
import Data.Map hiding (drop, null, findIndex, splitAt, foldl)
import qualified Data.Map as Map
import Data.SBV.Control
import Data.SBV
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Control.Lens
import Control.Monad
import qualified Data.Vector as Vec

import K hiding (storage)
import Prove
import Type

import EVM hiding (Query)
import EVM.Solidity hiding (Method)
import EVM.ABI
import EVM.Concrete
import EVM.SymExec
import EVM.Symbolic
import EVM.Types

type SolcJson = Map Text SolcContract

proveBehaviour :: SolcJson -> Behaviour -> Symbolic (Either (VM, [VM]) VM)
proveBehaviour sources behaviour = do
  let contractMap :: Map Id Addr -- TODO: this can be given as an option as well
                                 -- (in case you wanna verify against rpc or smth)
      contractMap = error "TODO"
  vm <- initialVm sources behaviour contractMap
  -- make context for trivial invariant
  let ctx = mkVmContext sources behaviour contractMap

--      preC vm = 
      postC (pre,post) = mkPostCondition behaviour (ctx pre post)
  query $ verify vm Nothing Nothing (Just postC)

interfaceCalldata :: Interface -> Symbolic Buffer
interfaceCalldata (Interface methodName vars) = error "TODO"

initialVm :: SolcJson -> Behaviour -> Map Id Addr -> Symbolic VM
initialVm sources b@Behaviour{..} contractMap = do
  let
    thisSource = fromMaybe (error ("Bytecode not found for: " <> show _contract <> ".\nSources available: " <> show (keys sources))) (lookup (pack _contract) sources)
  cd <- interfaceCalldata _interface
  caller' <- SAddr <$> sWord_
  value' <- sw256 <$> sWord_
  store <- Symbolic <$> newArray_ (if _creation then Just 0 else Nothing)
  contracts' <- forM (toList contractMap)
    (\(contractId, addr) -> do
        store <- Symbolic <$> newArray_ Nothing
        let code' = RuntimeCode $ view runtimeCode $
              fromMaybe (error "bytecode not found")
              (lookup (pack contractId) sources)
            c = initialContract code' & set storage store
        return (addr, c))

  return $ loadSymVM
    (RuntimeCode $ view runtimeCode thisSource)
    store
    (if _creation then InitialS else SymbolicS)
    caller'
    value'
    (cd, literal $ fromIntegral $ len cd)
    & over (env . contracts) (\a -> a <> (fromList contracts'))

storageSlot :: StorageItem -> StorageLocation -> SymWord
storageSlot StorageItem{..} _ = error "TODO: storage locations"

-- assumes preconditions as well
mkPostCondition :: Behaviour -> (Ctx, Maybe SMType) -> SBool
mkPostCondition
  (Behaviour name mode creation contract interface preCond postCond updates returns)
  (ctx@(Ctx c m args store' env), actualReturn) =
  let storageConstraints = sAnd $ mkConstraint ctx <$> updates
      preCond' = symExpBool ctx Pre preCond
      postCond' = symExpBool ctx Pre postCond
      ret = symExp ctx Pre <$> returns
  in preCond' .=>
      (postCond' .&&
      storageConstraints .&&
       ret .== actualReturn)
--  let preCond = _

--  storageConstraints = mkStorageConstraints ctx (_stateUpdates behv) locs

mkVmContext :: SolcJson -> Behaviour -> Map Id Addr -> VM -> VM -> (Ctx, Maybe SMType)
mkVmContext solcjson (Behaviour method _ _ c1 (Interface _ decls) _ _ updates returns) contractMap pre post =
  let args = fromList $ flip fmap decls $
        \d@(Decl _ id) -> (id, locateCalldata d decls (fst $ view (state . calldata) pre))
      env = error "TODO"
      ret = error "TODO" -- returnexp
      -- add storage entries to the 'store' map as we go along
      ctx = foldl
       (\ctx@(Ctx c1 method args store env) update' ->
         let
           (id, entry) = locateStorage ctx solcjson contractMap method (pre, post) update'
         in Ctx c1 method args (Map.insert id entry store) env) (Ctx c1 method args mempty env) updates
  in (ctx, ret)

locateStorage :: Ctx -> SolcJson -> Map Id Addr -> Method -> (VM,VM) -> Either StorageLocation StorageUpdate -> (Id, (SMType, SMType))
locateStorage ctx solcjson contractMap method (pre, post) (Right update) = case update of
  (IntUpdate item@(MappedInt contractId _ _) exp) ->
    let addr = fromMaybe (error "internal error: could not find contract") (lookup contractId contractMap)
        Just preContract = view (env . contracts . at addr) pre
        Just postContract = view (env . contracts . at addr) post
        Just (S _ preValue) = readStorage (view storage preContract) (calculateSlot ctx solcjson item)
        Just (S _ postValue) = readStorage (view storage postContract) (calculateSlot ctx solcjson item)
    in (nameFromItem method item,  (SymInteger (sFromIntegral preValue), SymInteger (sFromIntegral postValue)))
  _ -> error "TODO"
locateStorage ctx solcjson contractMap method (pre, post) (Left _) = error ""


calculateSlot :: Ctx -> SolcJson -> TStorageItem Integer -> SymWord
calculateSlot ctx solcjson (MappedInt contractId containerId ixs) =
  let source = fromMaybe (error "internal error: could not find contract") (lookup (pack contractId) solcjson)
      layout = fromMaybe (error "internal error: no storageLayout") $ _storageLayout source
      StorageItem typ offset slot = fromMaybe (error "containerId not found in storageLayout") $ lookup (pack containerId) layout
      indexers :: NonEmpty SMType
      indexers = symExp ctx Pre <$> ixs
      start = setMemoryWord' 0 (w256lit (fromIntegral slot)) []
  in sw256 $ symkeccak' $ foldl (\a b -> toBytes $ symkeccak' (a <> (toSymBytes b))) start indexers

toSymBytes :: SMType -> [SWord 8]
toSymBytes (SymInteger i) = toBytes (sFromIntegral i :: SWord 256)
toSymBytes (SymBool i) = ite i (toBytes (1 :: SWord 256)) (toBytes (0 :: SWord 256))
toSymBytes (SymBytes i) = error "unsupported"

locateCalldata :: Decl -> [Decl] -> Buffer -> SMType
locateCalldata d@(Decl typ id) decls calldata =
  if any (\(Decl typ _) -> abiKind typ /= Static) decls
  then error "dynamic calldata args currently unsupported"
  else
    let
      -- every argument is static right now; length is always 32
      offset = w256 $ fromIntegral $ 4 + 32 * (fromMaybe
                                (error ("internal error: could not find calldata var: " ++
                                 id ++ " in interface declaration"))
                                (findIndex (== d) decls))
    in case metaType typ of
      -- all integers are 32 bytes
      Integer -> let S _ w = readSWord offset calldata
                 in SymInteger $ sFromIntegral w
      -- interpret all nonzero values as boolean true
      Boolean -> SymBool $ readSWord offset calldata ./= 0
      _ -> error "TODO: support bytes"
