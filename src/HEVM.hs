{-# Language RecordWildCards #-}
{-# Language LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language OverloadedStrings #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
module HEVM where

import Prelude hiding (lookup)
import Syntax
import RefinedAst hiding (S)

import Data.Text (Text, pack, splitOn)
import Data.Maybe
import Data.List hiding (lookup)
import Data.Map hiding (drop, null, findIndex, splitAt, foldl)
import qualified Data.Map as Map
import Control.Monad.State.Strict (execState)
import Data.SBV.Control
import Data.SBV
import Control.Lens hiding (pre)
import Control.Monad
import qualified Data.Vector as Vec

import Prove
import Type

import EVM hiding (Query)
import EVM.VMTest
import EVM.Solidity hiding (Method)
import EVM.ABI
import EVM.Concrete
import EVM.SymExec
import EVM.Symbolic
import EVM.Types

type SolcJson = Map Text SolcContract

proveBehaviour :: SolcJson -> Behaviour -> Symbolic (Either (VM, [VM]) VM)
proveBehaviour sources behaviour = do
  preVm <- initialVm sources' behaviour contractMap
  query $ do
    res <- verify preVm Nothing Nothing (Just postC)
    case res of
      Right vm -> do
        showCounterexample vm Nothing
        return res
      _ ->
        return res

   where
     -- todo: deal with ambiguities in contract name
     sources' = mapKeys (last . splitOn ":") sources

     -- create new addresses for each contract involved
     -- in the future addresses could be passed through the cli
     contractMap = fromList $ zipWith
       (\id' i -> (id', createAddress (Addr 0) i)) (nub $ (RefinedAst._contract behaviour):(contractsInvolved behaviour)) [0..]

     ctx = mkVmContext sources' behaviour contractMap

     postC (pre, post) = mkPostCondition behaviour (ctx pre post)

    
interfaceCalldata :: Interface -> Symbolic Buffer
interfaceCalldata (Interface methodname vars) =
  let types = fmap (\(Decl typ _) -> typ) vars
      textsig = pack $ methodname ++ "(" ++ intercalate "," (show <$> types) ++ ")"
      sig' = litBytes $ selector textsig
  in SymbolicBuffer <$> (sig' <>) <$> concatMapM mkabiArg types

initialVm :: SolcJson -> Behaviour -> Map Id Addr -> Symbolic VM
initialVm sources Behaviour{..} contractMap = do
  let
    -- todo; ensure no duplicates
    this = fromMaybe (error ("Bytecode not found for: " <> show _contract <> ".\nSources available: " <> show (keys sources))) (lookup (pack _contract) sources)
    c = fromMaybe (error ("Address not found for: " ++ show _contract ++ ".\nAvailable: " ++ show (keys contractMap))) (lookup _contract contractMap)
  cd <- interfaceCalldata _interface
  caller' <- SAddr <$> sWord_
  value' <- sw256 <$> sWord_
  store <- return $ Concrete mempty --this can be removed if we use something else than loadSymVM
  contracts' <- forM (toList contractMap) $
    \(contractId, addr) -> do
        let code' = RuntimeCode $ view runtimeCode $
              fromMaybe (error "bytecode not found")
              (lookup (pack contractId) sources)
        c' <- contractWithStore code' <$> Symbolic <$> newArray_ Nothing
        return (addr, c')

  let vm = loadSymVM
        (RuntimeCode $ view runtimeCode this)
        store
        (if _creation then InitialS else SymbolicS)
        caller'
        value'
        (cd, literal $ fromIntegral $ len cd)
        & over (env . contracts) (\a -> a <> (fromList contracts'))

  return $ initTx $ execState (loadContract c) vm

-- assumes preconditions as well
mkPostCondition :: Behaviour -> (Ctx, VMResult) -> SBool
mkPostCondition
  (Behaviour _ mode creation _ _ preCond postCond updates returns)
  (ctx, vmResult) =
  if creation then error "todo: constructor"
  else 
    let storageConstraints = sAnd $ mkConstraint ctx <$> updates
        preCond' = symExpBool ctx Pre preCond
        postCond' = symExpBool ctx Pre postCond
        (actual, reverted) = case vmResult of
          VMSuccess (ConcreteBuffer msg) -> (litBytes msg, sFalse)
          VMSuccess (SymbolicBuffer msg) -> (msg, sFalse)
          VMFailure (Revert _) -> ([], sTrue)
          _ -> ([], sFalse)
        expected = fromMaybe [] (toSymBytes <$> symExp ctx Pre <$> returns)

    in preCond' .=>
       (postCond' .&&
        storageConstraints .&&
        case mode of
          Pass -> sNot reverted .&& (actual .== expected)
          Fail -> reverted
          OOG -> error "internal error: OOG mode not supported yet")

-- | Locate the variables refered to in the act-spec in the vm
mkVmContext :: SolcJson -> Behaviour -> Map Id Addr -> VM -> VM -> (Ctx, VMResult)
mkVmContext solcjson b@(Behaviour method _ _ c1 (Interface _ decls) _ _ updates _) contractMap pre post =
  let args = fromList $ locateCalldata b decls (fst $ view (state . calldata) pre) <$> decls
      env' = makeVmEnv b pre
      -- we should always have a result after executing the vm fully.
      Just res = view result post
      -- add storage entries to the 'store' map as we go along
      ctx = foldl
       (\ctx'@(Ctx c m a s e) update' ->
         let
           (name, entry) = locateStorage ctx' solcjson contractMap method (pre, post) update'
         in Ctx c m a (Map.insert name entry s) e)
       (Ctx c1 method args mempty env') updates
  in (ctx, res)


makeVmEnv :: Behaviour -> VM -> Map Id SMType
makeVmEnv (Behaviour method _ _ c1 _ _ _ _ _) vm =
  fromList $
    [ Caller    |- SymInteger (sFromIntegral $ saddressWord160 (view (state . caller) vm))
    , Callvalue |- let S _ w = view (state . callvalue) vm
                   in SymInteger (sFromIntegral w)
    , Calldepth |- SymInteger (num $ length (view frames vm))
     -- the following environment variables are always concrete in hevm right now
    , Origin    |- SymInteger (num $ addressWord160 (view (tx . origin) vm))
    , Difficulty |- SymInteger (num $ (view (block . difficulty) vm))
    , Chainid |- SymInteger (num $ (view (env . chainId) vm))
    , Timestamp |- let S _ w = view (block . timestamp) vm
                   in SymInteger (sFromIntegral w)
    , This |- SymInteger (num $ addressWord160 (view (state . contract) vm))
    , Nonce |- SymInteger (num $ view (env . contracts . at (view (state . contract) vm)
                                       . non (initialContract (RuntimeCode mempty)) . nonce) vm)
      -- and this one does not even give a reasonable result
--    , Blockhash |- error "blockhash not available in hevm right now"
    ]
  where
    (|-) a b = (nameFromEnv c1 method a, b)

-- | Locate the variables refered to in the act-spec in the vm
locateStorage :: Ctx -> SolcJson -> Map Id Addr -> Method -> (VM,VM) -> Either StorageLocation StorageUpdate -> (Id, (SMType, SMType))
locateStorage ctx solcjson contractMap method (pre, post) item =
  let item' = getLoc item
      contractId = getContractId $ item'
      addr = fromMaybe (error "internal error: could not find contract")
        (lookup contractId contractMap)

      Just preContract = view (env . contracts . at addr) pre
      Just postContract = view (env . contracts . at addr) post


      Just (S _ preValue) = readStorage (view storage preContract) (calculateSlot ctx solcjson item')
      Just (S _ postValue) = readStorage (view storage postContract) (calculateSlot ctx solcjson item')

      name :: StorageLocation -> Id
      name (IntLoc i) = nameFromItem method i
      name (BoolLoc i) = nameFromItem method i
      name (BytesLoc i) = nameFromItem method i

  in (name item',  (SymInteger (sFromIntegral preValue), SymInteger (sFromIntegral postValue)))

-- | 
calculateSlot :: Ctx -> SolcJson -> StorageLocation -> SymWord
calculateSlot ctx solcjson loc =
  -- TODO: packing with offset
  let
    source = fromMaybe (error "internal error: could not find contract") (lookup (pack (getContractId loc)) solcjson)
    layout = fromMaybe (error "internal error: no storageLayout") $ _storageLayout source
    StorageItem _ offset slot = get (pack (getContainerId loc)) layout
    slotword = sFromIntegral (literal (fromIntegral slot :: Integer))
    indexers = symExp ctx Pre <$> getContainerIxs loc
  in sw256 $
     if null indexers
     then slotword
     else foldl (\a b -> keccak' (SymbolicBuffer (toBytes a <> (toSymBytes b)))) slotword indexers


locateCalldata :: Behaviour -> [Decl] -> Buffer -> Decl -> (Id, SMType)
locateCalldata b decls calldata' d@(Decl typ name) =
  if any (\(Decl typ' _) -> abiKind typ' /= Static) decls
  then error "dynamic calldata args currently unsupported"
  else (nameFromDecl (RefinedAst._contract b) (_name b) d, val)

  where
    -- every argument is static right now; length is always 32
    offset = w256 $ fromIntegral $ 4 + 32 * (fromMaybe
       (error ("internal error: could not find calldata var: " ++
        name ++ " in interface declaration"))
        (findIndex (== d) decls))

    val = case metaType typ of
      -- all integers are 32 bytes
      Integer -> let S _ w = readSWord offset calldata'
                 in SymInteger $ sFromIntegral w
      -- interpret all nonzero values as boolean true
      Boolean -> SymBool $ readSWord offset calldata' ./= 0
      _ -> error "TODO: support bytes"

-- | Embedd an SMType as a list of symbolic bytes
toSymBytes :: SMType -> [SWord 8]
toSymBytes (SymInteger i) = toBytes (sFromIntegral i :: SWord 256)
toSymBytes (SymBool i) = ite i (toBytes (1 :: SWord 256)) (toBytes (0 :: SWord 256))
toSymBytes (SymBytes _) = error "unsupported"


-- | Convenience functions for generating symbolic byte strings
freshbytes32 :: Symbolic [SWord 8]
freshbytes32 = toBytes <$> free_ @ (WordN 256)


-- | Adapted from SymExec.symAbiArg to fit into the `Symbolic` monad instead of
-- `Query`.
mkabiArg :: AbiType -> Symbolic [SWord 8]
mkabiArg (AbiUIntType n)  | n `mod` 8 == 0 && n <= 256 = freshbytes32
                          | otherwise = error "bad type"
mkabiArg (AbiIntType n)   | n `mod` 8 == 0 && n <= 256 = freshbytes32
                          | otherwise = error "bad type"
mkabiArg AbiBoolType     = freshbytes32
mkabiArg AbiAddressType  = freshbytes32
mkabiArg (AbiBytesType n) | n <= 32 = freshbytes32
                          | otherwise = error "bad type"
mkabiArg (AbiArrayType leng typ) =
  do args <- concat <$> mapM mkabiArg (replicate leng typ)
     return (litBytes (encodeAbiValue (AbiUInt 256 (fromIntegral leng))) <> args)
mkabiArg (AbiTupleType tuple) = concat <$> mapM mkabiArg (Vec.toList tuple)
mkabiArg n =
  error $ "TODO: symbolic abiencoding for"
    <> show n <> "."

-- | Literal keccak when input is concrete, uninterpreted function when input symbolic.
keccak' :: Buffer -> SWord 256
keccak' (SymbolicBuffer bytes) = case maybeLitBytes bytes of
  Nothing -> symkeccak' bytes
  Just bs -> keccak' (ConcreteBuffer bs)
keccak' (ConcreteBuffer bytes) = literal $ toSizzle $ wordValue $ keccakBlob bytes
