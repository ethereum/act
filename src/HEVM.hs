{-# Language RecordWildCards #-}
{-# Language TypeApplications #-}
{-# Language OverloadedStrings #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language MonadComprehensions #-}
{-# Language ViewPatterns #-}

module HEVM where

import Prelude hiding (lookup, GT, LT)

import Syntax
import Syntax.Annotated as Annotated

import Data.ByteString.UTF8 (toString)
import Data.Text (Text, pack, splitOn)
import Data.Maybe
import Data.List hiding (lookup)
import Data.Map hiding (drop, null, findIndex, splitAt, foldl, foldr, filter)
import qualified Data.Map as Map
import Control.Monad.State.Strict (execState)
import Data.SBV.Control
import Data.SBV
import Data.SBV.String ((.++), subStr)
import Control.Lens hiding (op, pre, (.>))
import Control.Monad
import qualified Data.Vector as Vec

import Print

import EVM hiding (Query)
import EVM.VMTest
import EVM.Solidity hiding (Method)
import EVM.ABI
import EVM.Concrete
import EVM.SymExec
import EVM.Symbolic
import EVM.Types (SymWord(..), Buffer(..), Addr(..), toSizzle, litBytes, num, var, w256, SAddr(..))

type SolcJson = Map Text SolcContract

proveBehaviour :: SolcJson -> Behaviour -> Symbolic VerifyResult
proveBehaviour sources behaviour = do
  preVm <- initialVm sources' behaviour contractMap
  query $ do
    res <- verify preVm Nothing Nothing Nothing (Just postC)
    case res of
      Cex tree -> do
        showCounterexample preVm Nothing
        return $ Cex tree
      Timeout tree -> return $ Timeout tree
      Qed tree -> return $ Qed tree

   where
     -- todo: deal with ambiguities in contract name
     sources' = mapKeys (last . splitOn ":") sources

     -- create new addresses for each contract involved
     -- in the future addresses could be passed through the cli
     contractMap = fromList $ zipWith
       (\id' i -> (id', createAddress (Addr 0) i)) (nub $ (Annotated._contract behaviour):(contractsInvolved behaviour)) [0..]

     ctx = mkVmContext sources' behaviour contractMap

     postC (pre, post) = mkPostCondition pre post sources' behaviour contractMap (ctx pre post)


interfaceCalldata :: Interface -> Symbolic Buffer
interfaceCalldata (Interface methodname vars) =
  let types = fmap (\(Decl typ _) -> typ) vars
      textsig = pack $ methodname ++ "(" ++ intercalate "," (show <$> types) ++ ")"
      sig' = litBytes $ selector textsig
  in SymbolicBuffer . (sig' <>) <$> concatMapM mkabiArg types

initialVm :: SolcJson -> Behaviour -> Map Id Addr -> Symbolic VM
initialVm sources Behaviour{..} contractMap = do
  let
    -- todo; ensure no duplicates
    this = fromMaybe (error ("Bytecode not found for: " <> show _contract <> ".\nSources available: " <> show (keys sources))) (lookup (pack _contract) sources)
    addr = fromMaybe (error ("Address not found for: " ++ show _contract ++ ".\nAvailable: " ++ show (keys contractMap))) (lookup _contract contractMap)
    store = Concrete mempty
  cd <- interfaceCalldata _interface
  caller' <- SAddr <$> sWord_
  value' <- (var "CALLVALUE") <$> sWord_
  contracts' <- forM (toList contractMap) $
    \(contractId, addr') -> do
        let code' = RuntimeCode . ConcreteBuffer $ view runtimeCode $
              fromMaybe (error "bytecode not found")
              (lookup (pack contractId) sources)
        c' <- contractWithStore code' . (Symbolic []) <$> newArray_ Nothing
        return (addr', c')

  let vm = loadSymVM
        (RuntimeCode . ConcreteBuffer $ view runtimeCode this)
        store
        SymbolicS
        caller'
        value'
        (cd, num $ len cd)
        & over (env . contracts) (\a -> a <> (fromList contracts'))

  return $ initTx $ execState (loadContract addr) vm

checkPostStorage :: Ctx -> Behaviour -> VM -> VM -> Map Id Addr -> SolcJson -> SBV Bool
checkPostStorage ctx (Behaviour _ _ _ _ _ _ rewrites _) pre post contractMap solcjson =
  sAnd $ flip fmap (keys (view (EVM.env . EVM.contracts) post)) $
    \addr ->
      case view (EVM.env . EVM.contracts . at addr) pre of
        Nothing -> sFalse -- TODO: deal with creations
        Just precontract ->
          let
            Just postcontract = view (EVM.env . EVM.contracts . at addr) post
            prestorage = view EVM.storage precontract
            poststorage = view EVM.storage postcontract
          in case (prestorage, poststorage) of
              (Concrete pre', Concrete post') -> literal $ pre' == post'
              (Symbolic _ pre', Symbolic _ post') ->
               let
                 insertions = updatesFromRewrites $ filter (\a -> addr == get (contractFromRewrite a) contractMap) rewrites
                 slot update' = let S _ w = calculateSlot ctx solcjson (locFromUpdate update')
                               in w
                 insertUpdate :: SArray (WordN 256) (WordN 256) -> StorageUpdate -> SArray (WordN 256) (WordN 256)
                 insertUpdate store u@(Update SInteger _ e) = writeArray store (slot u) $ sFromIntegral $ symExpInt ctx e
                 insertUpdate store u@(Update SBoolean _ e) = writeArray store (slot u) $ ite (symExpBool ctx e) 1 0
                 insertUpdate _ _ = error "bytes unsupported"
               in post' .== foldl insertUpdate pre' insertions
              _ -> sFalse


-- assumes preconditions as well
mkPostCondition :: VM -> VM -> SolcJson -> Behaviour -> Map Id Addr -> (Ctx, VMResult) -> SBool
mkPostCondition preVm postVm solcjson
  b@(Behaviour _ _ _ preCond ifs postCond _ returns)
  contractMap
  (ctx, vmResult) =
    let storageConstraints = checkPostStorage ctx b preVm postVm contractMap solcjson
        preCondPass = symExpBool ctx (mconcat (preCond <> ifs))
        preCondFail = symExpBool ctx (Neg nowhere (mconcat preCond))
        
        postCond' = symExpBool ctx (mconcat postCond)
        (actual, reverted) = case vmResult of
          VMSuccess (ConcreteBuffer msg) -> (litBytes msg, sFalse)
          VMSuccess (SymbolicBuffer msg) -> (msg, sFalse)
          VMFailure (Revert _) -> ([], sTrue)
          _ -> ([], sFalse)
        expected = maybe [] (toSymBytes . symExp ctx) returns

    in (preCondPass .=>
        (postCond' .&& storageConstraints .&& sNot reverted .&& (actual .== expected))) .&&
       (preCondFail .=> reverted) -- TODO shall we check for postCond' .&& storageConstraints here?

-- | Locate the variables refered to in the act-spec in the vm
mkVmContext :: SolcJson -> Behaviour -> Map Id Addr -> VM -> VM -> (Ctx, VMResult)
mkVmContext solcjson b@(Behaviour method c1 (Interface _ decls) _ _ _ updates _) contractMap pre post =
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


makeVmEnv :: Behaviour -> VM -> Map Id SActType
makeVmEnv (Behaviour method c1 _ _ _ _ _ _) vm =
  fromList
    [ Caller    |- SymInteger (sFromIntegral $ saddressWord160 (view (state . caller) vm))
    , Callvalue |- let S _ w = view (state . callvalue) vm
                   in SymInteger (sFromIntegral w)
    , Calldepth |- SymInteger (num $ length (view frames vm))
     -- the following environment variables are always concrete in hevm right now
    , Origin    |- SymInteger (num $ addressWord160 (view (tx . origin) vm))
    , Difficulty |- SymInteger (num $ view (block . difficulty) vm)
    , Chainid |- SymInteger (num $ view (env . chainId) vm)
    , Timestamp |- let S _ w = view (block . timestamp) vm
                   in SymInteger (sFromIntegral w)
    , This |- SymInteger (num $ addressWord160 (view (state . contract) vm))
    , Nonce |- let
                 maybeContract = view (env . contracts . at (view (state . contract) vm)) vm
               in SymInteger $ maybe 1 (num . view nonce) maybeContract

      -- and this one does not even give a reasonable result
--    , Blockhash |- error "blockhash not available in hevm right now"
    ]
  where
    (|-) a b = (nameFromEnv c1 method a, b)

-- | Locate the variables refered to in the act-spec in the vm
locateStorage :: Ctx -> SolcJson -> Map Id Addr -> Method -> (VM,VM) -> Rewrite -> (Id, (SActType, SActType))
locateStorage ctx@(Ctx c _ _ _ _) solcjson contractMap method (pre, post) item =
  let item' = locFromRewrite item
      addr = get (contractFromRewrite item) contractMap

      Just preContract = view (env . contracts . at addr) pre
      Just postContract = view (env . contracts . at addr) post

      Just (S _ preValue) = readStorage (view storage preContract) (calculateSlot ctx solcjson item')
      Just (S _ postValue) = readStorage (view storage postContract) (calculateSlot ctx solcjson item')

      name :: StorageLocation -> Id
      name (Loc _ i) = nameFromItem c method i

  in (name item',  (SymInteger (sFromIntegral preValue), SymInteger (sFromIntegral postValue)))

calculateSlot :: Ctx -> SolcJson -> StorageLocation -> SymWord
calculateSlot ctx solcjson loc =
  -- TODO: packing with offset
  let
    source = get (pack (contractFromLoc loc)) solcjson
    layout = fromMaybe (error "internal error: no storageLayout") $ _storageLayout source
    StorageItem _ _ slot = get (pack (idFromLocation loc)) layout
    slotword = sFromIntegral (literal (fromIntegral slot :: Integer))
    indexers = symExp ctx <$> ixsFromLocation loc
  in var (idFromLocation loc) $
     if null indexers
     then slotword
     else foldl (\a b -> keccak' . SymbolicBuffer $ toBytes a <> toSymBytes b) slotword indexers


locateCalldata :: Behaviour -> [Decl] -> Buffer -> Decl -> (Id, SActType)
locateCalldata b decls calldata' d@(Decl typ name) =
  if any (\(Decl typ' _) -> abiKind typ' /= Static) decls
  then error "dynamic calldata args currently unsupported"
  else (nameFromDecl (Annotated._contract b) (_name b) d, val)

  where
    -- every argument is static right now; length is always 32
    offset = w256 . fromIntegral $ 4 + 32 * fromMaybe
          (error ("internal error: could not find calldata var: "
              ++ name ++ " in interface declaration"))
          (elemIndex d decls)

    val = case fromAbiType typ of
      -- all integers are 32 bytes
      AInteger -> let S _ w = readSWord offset calldata'
                 in SymInteger $ sFromIntegral w
      -- interpret all nonzero values as boolean true
      ABoolean -> SymBool $ readSWord offset calldata' ./= 0
      _ -> error "TODO: support bytes"

-- | Embed an SActType as a list of symbolic bytes
toSymBytes :: SActType -> [SWord 8]
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
  do args <- concat <$> replicateM leng (mkabiArg typ)
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

--- Symbolic Expression Generation ---

data Ctx = Ctx ContractName Method Args HEVM.Storage HEVM.Env
  deriving (Show)

data SActType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes (SBV String)
  deriving (Show)

type ContractName = Id
type Method = Id
type Args = Map Id SActType
type Storage = Map Id (SActType, SActType)
type Env = Map Id SActType

symExp :: Ctx -> TypedExp -> SActType
symExp ctx (TExp t e) = case t of
  SInteger -> SymInteger $ symExpInt   ctx e
  SBoolean -> SymBool    $ symExpBool  ctx e
  SByteStr -> SymBytes   $ symExpBytes ctx e
  SContract -> error "calls not supported"

symExpBool :: Ctx -> Exp ABoolean -> SBV Bool
symExpBool ctx@(Ctx c m args store _) e = case e of
  And _ a b   -> symExpBool ctx a .&& symExpBool ctx b
  Or _ a b    -> symExpBool ctx a .|| symExpBool ctx b
  Impl _ a b  -> symExpBool ctx a .=> symExpBool ctx b
  LT _ a b    -> symExpInt ctx a .< symExpInt ctx b
  LEQ _ a b   -> symExpInt ctx a .<= symExpInt ctx b
  GT _ a b    -> symExpInt ctx a .> symExpInt ctx b
  GEQ _ a b   -> symExpInt ctx a .>= symExpInt ctx b
  NEq p t a b   -> sNot (symExpBool ctx (Eq p t a b))
  Neg _ a     -> sNot (symExpBool ctx a)
  LitBool _ a -> literal a
  Var _ _ a   -> get (nameFromArg c m a) (catBools args)
  TEntry _ t a -> get (nameFromItem c m a) (catBools $ timeStore t store)
  ITE _ x y z -> ite (symExpBool ctx x) (symExpBool ctx y) (symExpBool ctx z)
  Eq _ SInteger a b -> symExpInt  ctx a .== symExpInt  ctx b
  Eq _ SBoolean a b -> symExpBool  ctx a .== symExpBool  ctx b
  Eq _ SByteStr a b -> symExpBytes  ctx a .== symExpBytes  ctx b
  Eq _ SContract _ _ -> error "calls not supported"
  Create _ _ _ _ -> error "calls not supported"

symExpInt :: Ctx -> Exp AInteger -> SBV Integer
symExpInt ctx@(Ctx c m args store environment) e = case e of
  Add _ a b   -> symExpInt ctx a + symExpInt ctx b
  Sub _ a b   -> symExpInt ctx a - symExpInt ctx b
  Mul _ a b   -> symExpInt ctx a * symExpInt ctx b
  Div _ a b   -> symExpInt ctx a `sDiv` symExpInt ctx b
  Mod _ a b   -> symExpInt ctx a `sMod` symExpInt ctx b
  Exp _ a b   -> symExpInt ctx a .^ symExpInt ctx b
  LitInt _ a  -> literal a
  IntMin _ a  -> literal $ intmin a
  IntMax _ a  -> literal $ intmax a
  UIntMin _ a -> literal $ uintmin a
  UIntMax _ a -> literal $ uintmax a
  Var _ _ a   -> get (nameFromArg c m a) (catInts args)
  TEntry _ t a -> get (nameFromItem c m a) (catInts $ timeStore t store)
  IntEnv _ a -> get (nameFromEnv c m a) (catInts environment)
  ITE _ x y z -> ite (symExpBool ctx x) (symExpInt ctx y) (symExpInt ctx z)
  Create _ _ _ _ -> error "calls not supported"

symExpBytes :: Ctx -> Exp AByteStr -> SBV String
symExpBytes ctx@(Ctx c m args store environment) e = case e of
  Cat _ a b -> symExpBytes ctx a .++ symExpBytes ctx b
  Var _ _ a -> get (nameFromArg c m a) (catBytes args)
  ByStr _ a -> literal a
  ByLit _ a -> literal $ toString a
  TEntry _ t a -> get (nameFromItem c m a) (catBytes $ timeStore t store)
  Slice _ a x y -> subStr (symExpBytes ctx a) (symExpInt ctx x) (symExpInt ctx y)
  ByEnv _ a -> get (nameFromEnv c m a) (catBytes environment)
  ITE _ x y z -> ite (symExpBool ctx x) (symExpBytes ctx y) (symExpBytes ctx z)
  Create _ _ _ _ -> error "calls not supported"

timeStore :: When -> HEVM.Storage -> Map Id SActType
timeStore Pre  s = fst <$> s
timeStore Post s = snd <$> s

-- *** SMT Variable Names *** --

nameFromStorageRef :: ContractName -> Method -> StorageRef -> Id
nameFromStorageRef c method (SVar _ _ name) = c @@ method @@ name
nameFromStorageRef c method (SMapping _ e ixs) = nameFromStorageRef c method e <> showIxs
  where
    showIxs = intercalate "-" $ "" : fmap (nameFromTypedExp c method) ixs
nameFromStorageRef _ _ (SField _ _ _ _) = error "contracts not supported"

nameFromItem :: ContractName -> Method -> TStorageItem a -> Id
nameFromItem c method (Item _ _ e) = nameFromStorageRef c method e

nameFromTypedExp :: ContractName -> Method -> TypedExp -> Id
nameFromTypedExp c method (TExp _ e) = nameFromExp c method e

nameFromExp :: ContractName -> Method -> Exp a -> Id
nameFromExp c m e = case e of
  Add _ a b   -> nameFromExp c m a <> "+" <> nameFromExp c m b
  Sub _ a b   -> nameFromExp c m a <> "-" <> nameFromExp c m b
  Mul _ a b   -> nameFromExp c m a <> "*" <> nameFromExp c m b
  Div _ a b   -> nameFromExp c m a <> "/" <> nameFromExp c m b
  Mod _ a b   -> nameFromExp c m a <> "%" <> nameFromExp c m b
  Exp _ a b   -> nameFromExp c m a <> "^" <> nameFromExp c m b
  LitInt _ a  -> show a
  IntMin _ a  -> show $ intmin a
  IntMax _ a  -> show $ intmax a
  UIntMin _ a -> show $ uintmin a
  UIntMax _ a -> show $ uintmax a
  IntEnv _ a -> nameFromEnv c m a

  And _ a b   -> nameFromExp c m a <> "&&" <> nameFromExp c m b
  Or _ a b    -> nameFromExp c m a <> "|" <> nameFromExp c m b
  Impl _ a b  -> nameFromExp c m a <> "=>" <> nameFromExp c m b
  LT _ a b    -> nameFromExp c m a <> "<" <> nameFromExp c m b
  LEQ _ a b   -> nameFromExp c m a <> "<=" <> nameFromExp c m b
  GT _ a b    -> nameFromExp c m a <> ">" <> nameFromExp c m b
  GEQ _ a b   -> nameFromExp c m a <> ">=" <> nameFromExp c m b
  Neg _ a     -> "~" <> nameFromExp c m a
  LitBool _ a -> show a
  Eq _ _ a b    -> nameFromExp c m a <> "=="  <> nameFromExp c m b
  NEq _ _ a b   -> nameFromExp c m a <> "=/=" <> nameFromExp c m b
  Cat _ a b -> nameFromExp c m a <> "++" <> nameFromExp c m b
  ByStr _ a -> show a
  ByLit _ a -> show a
  Slice _ a x y -> nameFromExp c m a <> "[" <> show x <> ":" <> show y <> "]"
  ByEnv _ a -> nameFromEnv c m a

  Var _ _ a -> nameFromArg c m a
  TEntry _ _ a -> nameFromItem c m a
  ITE _ x y z -> "if-" <> nameFromExp c m x <> "-then-" <> nameFromExp c m y <> "-else-" <> nameFromExp c m z

  Create _ _ _ _ -> error "calls not supported"

nameFromDecl :: ContractName -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: ContractName -> Method -> Id -> Id
nameFromArg c method name = c @@ method @@ name

nameFromEnv :: ContractName -> Method -> EthEnv -> Id
nameFromEnv c method e = c @@ method @@ (prettyEnv e)

(@@) :: (Show a, Show b) => a -> b -> Id
x @@ y = show x <> "_" <> show y

-- *** Utils *** --


get :: (Show a, Ord a, Show b) => a -> Map a b -> b
get name vars = fromMaybe (error (show name <> " not found in " <> show vars)) $ Map.lookup name vars

catInts :: Map Id SActType -> Map Id (SBV Integer)
catInts m = Map.fromList [(name, i) | (name, SymInteger i) <- Map.toList m]

catBools :: Map Id SActType -> Map Id (SBV Bool)
catBools m = Map.fromList [(name, i) | (name, SymBool i) <- Map.toList m]

catBytes :: Map Id SActType -> Map Id (SBV String)
catBytes m = Map.fromList [(name, i) | (name, SymBytes i) <- Map.toList m]

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = fmap concat (mapM f xs)
