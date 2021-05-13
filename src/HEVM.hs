{-# Language RecordWildCards #-}
{-# Language TypeApplications #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}

module HEVM where

import Prelude hiding (lookup)
import Syntax hiding (Post)
import RefinedAst hiding (S)
import Extract

import Data.ByteString (ByteString)
import Data.ByteString.UTF8 (toString)
import Data.Text (Text, pack, splitOn)
import Data.Maybe
import Data.Either
import Data.List hiding (lookup)
import qualified Data.List.NonEmpty as NonEmpty (toList)
import Data.Map hiding (drop, null, findIndex, splitAt, foldl, foldr, filter)
import qualified Data.Map as Map
import Control.Monad.State.Strict (execState)
import Data.SBV.Control
import Data.SBV
import Data.SBV.String ((.++), subStr)
import Control.Lens hiding (pre, (.>))
import Control.Monad
import qualified Data.Vector as Vec
import Data.Type.Equality
import Data.Typeable
import Data.Tree

import Print

import EVM hiding (Query)
import EVM.VMTest
import EVM.Solidity hiding (Method)
import EVM.ABI
import EVM.Concrete
import EVM.SymExec
import EVM.Symbolic
import EVM.Types (SymWord(..), Buffer(..), Addr(..), toSizzle, litBytes, num, var)
import EVM.Types (w256, addressWord160, saddressWord160, SAddr(..))

type SolcJson = Map Text SolcContract

proveBehaviour :: SolcJson -> Behaviour -> Symbolic (Either (Tree BranchInfo) VM)
proveBehaviour sources behaviour = do
  preVm <- initialVm sources' behaviour contractMap
  query $ do
    res <- verify preVm Nothing Nothing (Just postC)
    case res of
      Right _ -> do
        showCounterexample preVm Nothing
        return $ Right preVm :: Query (Either (Tree BranchInfo) VM)
      Left tree -> return $ Left tree :: Query (Either (Tree BranchInfo) VM)

   where
     -- todo: deal with ambiguities in contract name
     sources' = mapKeys (last . splitOn ":") sources

     -- create new addresses for each contract involved
     -- in the future addresses could be passed through the cli
     contractMap = fromList $ zipWith
       (\id' i -> (id', createAddress (Addr 0) i)) (nub $ (RefinedAst._contract behaviour):(contractsInvolved behaviour)) [0..]

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
checkPostStorage ctx (Behaviour _ _ _ _ _ _ updates _) pre post contractMap solcjson =
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
                 insertions = rights $ filter (\a -> addr == get (getContractId (getLoc a)) contractMap) updates
                 slot update' = let S _ w = calculateSlot ctx solcjson (mkLoc update')
                               in w
                 insertUpdate :: SArray (WordN 256) (WordN 256) -> StorageUpdate -> SArray (WordN 256) (WordN 256)
                 insertUpdate store u@(IntUpdate _ e) = writeArray store (slot u) $ sFromIntegral $ symExpInt ctx Pre e
                 insertUpdate store u@(BoolUpdate _ e) = writeArray store (slot u) $ ite (symExpBool ctx Pre e) 1 0
                 insertUpdate _ _ = error "bytes unsupported"
               in post' .== foldl insertUpdate pre' insertions
              _ -> sFalse


-- assumes preconditions as well
mkPostCondition :: VM -> VM -> SolcJson -> Behaviour -> Map Id Addr -> (Ctx, VMResult) -> SBool
mkPostCondition preVm postVm solcjson
  b@(Behaviour _ mode _ _ preCond postCond _ returns)
  contractMap
  (ctx, vmResult) =
    let storageConstraints = checkPostStorage ctx b preVm postVm contractMap solcjson
        preCond' = symExpBool ctx Pre (mconcat preCond)
        postCond' = symExpBool ctx Pre (mconcat postCond)
        (actual, reverted) = case vmResult of
          VMSuccess (ConcreteBuffer msg) -> (litBytes msg, sFalse)
          VMSuccess (SymbolicBuffer msg) -> (msg, sFalse)
          VMFailure (Revert _) -> ([], sTrue)
          _ -> ([], sFalse)
        expected = maybe [] (toSymBytes . symExp ctx Pre) returns

    in preCond' .=>
       (postCond' .&&
        storageConstraints .&&
        case mode of
          Pass -> sNot reverted .&& (actual .== expected)
          Fail -> reverted
          OOG -> error "internal error: OOG mode not supported yet")

-- | Locate the variables refered to in the act-spec in the vm
mkVmContext :: SolcJson -> Behaviour -> Map Id Addr -> VM -> VM -> (Ctx, VMResult)
mkVmContext solcjson b@(Behaviour method _ c1 (Interface _ decls) _ _ updates _) contractMap pre post =
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
makeVmEnv (Behaviour method _ c1 _ _ _ _ _) vm =
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
locateStorage :: Ctx -> SolcJson -> Map Id Addr -> Method -> (VM,VM) -> Either StorageLocation StorageUpdate -> (Id, (SMType, SMType))
locateStorage ctx solcjson contractMap method (pre, post) item =
  let item' = getLoc item
      contractId = getContractId item'
      addr = get contractId contractMap

      Just preContract = view (env . contracts . at addr) pre
      Just postContract = view (env . contracts . at addr) post


      Just (S _ preValue) = readStorage (view storage preContract) (calculateSlot ctx solcjson item')
      Just (S _ postValue) = readStorage (view storage postContract) (calculateSlot ctx solcjson item')

      name :: StorageLocation -> Id
      name (IntLoc i) = nameFromItem method i
      name (BoolLoc i) = nameFromItem method i
      name (BytesLoc i) = nameFromItem method i

  in (name item',  (SymInteger (sFromIntegral preValue), SymInteger (sFromIntegral postValue)))

calculateSlot :: Ctx -> SolcJson -> StorageLocation -> SymWord
calculateSlot ctx solcjson loc =
  -- TODO: packing with offset
  let
    source = get (pack (getContractId loc)) solcjson
    layout = fromMaybe (error "internal error: no storageLayout") $ _storageLayout source
    StorageItem _ _ slot = get (pack (getContainerId loc)) layout
    slotword = sFromIntegral (literal (fromIntegral slot :: Integer))
    indexers = symExp ctx Pre <$> getContainerIxs loc
  in var (getContainerId loc) $
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
        (elemIndex d decls))

    val = case metaType typ of
      -- all integers are 32 bytes
      Integer -> let S _ w = readSWord offset calldata'
                 in SymInteger $ sFromIntegral w
      -- interpret all nonzero values as boolean true
      Boolean -> SymBool $ readSWord offset calldata' ./= 0
      _ -> error "TODO: support bytes"

-- | Embed an SMType as a list of symbolic bytes
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

data SMType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes (SBV String)
  deriving (Show)

type ContractName = Id
type Method = Id
type Args = Map Id SMType
type Storage = Map Id (SMType, SMType)
type Env = Map Id SMType
data When = Pre | Post

symExp :: Ctx -> When -> ReturnExp -> SMType
symExp ctx whn ret = case ret of
  ExpInt e -> SymInteger $ symExpInt ctx whn e
  ExpBool e -> SymBool $ symExpBool ctx whn e
  ExpBytes e -> SymBytes $ symExpBytes ctx whn e

symExpBool :: Ctx -> When -> Exp Bool -> SBV Bool
symExpBool ctx@(Ctx c m args store _) w e = case e of
  And a b   -> symExpBool ctx w a .&& symExpBool ctx w b
  Or a b    -> symExpBool ctx w a .|| symExpBool ctx w b
  Impl a b  -> symExpBool ctx w a .=> symExpBool ctx w b
  LE a b    -> symExpInt ctx w a .< symExpInt ctx w b
  LEQ a b   -> symExpInt ctx w a .<= symExpInt ctx w b
  GE a b    -> symExpInt ctx w a .> symExpInt ctx w b
  GEQ a b   -> symExpInt ctx w a .>= symExpInt ctx w b
  NEq a b   -> sNot (symExpBool ctx w (Eq a b))
  Neg a     -> sNot (symExpBool ctx w a)
  LitBool a -> literal a
  BoolVar a -> get (nameFromArg c m a) (catBools args)
  TEntry a  -> get (nameFromItem m a) (catBools store')
  ITE x y z -> ite (symExpBool ctx w x) (symExpBool ctx w y) (symExpBool ctx w z)
  Eq (a :: Exp t) (b :: Exp t) -> case eqT @t @Integer of
    Just Refl -> symExpInt ctx w a .== symExpInt ctx w b
    Nothing -> case eqT @t @Bool of
      Just Refl -> symExpBool ctx w a .== symExpBool ctx w b
      Nothing -> case eqT @t @ByteString of
        Just Refl -> symExpBytes ctx w a .== symExpBytes ctx w b
        Nothing -> error "Internal Error: invalid expression type"
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store

symExpInt :: Ctx -> When -> Exp Integer -> SBV Integer
symExpInt ctx@(Ctx c m args store environment) w e = case e of
  Add a b   -> symExpInt ctx w a + symExpInt ctx w b
  Sub a b   -> symExpInt ctx w a - symExpInt ctx w b
  Mul a b   -> symExpInt ctx w a * symExpInt ctx w b
  Div a b   -> symExpInt ctx w a `sDiv` symExpInt ctx w b
  Mod a b   -> symExpInt ctx w a `sMod` symExpInt ctx w b
  Exp a b   -> symExpInt ctx w a .^ symExpInt ctx w b
  LitInt a  -> literal a
  IntMin a  -> literal $ intmin a
  IntMax a  -> literal $ intmax a
  UIntMin a -> literal $ uintmin a
  UIntMax a -> literal $ uintmax a
  IntVar a  -> get (nameFromArg c m a) (catInts args)
  TEntry a  -> get (nameFromItem m a) (catInts store')
  IntEnv a -> get (nameFromEnv c m a) (catInts environment)
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE x y z -> ite (symExpBool ctx w x) (symExpInt ctx w y) (symExpInt ctx w z)
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store

symExpBytes :: Ctx -> When -> Exp ByteString -> SBV String
symExpBytes ctx@(Ctx c m args store environment) w e = case e of
  Cat a b -> symExpBytes ctx w a .++ symExpBytes ctx w b
  ByVar a  -> get (nameFromArg c m a) (catBytes args)
  ByStr a -> literal a
  ByLit a -> literal $ toString a
  TEntry a  -> get (nameFromItem m a) (catBytes store')
  Slice a x y -> subStr (symExpBytes ctx w a) (symExpInt ctx w x) (symExpInt ctx w y)
  ByEnv a -> get (nameFromEnv c m a) (catBytes environment)
  ITE x y z -> ite (symExpBool ctx w x) (symExpBytes ctx w y) (symExpBytes ctx w z)
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store


-- *** SMT Variable Names *** --


nameFromItem :: Method -> TStorageItem a -> Id
nameFromItem method item = case item of
  DirectInt c name -> c @@ method @@ name
  DirectBool c name -> c @@ method @@ name
  DirectBytes c name -> c @@ method @@ name
  MappedInt c name ixs -> c @@ method @@ name >< showIxs c ixs
  MappedBool c name ixs -> c @@ method @@ name >< showIxs c ixs
  MappedBytes c name ixs -> c @@ method @@ name >< showIxs c ixs
  where
    x >< y = x <> "-" <> y
    showIxs c ixs = intercalate "-" (NonEmpty.toList $ nameFromExp c method <$> ixs)

nameFromExp :: ContractName -> Method -> ReturnExp -> Id
nameFromExp c method e = case e of
  ExpInt e' -> nameFromExpInt c method e'
  ExpBool e' -> nameFromExpBool c method e'
  ExpBytes e' -> nameFromExpBytes c method e'

nameFromExpInt :: ContractName -> Method -> Exp Integer -> Id
nameFromExpInt c m e = case e of
  Add a b   -> nameFromExpInt c m a <> "+" <> nameFromExpInt c m b
  Sub a b   -> nameFromExpInt c m a <> "-" <> nameFromExpInt c m b
  Mul a b   -> nameFromExpInt c m a <> "*" <> nameFromExpInt c m b
  Div a b   -> nameFromExpInt c m a <> "/" <> nameFromExpInt c m b
  Mod a b   -> nameFromExpInt c m a <> "%" <> nameFromExpInt c m b
  Exp a b   -> nameFromExpInt c m a <> "^" <> nameFromExpInt c m b
  LitInt a  -> show a
  IntMin a  -> show $ intmin a
  IntMax a  -> show $ intmax a
  UIntMin a -> show $ uintmin a
  UIntMax a -> show $ uintmax a
  IntVar a  -> a
  TEntry a  -> nameFromItem m a
  IntEnv a -> nameFromEnv c m a
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE x y z -> "if-" <> nameFromExpBool c m x <> "-then-" <> nameFromExpInt c m y <> "-else-" <> nameFromExpInt c m z

nameFromExpBool :: ContractName -> Method -> Exp Bool -> Id
nameFromExpBool c m e = case e of
  And a b   -> nameFromExpBool c m a <> "&&" <> nameFromExpBool c m b
  Or a b    -> nameFromExpBool c m a <> "|" <> nameFromExpBool c m b
  Impl a b  -> nameFromExpBool c m a <> "=>" <> nameFromExpBool c m b
  LE a b    -> nameFromExpInt c m a <> "<" <> nameFromExpInt c m b
  LEQ a b   -> nameFromExpInt c m a <> "<=" <> nameFromExpInt c m b
  GE a b    -> nameFromExpInt c m a <> ">" <> nameFromExpInt c m b
  GEQ a b   -> nameFromExpInt c m a <> ">=" <> nameFromExpInt c m b
  Neg a     -> "~" <> nameFromExpBool c m a
  LitBool a -> show a
  BoolVar a -> nameFromArg c m a
  TEntry a  -> nameFromItem m a
  ITE x y z -> "if-" <> nameFromExpBool c m x <> "-then-" <> nameFromExpBool c m y <> "-else-" <> nameFromExpBool c m z
  Eq (a :: Exp t) (b :: Exp t) -> case eqT @t @Integer of
    Just Refl -> nameFromExpInt c m a <> "==" <> nameFromExpInt c m b
    Nothing -> case eqT @t @Bool of
      Just Refl -> nameFromExpBool c m a <> "==" <> nameFromExpBool c m b
      Nothing -> case eqT @t @ByteString of
        Just Refl -> nameFromExpBytes c m a <> "==" <> nameFromExpBytes c m b
        Nothing -> error "Internal Error: invalid expression type"
  NEq (a :: Exp t) (b :: Exp t) -> case eqT @t @Integer of
    Just Refl -> nameFromExpInt c m a <> "=/=" <> nameFromExpInt c m b
    Nothing -> case eqT @t @Bool of
      Just Refl -> nameFromExpBool c m a <> "=/=" <> nameFromExpBool c m b
      Nothing -> case eqT @t @ByteString of
        Just Refl -> nameFromExpBytes c m a <> "=/=" <> nameFromExpBytes c m b
        Nothing -> error "Internal Error: invalid expression type"

nameFromExpBytes :: ContractName -> Method -> Exp ByteString -> Id
nameFromExpBytes c m e = case e of
  Cat a b -> nameFromExpBytes c m a <> "++" <> nameFromExpBytes c m b
  ByVar a  -> nameFromArg c m a
  ByStr a -> show a
  ByLit a -> show a
  TEntry a  -> nameFromItem m a
  Slice a x y -> nameFromExpBytes c m a <> "[" <> show x <> ":" <> show y <> "]"
  ByEnv a -> nameFromEnv c m a
  ITE x y z -> "if-" <> nameFromExpBool c m x <> "-then-" <> nameFromExpBytes c m y <> "-else-" <> nameFromExpBytes c m z

nameFromDecl :: ContractName -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: ContractName -> Method -> Id -> Id
nameFromArg c method name = c @@ method @@ name

nameFromEnv :: ContractName -> Method -> EthEnv -> Id
nameFromEnv c method e = c @@ method @@ (prettyEnv e)

(@@) :: Id -> Id -> Id
x @@ y = x <> "_" <> y


-- *** Utils *** --


get :: (Show a, Ord a, Show b) => a -> Map a b -> b
get name vars = fromMaybe (error (show name <> " not found in " <> show vars)) $ Map.lookup name vars

catInts :: Map Id SMType -> Map Id (SBV Integer)
catInts m = Map.fromList [(name, i) | (name, SymInteger i) <- Map.toList m]

catBools :: Map Id SMType -> Map Id (SBV Bool)
catBools m = Map.fromList [(name, i) | (name, SymBool i) <- Map.toList m]

catBytes :: Map Id SMType -> Map Id (SBV String)
catBytes m = Map.fromList [(name, i) | (name, SymBytes i) <- Map.toList m]

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM concat (mapM f xs)
