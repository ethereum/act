{-# LANGUAGE RecordWildCards #-}
{-# Language QuasiQuotes #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
module Splitter where

import Syntax
import RefinedAst
import ErrM
import Data.Text (Text, pack, unpack)
import Data.List
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.ByteString hiding (pack, unpack, intercalate, foldr, concat)
import qualified Data.Text as Text
import Parse
import Data.Bifunctor
import EVM (VM, ContractCode)
import EVM.Types
import EVM.Symbolic (verify, Precondition, Postcondition)
--import EVM.Solidity (AbiType)
import EVM.Solidity (SolcContract(..), StorageItem(..), SlotType(..))
import Control.Monad
import Data.Map.Strict (Map) -- abandon in favor of [(a,b)]?
import qualified Data.Map.Strict as Map -- abandon in favor of [(a,b)]?

-- data Implementation = Implementation
--   {_contractBinaries :: Map Id Code,
--    _storageLayout :: Map Id Layout
--   }

-- type Code = (String, String)

-- data Layout = Layout {
--   slot :: Int,
--   offset :: Int,
--   label :: Id,
--   encoding :: Encoding,
--   length :: Int
--   }
-- data Encoding = Inplace | Mapping | DynamicArray | Bytes

-- data KSpec = KSpec {
--   k :: KTerm,
--   exitCode :: Int,
--   mode :: Mode,
--   schedule :: Fork
--   program :: ByteString,
--   jumpDests :: ByteString,
--   callData :: Bytes,
--   output :: Bytes,
--   statusCode :: StatusCode,
--   kreturn :: String
--  accounts :: Map Contract
-- deriving (Ord, Eq)

-- -- instance Show KSpec whereR
-- --   show KSpec { .. }  = error "TODO"

-- data Mode = Normal
--   deriving (Eq, Show)

-- data Fork = Istanbul
--   deriving (Eq, Show)

-- data KTerm = Execute | Halt
--   deriving (Eq, Show)

-- -- instance Show KTerm where
-- --   show Execute = "execute"
-- --   show Halt = "halt"

-- data StatusCode
--   = EVMC_SUCCESS
--   | EVMC_REVERT
--   | EVMC_OOG
--   deriving (Show, Eq)


cell :: String -> String -> String
cell key value = "<" <> key <> "> " <> value <> " </" <> key <> "> \n"

(|-) = cell

infix 7 |-

kStatus :: Mode -> String
kStatus Pass = "EVMC_SUCCESS"
kStatus Fail = "FAILURE:EndStatusCode"

type KSpec = String

getContractName :: Text -> String
getContractName = unpack . Text.concat . Data.List.tail . Text.splitOn ":"

makekSpec :: Map Text SolcContract -> Behaviour -> Err (String, String)
makekSpec sources behaviour =
  let this = _contract behaviour
      names = Map.fromList $ fmap (\(a, b) -> (getContractName a, b)) (Map.toList sources)
      hasLayout = Map.foldr ((&&) . isJust . _storageLayout) True sources
  in
    if hasLayout then do
      accounts <- forM (_contracts behaviour)
         (\c ->
            errMessage
            (nowhere, "err: " <> show c <> "Bytecode not found\nSources available: " <> show (Map.keys sources))
            (Map.lookup c names))
      thisSource <- errMessage
            (nowhere, "err: " <> show this <> "Bytecode not found\nSources available: " <> show (Map.keys sources))
            (Map.lookup this names)

      return $ mkTerm thisSource names behaviour
    else Bad (nowhere, "No storagelayout found")

kCalldata :: Interface -> String
kCalldata (Interface a b) =
  "#abiCallData("
  <> show a <> ", "
  <> (case b of
       [] -> ".IntList"
       args -> 
         intercalate ", " (fmap (\(Decl typ varname) -> "#" <> show typ <> "(" <> kVar varname <> ")") args))
  <> ")"

getId :: StorageUpdate -> Id
getId (IntUpdate a _) = getId' a
getId (BoolUpdate a _) = getId' a
getId (BytesUpdate a _) = getId' a

getId' :: TStorageItem a -> Id
getId' (DirectInt id) = id
getId' (DirectBool id) = id
getId' (DirectBytes id) = id
getId' (MappedInt id _) = id
getId' (MappedBool id _) = id
getId' (MappedBytes id _) = id


kstorageName :: TStorageItem a -> String
kstorageName (DirectInt id)    = kVar id
kstorageName (DirectBool id)   = kVar id
kstorageName (DirectBytes id)  = kVar id
kstorageName (MappedInt id ixs) = kVar id <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kExpr ixs)
kstorageName (MappedBool id ixs) = kVar id <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kExpr ixs)
kstorageName (MappedBytes id ixs) = kVar id <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kExpr ixs)

kVar = unpack . Text.toUpper . pack

kAbiEncode :: Maybe ReturnExp -> String
kAbiEncode Nothing = ".ByteArray"
kAbiEncode (Just (ExpInt a)) = "#enc(#uint256" <> kExprInt a <> ")"
kAbiEncode (Just (ExpBool a)) = ".ByteArray"
kAbiEncode (Just (ExpBytes a)) = ".ByteArray"


kExpr :: ReturnExp -> String
kExpr (ExpInt a) = kExprInt a
-- kExpr (ExpBool a) = kExpr
-- kExpr (ExpBytes a)


kExprInt :: Exp T_Int -> String
kExprInt (Add a b) = "(" <> kExprInt a <> " +Int " <> kExprInt b <> ")"
kExprInt (LitInt a) = show a
kExprInt (IntVar a) = kVar a
kExprInt (TEntry a) = kstorageName a
kExprInt v = error ("Internal error: TODO kExprInt of " <> show v)

fst' (x, _, _) = x
snd' (_, y, _) = y
trd' (_, _, z) = z




kStorageEntry :: Map Text StorageItem -> StorageUpdate -> (String, (Int, String, String))
kStorageEntry storageLayout update =
  let (loc, offset) = kSlot $
        fromMaybe
         (error "Internal error: storageVar not found, please report this error")
         (Map.lookup (pack (getId update)) storageLayout)
  in case update of
       IntUpdate a b -> (loc, (offset, kstorageName a <> "_PRE", kExprInt b))
       v -> error $ "Internal error: TODO kStorageEntry: " <> show v
--  BoolUpdate (TStorageItem T_Bool) c -> 
--  BytesUpdate (TStorageItem T_Bytes) d ->  (Exp T_Bytes)


--packs entries packed in one slot
normalize :: [(String, (Int, String, String))] -> String
normalize entries = foldr (\a acc -> case a of
                              (loc, [(_, pre, post)]) -> loc <> " |-> " <> pre <> " => " <> post <> "\n" <> acc
                              (loc, items) -> let (offsets, pres, posts) = unzip3 items
                                              in loc <> " |-> #packWords(" <> showSList (fmap show offsets) <> ", "
                                                     <> showSList pres <> ") "
                                                     <> " => #packWords(" <> showSList (fmap show offsets) <> ", "
                                                     <> showSList posts <> ")\n" <> acc)
                                 "\n"
                      (group entries)
  where group :: [(String, (Int, String, String))] -> [(String, [(Int, String, String)])]
        group a = Map.toList (foldr (\(slot, (offset, pre, post)) acc -> Map.insertWith (<>) slot [(offset, pre, post)] acc) mempty a)
        showSList :: [String] -> String
        showSList = intercalate " "

kSlot :: StorageItem -> (String, Int)
kSlot StorageItem{..} = case _type of
  (StorageValue _) -> (show _slot, _offset)
  (StorageMapping _ _) -> error "TODO"--(show _slot, offset)


kAccount :: Id -> SolcContract -> [StorageUpdate] -> String
kAccount name source updates =
  "account" |- ("\n"
   <> "acctID" |- kVar name
   <> "balance" |- (kVar name <> "_balance")
   <> "code" |- (kByteStack (_runtimeCode source))
   <> "storage" |- (normalize ( fmap (kStorageEntry (fromJust (_storageLayout source))) updates) <> "\n.Map")
   <> "origStorage" |- ".Map" -- need to be generalized once "kStorageEntry" is implemented
   <> "nonce" |- "_"
      )

kByteStack :: ByteString -> String
kByteStack bs = "#parseByteStack(\"" <> show (ByteStringS bs) <> "\")"


mkTerm :: SolcContract -> Map Id SolcContract -> Behaviour -> (String, String)
mkTerm this accounts behaviour@Behaviour{..} = (name, term)
  where code = if _creation then _creationCode this
               else _runtimeCode this
        repl '_' = '.'
        repl  c  = c
        name = _contract <> "_" <> _name <> "_" <> show _mode
        term =  "rule [" <> (fmap repl name) <> "]:\n"
             <> "k" |- "#execute"
             <> "exit-code" |- "1"
             <> "mode" |- "NORMAL"
             <> "schedule" |- "ISTANBUL"
             <> "evm" |- ("\n"
                  <> "output" |- kAbiEncode _returns
                  <> "statusCode" |- kStatus _mode
                  <> "callStack" |- "CallStack"
                  <> "interimStates" |- "_"
                  <> "touchedAccounts" |- "_"
                  <> "callState" |- ("\n"
                     <> "program" |- kByteStack code
                     <> "jumpDests" |- ("#computeValidJumpDests(" <> kByteStack code <> ")")
                     <> "id" |- kVar _contract
                     <> "caller" |- (show Caller)
                     <> "callData" |- kCalldata _interface
                     <> "callValue" |- (show Callvalue)
                        -- the following are set to the values they have
                        -- at the beginning of a CALL. They can take a
                        -- more general value in "internal" specs.
                     <> "wordStack" |- ".WordStack => _"
                     <> "localMem"  |- ".Map => _"
                     <> "pc" |- "0"
                     <> "gas" |- "300000 => _" -- can be generalized in the future
                     <> "memoryUsed" |- "0 => _"
                     <> "callGas" |- "_ => _"
                     <> "static" |- "false" -- TODO: generalize
                     <> "callDepth" |- (show Calldepth)
                     )
                  <> "substate" |- ("\n"
                      <> "selfDestruct" |- "_"
                      <> "log" |- "_" --TODO: spec logs?
                      <> "refund" |- "_"
                      )
                  <> "gasPrice" |- "_" --could be environment var
                  <> "origin" |- show Origin
                  <> "blockhashes" |- "_"
                  <> "block" |- ("\n"
                     <> "previousHash" |- "_"
                     <> "ommersHash" |- "_"
                     <> "coinbase" |- (show Coinbase)
                     <> "stateRoot" |- "_"
                     <> "transactionsRoot" |- "_"
                     <> "receiptsRoot" |- "_"
                     <> "logsBloom" |- "_"
                     <> "difficulty" |- (show Difficulty)
                     <> "number" |- (show Blocknumber)
                     <> "gasLimit" |- "_"
                     <> "gasUsed" |- "_"
                     <> "timestamp" |- (show Timestamp)
                     <> "extraData" |- "_"
                     <> "mixHash" |- "_"
                     <> "blockNonce" |- "_"
                     <> "ommerBlockHeaders" |- "_"
                     )
                )
                <> "network" |- ("\n"
                  <> "activeAccounts" |- "_"
                  <> "accounts" |- ("\n" <> unpack (Text.intercalate "\n" (fmap (\a -> pack $ kAccount a (fromJust $ Map.lookup a accounts) (fromJust $ Map.lookup a _stateUpdates)) _contracts)))
                  <> "txOrder" |- "_"
                  <> "txPending" |- "_"
                  <> "messages" |- "_"
                  )
