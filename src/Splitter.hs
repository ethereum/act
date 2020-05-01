{-# LANGUAGE RecordWildCards #-}
{-# Language QuasiQuotes #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
module Splitter where

import Syntax
import RefinedAst
import ErrM
import Data.Text hiding (foldr, intercalate)
import Data.List
import Data.Maybe
import Data.ByteString hiding (pack, unpack, intercalate)
import qualified Data.Text as Text
import Parse
import Data.Bifunctor
import EVM (VM, ContractCode)
import EVM.Types
import EVM.Symbolic (verify, Precondition, Postcondition)
--import EVM.Solidity (AbiType)
import EVM.Solidity (SolcContract(..))
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
getContractName = unpack . Data.Text.concat . Data.List.tail . Text.splitOn ":"

makekSpec :: Map Text SolcContract -> Behaviour -> Err (String, String)
makekSpec sources behaviour =
  let this = _contract behaviour
      names = Map.fromList $ fmap (\(a, b) -> (getContractName a, b)) (Map.toList sources)
  in
    do accounts <- forM (_contracts behaviour)
         (\c ->
            errMessage
            (nowhere, "err: " <> show c <> "Bytecode not found\nSources available: " <> show (Map.keys sources))
            (Map.lookup c names))
       thisSource <- errMessage
            (nowhere, "err: " <> show this <> "Bytecode not found\nSources available: " <> show (Map.keys sources))
            (Map.lookup this names)

       return $ mkTerm thisSource names behaviour

kCalldata :: Interface -> String
kCalldata (Interface a b) =
  "#abiCallData("
  <> show a <> ", "
  <> intercalate ", " (fmap (\(Decl typ varname) -> "#" <> show typ <> "(" <> kVar varname <> ")") b)
  <> ")"

kVar = unpack .toUpper . pack

kAbiEncode :: Maybe ReturnExp -> String
kAbiEncode Nothing = ".ByteArray"
kAbiEncode (Just (ExpInt a)) = "#enc(#uint256" <> kExprInt a <> ")"
kAbiEncode (Just (ExpBool a)) = ".ByteArray"
kAbiEncode (Just (ExpBytes a)) = ".ByteArray"

kExprInt :: Exp T_Int -> String
kExprInt (Add a b) = "(" <> kExprInt a <> " +Int " <> kExprInt b <> ")"
kExprInt (LitInt a) = show a
kExprInt (IntVar a) = kVar a


-- kStorageLoc :: StorageLayout -> [StorageUpdate] -> String
-- kStorageLoc = error "TODO"
data StorageLayout = Soon | To | Be

kStorageEntry :: StorageLayout -> StorageUpdate -> String
kStorageEntry = error "TODO"

_storageLayout :: SolcContract -> StorageLayout
_storageLayout = error "should be in hevm"

kAccount :: Id -> SolcContract -> [StorageUpdate] -> String
kAccount name source updates =
  "account" |- ("\n"
   <> "acctID" |- kVar name
   <> "balance" |- (kVar name <> "_balance")
   <> "code" |- (kByteStack (_runtimeCode source))
   <> "storage" |- (mconcat ( fmap (kStorageEntry (_storageLayout source)) updates) <> "\n.Map")
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
