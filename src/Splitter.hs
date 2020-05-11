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

import EVM.Solidity (SolcContract(..), StorageItem(..), SlotType(..))
import Control.Monad
import Data.Map.Strict (Map) -- abandon in favor of [(a,b)]?
import qualified Data.Map.Strict as Map -- abandon in favor of [(a,b)]?

-- Transforms a RefinedSyntax.Behaviour
-- to a k spec.

cell :: String -> String -> String
cell key value = "<" <> key <> "> " <> value <> " </" <> key <> "> \n"

(|-) = cell

infix 7 |-

kStatus :: Mode -> String
kStatus Pass = "EVMC_SUCCESS"
kStatus Fail = "FAILURE:EndStatusCode"

type KSpec = String


defaultConditions :: String
defaultConditions = ""

getContractName :: Text -> String
getContractName = unpack . Text.concat . Data.List.tail . Text.splitOn ":"


data KOptions =
  KOptions {
    gasExprs :: Map Id String,
    storage :: Maybe String,
    extractbin :: Bool
    }
  

makekSpec :: Map Text SolcContract -> KOptions -> Behaviour -> Err (String, String)
makekSpec sources kOpts behaviour =
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

getId :: Either StorageLocation StorageUpdate -> Id
getId (Right (IntUpdate a _)) = getId' a
getId (Right (BoolUpdate a _)) = getId' a
getId (Right (BytesUpdate a _)) = getId' a
getId (Left (IntLoc a)) = getId' a
getId (Left (BoolLoc a)) = getId' a
getId (Left (BytesLoc a)) = getId' a

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
kExpr (ExpBool a) = kExprBool a
-- kExpr (ExpBytes a)


kExprInt :: Exp Int -> String
kExprInt (Add a b) = "(" <> kExprInt a <> " +Int " <> kExprInt b <> ")"
kExprInt (Sub a b) = "(" <> kExprInt a <> " -Int " <> kExprInt b <> ")"
kExprInt (Mul a b) = "(" <> kExprInt a <> " *Int " <> kExprInt b <> ")"
kExprInt (Div a b) = "(" <> kExprInt a <> " /Int " <> kExprInt b <> ")"
kExprInt (Mod a b) = "(" <> kExprInt a <> " modInt " <> kExprInt b <> ")"
kExprInt (Exp a b) = "(" <> kExprInt a <> " ^Int " <> kExprInt b <> ")"
kExprInt (LitInt a) = show a
kExprInt (IntVar a) = kVar a
kExprInt (IntEnv a) = show a
kExprInt (TEntry a) = kstorageName a
kExprInt v = error ("Internal error: TODO kExprInt of " <> show v)


kExprBool :: Exp Bool -> String
kExprBool (And a b) = "(" <> kExprBool a <> " andBool " <> kExprBool b <> ")"
kExprBool (Or a b) = "(" <> kExprBool a <> " orBool " <> kExprBool b <> ")"
kExprBool (Impl a b) = "(" <> kExprBool a <> " impliesBool " <> kExprBool b <> ")"
kExprBool (Eq a b) = "(" <> kExprInt a <> " ==Int " <> kExprInt b <> ")"

kExprBool (NEq a b) = "(" <> kExprInt a <> " =/=Int " <> kExprInt b <> ")"
kExprBool (Neg a) = "notBool (" <> kExprBool a <> ")"
kExprBool (LE a b) = "(" <> kExprInt a <> " <Int " <> kExprInt b <> ")"
kExprBool (LEQ a b) = "(" <> kExprInt a <> " <=Int " <> kExprInt b <> ")"
kExprBool (GE a b) = "(" <> kExprInt a <> " >Int " <> kExprInt b <> ")"
kExprBool (GEQ a b) = "(" <> kExprInt a <> " >=Int " <> kExprInt b <> ")"
kExprBool (LitBool a) = show a
kExprBool (BoolVar a) = kVar a
kExprBool v = error ("Internal error: TODO kExprBool of " <> show v)

fst' (x, _, _) = x
snd' (_, y, _) = y
trd' (_, _, z) = z

kStorageEntry :: Map Text StorageItem -> Either StorageLocation StorageUpdate -> (String, (Int, String, String))
kStorageEntry storageLayout update =
  let (loc, offset) = kSlot update $
        fromMaybe
         (error "Internal error: storageVar not found, please report this error")
         (Map.lookup (pack (getId update)) storageLayout)
  in case update of
       Right (IntUpdate a b) -> (loc, (offset, kstorageName a, kExprInt b))
       Left (IntLoc a) -> (loc, (offset, kstorageName a, kstorageName a))
       v -> error $ "Internal error: TODO kStorageEntry: " <> show v
--  BoolUpdate (TStorageItem Bool) c -> 
--  BytesUpdate (TStorageItem ByteString) d ->  (Exp ByteString)


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

kSlot :: Either StorageLocation StorageUpdate -> StorageItem -> (String, Int)
kSlot update StorageItem{..} = case _type of
  (StorageValue _) -> (show _slot, _offset)
  (StorageMapping _ _) -> case update of
      Right (IntUpdate (MappedInt _ ixs) _) -> ("#hashedLocation(\"Solidity\", " <> show _slot <> " ," <> intercalate " " (fmap show (NonEmpty.toList ixs)) <> ")", _offset)
      Right (BoolUpdate (MappedBool _ ixs) _) -> ("#hashedLocation(\"Solidity\", " <> show _slot <> " ," <> intercalate " " (fmap show (NonEmpty.toList ixs)) <> ")", _offset)
      Right (BytesUpdate (MappedBytes _ ixs) _) -> ("#hashedLocation(\"Solidity\", " <> show _slot <> " ," <> intercalate " " (fmap show (NonEmpty.toList ixs)) <> ")", _offset)
      _ -> error "internal error: kSlot. Please report"


kAccount :: Id -> SolcContract -> [Either StorageLocation StorageUpdate] -> String
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
               <> "\nrequires "
               <> defaultConditions
               <> kExprBool _preconditions
