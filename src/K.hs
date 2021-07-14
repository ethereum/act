{-# LANGUAGE RecordWildCards #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}

module K where

import RefinedAst
import Extract
import ErrM
import Control.Applicative ((<|>))
import Data.Functor (($>))
import Data.Text (Text, pack, unpack)
import Data.Typeable
import Data.List hiding (group)
import Data.Maybe
import Data.ByteString hiding (group, pack, unpack, intercalate, filter, foldr, concat, head, tail, null)
import qualified Data.Text as Text
import Parse
import EVM.Types hiding (Whiff(..))

import EVM.Solidity (SolcContract(..), StorageItem(..), SlotType(..))
import Data.Map.Strict (Map) -- abandon in favor of [(a,b)]?
import qualified Data.Map.Strict as Map -- abandon in favor of [(a,b)]?

-- Transforms a RefinedSyntax.Behaviour
-- to a k spec.

cell :: String -> String -> String
cell key value = "<" <> key <> "> " <> value <> " </" <> key <> "> \n"

(|-) :: String -> String -> String
(|-) = cell

infix 7 |-

kStatus :: Mode -> String
kStatus Pass = "EVMC_SUCCESS"
kStatus Fail = "FAILURE:EndStatusCode"
kStatus OOG = error "TODO: handle OOG specs"

type KSpec = String

getContractName :: Text -> String
getContractName = unpack . Text.concat . Data.List.tail . Text.splitOn ":"

data KOptions =
  KOptions {
    gasExprs :: Map Id String,
    storage :: Maybe String,
    extractbin :: Bool
    }

makekSpec :: Map Text SolcContract -> KOptions -> Behaviour -> Err (String, String)
makekSpec sources _ behaviour =
  let this = _contract behaviour
      names = Map.fromList $ fmap (\(a, b) -> (getContractName a, b)) (Map.toList sources)
      hasLayout = Map.foldr ((&&) . isJust . _storageLayout) True sources
  in
    if hasLayout then do
      thisSource <- errMessage
            (nowhere, "err: " <> show this <> "Bytecode not found\nSources available: " <> show (Map.keys sources))
            (Map.lookup this names)

      return $ mkTerm thisSource names behaviour

    else Bad (nowhere, "No storagelayout found")

kCalldata :: Interface -> String
kCalldata (Interface a args) =
  "#abiCallData("
  <> show a <> ", "
  <> if null args then ".IntList"
     else intercalate ", " (fmap (\(Decl typ varname) -> "#" <> show typ <> "(" <> kVar varname <> ")") args)
  <> ")"

kStorageName :: TStorageItem Timed a -> When -> String
kStorageName item t = kVar (idFromItem item) <> "-" <> show t
                   <> intercalate "_" ("" : fmap kTypedExpr (ixsFromItem item))

kVar :: Id -> String
kVar a = (unpack . Text.toUpper . pack $ [head a]) <> tail a

kAbiEncode :: Maybe (TypedExp Timed) -> String
kAbiEncode Nothing = ".ByteArray"
kAbiEncode (Just (ExpInt a)) = "#enc(#uint256" <> kExpr a <> ")"
kAbiEncode (Just (ExpBool _)) = ".ByteArray"
kAbiEncode (Just (ExpBytes _)) = ".ByteArray"

kTypedExpr :: TypedExp Timed -> String
kTypedExpr (ExpInt a) = kExpr a
kTypedExpr (ExpBool a) = kExpr a
kTypedExpr (ExpBytes _) = error "TODO: add support for ExpBytes to kExpr"

kExpr :: Exp Timed a -> String
-- integers
kExpr (Add a b) = "(" <> kExpr a <> " +Int " <> kExpr b <> ")"
kExpr (Sub a b) = "(" <> kExpr a <> " -Int " <> kExpr b <> ")"
kExpr (Mul a b) = "(" <> kExpr a <> " *Int " <> kExpr b <> ")"
kExpr (Div a b) = "(" <> kExpr a <> " /Int " <> kExpr b <> ")"
kExpr (Mod a b) = "(" <> kExpr a <> " modInt " <> kExpr b <> ")"
kExpr (Exp a b) = "(" <> kExpr a <> " ^Int " <> kExpr b <> ")"
kExpr (LitInt a) = show a
kExpr (IntMin a) = kExpr $ LitInt $ negate $ 2 ^ (a - 1)
kExpr (IntMax a) = kExpr $ LitInt $ 2 ^ (a - 1) - 1
kExpr (UIntMin _) = kExpr $ LitInt 0
kExpr (UIntMax a) = kExpr $ LitInt $ 2 ^ a - 1
kExpr (IntVar a) = kVar a
kExpr (IntEnv a) = show a

-- booleans
kExpr (And a b) = "(" <> kExpr a <> " andBool\n " <> kExpr b <> ")"
kExpr (Or a b) = "(" <> kExpr a <> " orBool " <> kExpr b <> ")"
kExpr (Impl a b) = "(" <> kExpr a <> " impliesBool " <> kExpr b <> ")"
kExpr (Neg a) = "notBool (" <> kExpr a <> ")"
kExpr (LE a b) = "(" <> kExpr a <> " <Int " <> kExpr b <> ")"
kExpr (LEQ a b) = "(" <> kExpr a <> " <=Int " <> kExpr b <> ")"
kExpr (GE a b) = "(" <> kExpr a <> " >Int " <> kExpr b <> ")"
kExpr (GEQ a b) = "(" <> kExpr a <> " >=Int " <> kExpr b <> ")"
kExpr (LitBool a) = show a
kExpr (BoolVar a) = kVar a
kExpr (NEq a b) = "notBool (" <> kExpr (Eq a b) <> ")"
kExpr (Eq (a :: Exp t a) (b :: Exp t a)) = fromMaybe (error "Internal Error: invalid expression type") $
  let eqK typ = "(" <> kExpr a <> " ==" <> typ <> " " <> kExpr b <> ")"
   in eqT @a @Integer    $> eqK "Int"
  <|> eqT @a @Bool       $> eqK "Bool"
  <|> eqT @a @ByteString $> eqK "K" -- TODO: Is ==K correct?

-- bytestrings
kExpr (ByVar name) = kVar name
kExpr (ByStr str) = show str
kExpr (ByLit bs) = show bs
kExpr (TEntry item t) = kStorageName item t
kExpr v = error ("Internal error: TODO kExpr of " <> show v)
--kExpr (Cat a b) =
--kExpr (Slice a start end) =
--kExpr (ByEnv env) =

fst' :: (a, b, c) -> a
fst' (x, _, _) = x

snd' :: (a, b, c) -> b
snd' (_, y, _) = y

trd' :: (a, b, c) -> c
trd' (_, _, z) = z

kStorageEntry :: Map Text StorageItem -> Rewrite -> (String, (Int, String, String))
kStorageEntry storageLayout update =
  let (loc, offset) = kSlot update $
        fromMaybe
         (error "Internal error: storageVar not found, please report this error")
         (Map.lookup (pack (idFromRewrite update)) storageLayout)
  in case update of
       Rewrite (IntUpdate a b) -> (loc, (offset, kStorageName (a `as` Pre) Pre, kExpr $ b `as` Pre))
       Rewrite (BoolUpdate a b) -> (loc, (offset, kStorageName (a `as` Pre) Pre, kExpr $ b `as` Pre))
       Rewrite (BytesUpdate a b) -> (loc, (offset, kStorageName (a `as` Pre) Pre, kExpr $ b `as` Pre))
       Constant (IntLoc a) -> (loc, (offset, kStorageName (a `as` Pre) Pre, kStorageName (a `as` Pre) Pre))
       v -> error $ "Internal error: TODO kStorageEntry: " <> show v

--packs entries packed in one slot
normalize :: Bool -> [(String, (Int, String, String))] -> String
normalize pass entries = foldr (\a acc -> case a of
                                 (loc, [(_, pre, post)]) ->
                                   loc <> " |-> (" <> pre
                                       <> " => " <> (if pass then post else "_") <> ")\n"
                                       <> acc
                                 (loc, items) -> let (offsets, pres, posts) = unzip3 items
                                                 in loc <> " |-> ( #packWords("
                                                        <> showSList (fmap show offsets) <> ", "
                                                        <> showSList pres <> ") "
                                                        <> " => " <> (if pass
                                                                     then "#packWords("
                                                                       <> showSList (fmap show offsets)
                                                                       <> ", " <> showSList posts <> ")"
                                                                     else "_")
                                                        <> ")\n"
                                                        <> acc
                               )
                               "\n" (group entries)
  where group :: [(String, (Int, String, String))] -> [(String, [(Int, String, String)])]
        group a = Map.toList (foldr (\(slot, (offset, pre, post)) acc -> Map.insertWith (<>) slot [(offset, pre, post)] acc) mempty a)
        showSList :: [String] -> String
        showSList = unwords

kSlot :: Rewrite -> StorageItem -> (String, Int)
kSlot update StorageItem{..} = case _type of
  (StorageValue _) -> (show _slot, _offset)
  (StorageMapping _ _) -> if null (ixsFromRewrite update) 
    then error $ "internal error: kSlot. Please report: " <> show update
    else ( "#hashedLocation(\"Solidity\", "
             <> show _slot <> ", " <> unwords (kTypedExpr . setTyped Pre <$> ixsFromRewrite update) <> ")"
         , _offset )

kAccount :: Bool -> Id -> SolcContract -> [Rewrite] -> String
kAccount pass name source updates =
  "account" |- ("\n"
   <> "acctID" |- kVar name
   <> "balance" |- (kVar name <> "_balance") -- needs to be constrained to uint256
   <> "code" |- (kByteStack (_runtimeCode source))
   <> "storage" |- (normalize pass ( fmap (kStorageEntry (fromJust (_storageLayout source))) updates) <> "\n.Map")
   <> "origStorage" |- ".Map" -- need to be generalized once "kStorageEntry" is implemented
   <> "nonce" |- "_"
      )

kByteStack :: ByteString -> String
kByteStack bs = "#parseByteStack(\"" <> show (ByteStringS bs) <> "\")"

defaultConditions :: String -> String
defaultConditions acct_id =
    "#rangeAddress(" <> acct_id <> ")\n" <>
    "andBool " <> acct_id <> " =/=Int 0\n" <>
    "andBool " <> acct_id <> " >Int 9\n" <>
    "andBool #rangeAddress( " <> show Caller <> ")\n" <>
    "andBool #rangeAddress( " <> show Origin <> ")\n" <>
    "andBool #rangeUInt(256, " <> show  Timestamp <> ")\n" <>
    -- "andBool #rangeUInt(256, ECREC_BAL)" <>
    -- "andBool #rangeUInt(256, SHA256_BAL)" <>
    -- "andBool #rangeUInt(256, RIP160_BAL)" <>
    -- "andBool #rangeUInt(256, ID_BAL)" <>
    -- "andBool #rangeUInt(256, MODEXP_BAL)" <>
    -- "andBool #rangeUInt(256, ECADD_BAL)" <>
    -- "andBool #rangeUInt(256, ECMUL_BAL)" <>
    -- "andBool #rangeUInt(256, ECPAIRING_BAL)" <>
    "andBool " <> show Calldepth <> " <=Int 1024\n" <>
    "andBool #rangeUInt(256, " <> show Callvalue <> ")\n" <>
    "andBool #rangeUInt(256, " <> show Chainid <>  " )\n"

indent :: Int -> String -> String
indent n text = unlines $ ((Data.List.replicate n ' ') <>) <$> (lines text)

mkTerm :: SolcContract -> Map Id SolcContract -> Behaviour -> (String, String)
mkTerm this accounts Behaviour{..} = (name, term)
  where code = _runtimeCode this
        pass = _mode == Pass
        repl '_' = '.'
        repl  c  = c
        name = _contract <> "_" <> _name <> "_" <> show _mode
        term =  "rule [" <> (fmap repl name) <> "]:\n"
             <> "k" |- "#execute => #halt"
             <> "exit-code" |- "1"
             <> "mode" |- "NORMAL"
             <> "schedule" |- "ISTANBUL"
             <> "evm" |- indent 2 ("\n"
                  <> "output" |- (if pass then kAbiEncode _returns else ".ByteArray")
                  <> "statusCode" |- kStatus _mode
                  <> "callStack" |- "CallStack"
                  <> "interimStates" |- "_"
                  <> "touchedAccounts" |- "_"
                  <> "callState" |- indent 2 ("\n"
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
                     <> "pc" |- "0 => _"
                     <> "gas" |- "300000 => _" -- can be generalized in the future
                     <> "memoryUsed" |- "0 => _"
                     <> "callGas" |- "_ => _"
                     <> "static" |- "false" -- TODO: generalize
                     <> "callDepth" |- (show Calldepth)
                     )
                  <> "substate" |- indent 2 ("\n"
                      <> "selfDestruct" |- "_ => _"
                      <> "log" |- "_ => _" --TODO: spec logs?
                      <> "refund" |- "_ => _"
                      )
                  <> "gasPrice" |- "_" --could be environment var
                  <> "origin" |- show Origin
                  <> "blockhashes" |- "_"
                  <> "block" |- indent 2 ("\n"
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
                <> "network" |- indent 2 ("\n"
                  <> "activeAccounts" |- "_"
                  <> "accounts" |- indent 2 ("\n" <> (unpack $
                    Text.unlines (flip fmap (contractFromRewrite <$> _stateUpdates) $ \a ->
                      pack $
                        kAccount pass a
                          (fromMaybe
                            (error $ show a ++ " not found in accounts: " ++ show accounts)
                            $ Map.lookup a accounts
                          )
                          (filter (\u -> contractFromRewrite u == a) _stateUpdates)
                          )))
                  <> "txOrder" |- "_"
                  <> "txPending" |- "_"
                  <> "messages" |- "_"
                  )
               <> "\nrequires "
               <> defaultConditions (kVar _contract) <> "\n andBool\n"
               <> kExpr (mconcat _preconditions `as` Pre)
               <> "\nensures "
               <> kExpr (mconcat _postconditions)
