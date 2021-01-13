{-# LANGUAGE RecordWildCards #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}

module K where

import Syntax
import RefinedAst
import Extract
import ErrM
import Data.Text (Text, pack, unpack)
import Data.Type.Equality
import Data.Typeable
import Data.List hiding (group)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.ByteString hiding (group, pack, unpack, intercalate, filter, foldr, concat, head, tail)
import qualified Data.Text as Text
import Parse
import EVM.Types

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
kCalldata (Interface a b) =
  "#abiCallData("
  <> show a <> ", "
  <> (case b of
       [] -> ".IntList"
       args ->
         intercalate ", " (fmap (\(Decl typ varname) -> "#" <> show typ <> "(" <> kVar varname <> ")") args))
  <> ")"

kStorageName :: TStorageItem a -> String
kStorageName (DirectInt _ name)    = kVar name
kStorageName (DirectBool _ name)   = kVar name
kStorageName (DirectBytes _ name)  = kVar name
kStorageName (MappedInt _ name ixs) = kVar name <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kExpr ixs)
kStorageName (MappedBool _ name ixs) = kVar name <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kExpr ixs)
kStorageName (MappedBytes _ name ixs) = kVar name <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kExpr ixs)

kVar :: Id -> String
kVar a = (unpack . Text.toUpper . pack $ [head a]) <> (tail a)

kAbiEncode :: Maybe ReturnExp -> String
kAbiEncode Nothing = ".ByteArray"
kAbiEncode (Just (ExpInt a)) = "#enc(#uint256" <> kExprInt a <> ")"
kAbiEncode (Just (ExpBool _)) = ".ByteArray"
kAbiEncode (Just (ExpBytes _)) = ".ByteArray"

kExpr :: ReturnExp -> String
kExpr (ExpInt a) = kExprInt a
kExpr (ExpBool a) = kExprBool a
kExpr (ExpBytes _) = error "TODO: add support for ExpBytes to kExpr"

kExprInt :: Exp Integer -> String
kExprInt (Add a b) = "(" <> kExprInt a <> " +Int " <> kExprInt b <> ")"
kExprInt (Sub a b) = "(" <> kExprInt a <> " -Int " <> kExprInt b <> ")"
kExprInt (Mul a b) = "(" <> kExprInt a <> " *Int " <> kExprInt b <> ")"
kExprInt (Div a b) = "(" <> kExprInt a <> " /Int " <> kExprInt b <> ")"
kExprInt (Mod a b) = "(" <> kExprInt a <> " modInt " <> kExprInt b <> ")"
kExprInt (Exp a b) = "(" <> kExprInt a <> " ^Int " <> kExprInt b <> ")"
kExprInt (LitInt a) = show a
kExprInt (IntMin a) = kExprInt $ LitInt $ negate $ 2 ^ (a - 1)
kExprInt (IntMax a) = kExprInt $ LitInt $ 2 ^ (a - 1) - 1
kExprInt (UIntMin _) = kExprInt $ LitInt 0
kExprInt (UIntMax a) = kExprInt $ LitInt $ 2 ^ a - 1
kExprInt (IntVar a) = kVar a
kExprInt (IntEnv a) = show a
kExprInt (TEntry a) = kStorageName a
kExprInt v = error ("Internal error: TODO kExprInt of " <> show v)


kExprBool :: Exp Bool -> String
kExprBool (And a b) = "(" <> kExprBool a <> " andBool\n " <> kExprBool b <> ")"
kExprBool (Or a b) = "(" <> kExprBool a <> " orBool " <> kExprBool b <> ")"
kExprBool (Impl a b) = "(" <> kExprBool a <> " impliesBool " <> kExprBool b <> ")"
kExprBool (Neg a) = "notBool (" <> kExprBool a <> ")"
kExprBool (LE a b) = "(" <> kExprInt a <> " <Int " <> kExprInt b <> ")"
kExprBool (LEQ a b) = "(" <> kExprInt a <> " <=Int " <> kExprInt b <> ")"
kExprBool (GE a b) = "(" <> kExprInt a <> " >Int " <> kExprInt b <> ")"
kExprBool (GEQ a b) = "(" <> kExprInt a <> " >=Int " <> kExprInt b <> ")"
kExprBool (LitBool a) = show a
kExprBool (BoolVar a) = kVar a
kExprBool (NEq a b) = "notBool (" <> kExprBool (Eq a b) <> ")"
kExprBool (Eq (a :: Exp t) (b :: Exp t)) = case eqT @t @Integer of
  Just Refl -> "(" <> kExprInt a <> " ==Int " <> kExprInt b <> ")"
  Nothing -> case eqT @t @Bool of
    Just Refl -> "(" <> kExprBool a <> " ==Bool " <> kExprBool b <> ")"
    Nothing -> case eqT @t @ByteString of
      Just Refl -> "(" <> kExprBytes a <> " ==K " <> kExprBytes b <> ")" -- TODO: Is ==K correct?
      Nothing -> error "Internal Error: invalid expression type"
kExprBool v = error ("Internal error: TODO kExprBool of " <> show v)

kExprBytes :: Exp ByteString -> String
kExprBytes (ByVar name) = kVar name
kExprBytes (ByStr str) = show str
kExprBytes (ByLit bs) = show bs
kExprBytes (TEntry item) = kStorageName item
kExprBytes e = error $ "TODO: kExprBytes of " <> show e
--kExprBytes (Cat a b) =
--kExprBytes (Slice a start end) =
--kExprBytes (ByEnv env) =

fst' :: (a, b, c) -> a
fst' (x, _, _) = x

snd' :: (a, b, c) -> b
snd' (_, y, _) = y

trd' :: (a, b, c) -> c
trd' (_, _, z) = z

kStorageEntry :: Map Text StorageItem -> Either StorageLocation StorageUpdate -> (String, (Int, String, String))
kStorageEntry storageLayout update =
  let (loc, offset) = kSlot update $
        fromMaybe
         (error "Internal error: storageVar not found, please report this error")
         (Map.lookup (pack (getId update)) storageLayout)
  in case update of
       Right (IntUpdate a b) -> (loc, (offset, kStorageName a, kExprInt b))
       Right (BoolUpdate a b) -> (loc, (offset, kStorageName a, kExprBool b))
       Right (BytesUpdate a b) -> (loc, (offset, kStorageName a, kExprBytes b))
       Left (IntLoc a) -> (loc, (offset, kStorageName a, kStorageName a))
       v -> error $ "Internal error: TODO kStorageEntry: " <> show v
--  BoolUpdate (TStorageItem Bool) c ->
--  BytesUpdate (TStorageItem ByteString) d ->  (Exp ByteString)

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

kSlot :: Either StorageLocation StorageUpdate -> StorageItem -> (String, Int)
kSlot update StorageItem{..} = case _type of
  (StorageValue _) -> (show _slot, _offset)
  (StorageMapping _ _) -> case update of
      Right (IntUpdate (MappedInt _ _ ixs) _) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kExpr (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Left (IntLoc (MappedInt _ _ ixs)) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kExpr (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Right (BoolUpdate (MappedBool _ _ ixs) _) ->
        (
          "#hashedLocation(\"Solidity\", "
              <> show _slot <> ", " <> unwords (fmap kExpr (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Left (BoolLoc (MappedBool _ _ ixs)) ->
        (
          "#hashedLocation(\"Solidity\", "
              <> show _slot <> ", " <> unwords (fmap kExpr (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Right (BytesUpdate (MappedBytes _ _ ixs) _) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kExpr (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Left (BytesLoc (MappedBytes _ _ ixs)) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kExpr (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      s -> error $ "internal error: kSlot. Please report: " <> (show s)


kAccount :: Bool -> Id -> SolcContract -> [Either StorageLocation StorageUpdate] -> String
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
                    Text.intercalate "\n" (flip fmap (getContract <$> _stateUpdates) $ \a ->
                      pack $
                        kAccount pass a
                         (fromMaybe
                           (error $ show a ++ " not found in accounts: " ++ show accounts)
                           $ Map.lookup a accounts
                         )
                         (filter (\u -> getContract u == a) _stateUpdates)
                         )))
                  <> "txOrder" |- "_"
                  <> "txPending" |- "_"
                  <> "messages" |- "_"
                  )
               <> "\nrequires "
               <> defaultConditions (kVar _contract) <> "\n andBool\n"
               <> kExprBool (mconcat _preconditions)
               <> "\nensures "
               <> kExprBool (mconcat _postconditions)
