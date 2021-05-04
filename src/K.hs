{-# LANGUAGE RecordWildCards #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeOperators #-}

module K where

import Syntax
import RefinedAst
import Extract
import ErrM
import Control.Applicative ((<|>))
import Data.Char (toUpper)
import Data.Functor (($>))
import Data.Text (Text, pack, unpack)
import Data.Typeable
import Data.List hiding (group)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.ByteString hiding (group, pack, unpack, intercalate, filter, foldr, concat, head, tail)
import qualified Data.Text as Text
import Parse
import EVM.Types
import Utils
import Data.Comp.Multi.Ops ((:*:)(..), ffst, fsnd)
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Show (showHF')

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
kStorageName (MappedInt _ name ixs) = kVar name <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kReturnExp ixs)
kStorageName (MappedBool _ name ixs) = kVar name <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kReturnExp ixs)
kStorageName (MappedBytes _ name ixs) = kVar name <> "_" <> intercalate "_" (NonEmpty.toList $ fmap kReturnExp ixs)

kVar :: Id -> String
kVar (a:as) = toUpper a : as
kVar _      = error "kVar: empty variable name"

kAbiEncode :: Maybe ReturnExp -> String
kAbiEncode Nothing = ".ByteArray"
kAbiEncode (Just (ExpInt a)) = "#enc(#uint256" <> kExpr a <> ")"
kAbiEncode (Just (ExpBool _)) = ".ByteArray"
kAbiEncode (Just (ExpBytes _)) = ".ByteArray"

kReturnExp :: ReturnExp -> String
kReturnExp (ExpInt a) = kExpr a
kReturnExp (ExpBool a) = kExpr a
kReturnExp (ExpBytes _) = error "TODO: add support for ExpBytes to kReturnExp"

kExpr :: Exp a -> String
kExpr = paraK \case

  -- integers
  Add a b -> infix2 "+Int"   <$*> fsnd a <$*> fsnd b
  Sub a b -> infix2 "-Int"   <$*> fsnd a <$*> fsnd b
  Mul a b -> infix2 "*Int"   <$*> fsnd a <$*> fsnd b
  Div a b -> infix2 "/Int"   <$*> fsnd a <$*> fsnd b
  Mod a b -> infix2 "modInt" <$*> fsnd a <$*> fsnd b
  Exp a b -> infix2 "^Int"   <$*> fsnd a <$*> fsnd b
  LitInt   a -> show a

  -- TODO these cases are somewhat unsatisfactory. 
  -- *manual* recursion!? 😱
  IntMin   a -> kExpr . iLitInt . negate $ 2 ^ (a - 1)
  IntMax   a -> kExpr . iLitInt $ 2 ^ (a - 1) - 1
  UIntMin  _ -> kExpr . iLitInt $ 0
  UIntMax  a -> kExpr . iLitInt $ 2 ^ a - 1
  IntVar   a -> kVar a
  IntEnv   a -> show a
  IntStore a -> kStorageName a

  -- booleans
  And  a b -> infix2  "andBool\n"   <$*> fsnd a <$*> fsnd b
  Or   a b -> infix2  "orBool"      <$*> fsnd a <$*> fsnd b
  Impl a b -> infix2  "impliesBool" <$*> fsnd a <$*> fsnd b
  Neg  a   -> prefix1 "notBool"     <$*> fsnd a
  LE   a b -> infix2  "<Int"        <$*> fsnd a <$*> fsnd b
  LEQ  a b -> infix2  "<=Int"       <$*> fsnd a <$*> fsnd b
  GE   a b -> infix2  ">Int"        <$*> fsnd a <$*> fsnd b
  GEQ  a b -> infix2  ">=Int"       <$*> fsnd a <$*> fsnd b
  LitBool a -> show a
  BoolVar a -> kVar a
  NEq a b -> kExpr . iNeg $ iEq (ffst a) (ffst b) -- TODO 😱
  Eq (_:*:(a :: K String t)) (_:*:(b :: K String t)) ->
    let
      eqExpr typ = infix2 ("==" <> typ) <$*> a <$*> b
     in
      fromMaybe (error "Internal Error: invalid expression type")
      $   eqT @t @Integer    $> eqExpr "Int"
      <|> eqT @t @Bool       $> eqExpr "Bool"
      <|> eqT @t @ByteString $> eqExpr "K"

  -- bytestrings
  ByVar name -> kVar name
  ByStr str -> show str
  ByLit bs -> show bs
  ByStore item -> kStorageName item

  -- error
  v -> error ("Internal error: TODO kExpr' of " <> showHF' (hfmap fsnd v))
  where
    prefix1 op x   = op <> parens x
    infix2  op a b = parens . apply $ [a,op,b]
    apply = intercalate " "
    parens s = "(" <> s <> ")"

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
       Right (IntUpdate a b) -> (loc, (offset, kStorageName a, kExpr b))
       Right (BoolUpdate a b) -> (loc, (offset, kStorageName a, kExpr b))
       Right (BytesUpdate a b) -> (loc, (offset, kStorageName a, kExpr b))
       Left (IntLoc a) -> (loc, (offset, kStorageName a, kStorageName a))
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

kSlot :: Either StorageLocation StorageUpdate -> StorageItem -> (String, Int)
kSlot update StorageItem{..} = case _type of
  (StorageValue _) -> (show _slot, _offset)
  (StorageMapping _ _) -> case update of
      Right (IntUpdate (MappedInt _ _ ixs) _) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kReturnExp (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Left (IntLoc (MappedInt _ _ ixs)) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kReturnExp (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Right (BoolUpdate (MappedBool _ _ ixs) _) ->
        (
          "#hashedLocation(\"Solidity\", "
              <> show _slot <> ", " <> unwords (fmap kReturnExp (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Left (BoolLoc (MappedBool _ _ ixs)) ->
        (
          "#hashedLocation(\"Solidity\", "
              <> show _slot <> ", " <> unwords (fmap kReturnExp (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Right (BytesUpdate (MappedBytes _ _ ixs) _) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kReturnExp (NonEmpty.toList ixs)) <> ")"
        , _offset
        )
      Left (BytesLoc (MappedBytes _ _ ixs)) ->
        (
          "#hashedLocation(\"Solidity\", "
            <> show _slot <> ", " <> unwords (fmap kReturnExp (NonEmpty.toList ixs)) <> ")"
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
               <> kExpr (mconcat _preconditions)
               <> "\nensures "
               <> kExpr (mconcat _postconditions)
