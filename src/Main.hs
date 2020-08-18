{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Data.List
import Data.Aeson hiding (Bool, Number)
import GHC.Generics
import System.Environment ( getArgs )
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr)
import Data.Text (Text, pack, unpack)
import EVM.ABI
import EVM.Solidity (SlotType(..))
import qualified EVM.Solidity as Solidity
import qualified Data.Text as Text
import Data.Map.Strict    (Map)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict      as Map -- abandon in favor of [(a,b)]?
import Data.Vector (fromList)

import qualified Data.ByteString.Lazy.Char8 as B
import Data.ByteString (ByteString)

import Control.Monad
import Control.Monad.Except
import Data.Functor.Identity

import Syntax
import Splitter
import ErrM
import Lex (lexer, AlexPosn(..))
import Parse
import Options.Generic
import RefinedAst

--command line options
data Command w
  = Parse             { file  :: w ::: String <?> "Path to file"}
  | Lex               { file  :: w ::: String <?> "Path to file"}
  | ParseAndTypeCheck { file  :: w ::: String <?> "Path to file"}

  | KaseSplit         { spec    :: w ::: String <?> "Path to spec"
                      , soljson :: w ::: String <?> "Path to .sol.json"
                      }

  | Type              { file  :: w ::: String <?> "Path to file"}

  | K                 { spec    :: w ::: String               <?> "Path to spec"
                      , soljson :: w ::: String               <?> "Path to .sol.json"
                      , gas     :: w ::: Maybe [(Id, String)] <?> "Gas usage per spec"
                      , storage    :: w ::: Maybe String    <?> "Path to storage definitions"
                      , extractbin :: w ::: Bool              <?> "Put EVM bytecode in separate file"
                      , out     :: w ::: Maybe String         <?> "output directory"
                      }
    deriving (Generic)

deriving instance ParseField [(Id, String)]

instance ParseRecord (Command Wrapped)
deriving instance Show (Command Unwrapped)

safeDrop :: Int -> [a] -> [a]
safeDrop 0 a = a
safeDrop p [] = []
safeDrop _ [a] = [a]
safeDrop n (_:xs) = safeDrop (n-1) xs

prettyErr :: String -> (Pn, String) -> IO ()
prettyErr contents pn@(AlexPn _ line col,msg) =
  if fst pn == nowhere then
    do hPutStrLn stderr "Internal error"
       hPutStrLn stderr msg
       exitFailure
  else
    do let cxt = safeDrop (line - 1) (lines contents)
       hPutStrLn stderr $ show line <> " | " <> head cxt
       hPutStrLn stderr $ unpack (Text.replicate (col + (length (show line <> " | ")) - 1) " " <> "^")
       hPutStrLn stderr $ msg
       exitFailure

main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      (Lex f) -> do contents <- readFile f
                    print $ lexer contents

      (Parse f) -> do contents <- readFile f
                      case parse $ lexer contents of
                        Bad e -> prettyErr contents e
                        Ok x -> print x

      (Type f) -> do contents <- readFile f
                     case parse (lexer contents) >>= typecheck of
                       Ok a  -> B.putStrLn $ encode a
                       Bad e -> prettyErr contents e

      (K spec soljson gas storage extractbin out) -> do
        specContents <- readFile spec
        solContents  <- readFile soljson
        let kOpts = KOptions (maybe mempty Map.fromList gas) storage extractbin
        errKSpecs <- pure $ do refinedSpecs  <- parse (lexer specContents) >>= typecheck
                               (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                                 $ Solidity.readJSON $ pack solContents
                               forM refinedSpecs (makekSpec sources kOpts)
        case errKSpecs of
             Bad e -> prettyErr specContents e
             Ok kSpecs -> do
               let printFile (filename, content) = case out of
                     Nothing -> putStrLn (filename <> ".k") >> putStrLn content
                     Just dir -> writeFile (dir <> "/" <> filename <> ".k") content
               forM_ kSpecs printFile






--       (TypeCheck f) -> do contents <- readFile f
--                           let act = read contents :: [RawBehaviour]
--                           case typecheck act of
--                             (Ok a)  -> B.putStrLn $ encode a
--                             (Bad s) -> error s

--       (KaseSplit specFile implFile) -> do specText <- readFile specFile
--                                           let spec = read specText :: [RawBehaviour]
--                                           case typecheck spec of
--                                             (Ok a)  -> do implText <- readFile implFile
--                                                           print "ok"
--                                             (Bad s) -> error s

typecheck :: [RawBehaviour] -> Err [Behaviour]
typecheck behvs = let store = lookupVars behvs in
                  do bs <- mapM (splitBehaviour store) behvs
                     return $ join bs

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Store
lookupVars ((Transition _ _ _ _ _ _):bs) = lookupVars bs
lookupVars ((Constructor _ contract _ _ (Creates assigns) _ _ _):bs) =
  Map.singleton contract (Map.fromList $ map fromAssign assigns)
  <> lookupVars bs -- TODO: deal with variable overriding
  where fromAssign (AssignVal (StorageVar typ var) _) = (var, typ)
        fromAssign (AssignMany (StorageVar typ var) _) = (var, typ)
        fromAssign (AssignStruct _ _) = error "TODO: assignstruct"
lookupVars [] = mempty


-- typing of eth env variables
defaultStore :: [(EthEnv, MType)]
defaultStore =
  [(Callvalue, Integer),
   (Caller, Integer),
   (Blockhash, ByteStr),
   (Blocknumber, Integer),
   (Difficulty, Integer),
   (Timestamp, Integer),
   (Gaslimit, Integer),
   (Coinbase, Integer),
   (Chainid, Integer),
   (Address, Integer),
   (Origin, Integer),
   (Nonce, Integer)
   --others TODO
  ]

type Store = Map Id (Map Id SlotType)

-- typing of vars: this contract storage, other contract scopes, calldata args
type Env = (Map Id SlotType, Store, Map Id MType)

andRaw :: [Expr] -> Expr
andRaw [x] = x
andRaw (x:xs) = EAnd nowhere x (andRaw xs)
andRaw [] = BoolLit True

-- checks a transition given a typing of its storage variables
splitBehaviour :: Store -> RawBehaviour -> Err [Behaviour]
splitBehaviour store (Transition name contract iface@(Interface _ decls) iffs' cases maybePost) = do
  -- constrain integer calldata variables (TODO: other types)
  let calldataBounds = getCallDataBounds decls
      storageBounds = snd $ getStorageBounds env
  iff <- checkIffs env (iffs' <> calldataBounds <> storageBounds)
  postcondition <- mapM (checkBool env) (fromMaybe [] maybePost)
  flatten iff postcondition [] cases
  where
    env = mkEnv contract store decls

    -- translate wildcards into negation of other cases
    normalize :: [Case Expr b] -> [Case Expr b]
    normalize =
      snd
        . mapAccumL
          ( \a b -> case b of
              Leaf pn WildExp p -> (a, Leaf pn (ENot nowhere (andRaw a)) p)
              Branch pn WildExp p -> (a, Branch pn (ENot nowhere (andRaw a)) p)
              e@(Leaf _ c _) -> (c : a, e)
              e@(Branch _ c _) -> (c : a, e)
          )
          []

    -- flatten case tree
    flatten :: [Exp Bool] -> [Exp Bool] -> [Exp Bool] -> Case Expr Post -> Err [Behaviour]
    flatten iff postc pathcond (Leaf _ cond post) = do
      c <- checkBool env cond
      (p, maybeReturn, contracts) <- checkPost env contract post
      return $ splitCase name False contract iface (c : pathcond) iff maybeReturn p postc contracts
    flatten iff postc pathcond (Branch _ cond cs) = do
      c <- checkBool env cond
      leaves <- mapM (flatten iff postc (c : pathcond)) (normalize cs)
      return $ join leaves

splitBehaviour store (Constructor name contract iface@(Interface _ decls) iffs creates@(Creates assigns) extStorage maybeEnsures maybeInvariants) = do
  let env = mkEnv contract store decls

  rawUpdates <- mapM (checkAssign env) assigns
  let stateUpdates = Map.fromList $ (\(id, upd) -> (id, Right <$> upd)) <$> rawUpdates

  let calldataBounds = getCallDataBounds decls
  iffs' <- checkIffs env (iffs <> calldataBounds)

  invariants <- mapM (checkBool env) $ fromMaybe [] maybeInvariants
  let storageBounds = fst $ getStorageBounds env
      postcs = storageBounds <> invariants

  return $ splitCase name True contract iface [] iffs' Nothing stateUpdates postcs [contract]

mkEnv :: Id -> Store -> [Decl]-> Env
mkEnv contract store decls = (fromMaybe mempty (Map.lookup contract store), store, abiVars)
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- split case into pass and fail case
splitCase :: String -> Bool -> String -> Interface -> [Exp Bool] -> [Exp Bool] -> Maybe ReturnExp
          -> Map String [Either StorageLocation StorageUpdate] -> [Exp Bool] -> [String] -> [Behaviour]
splitCase name creates contract iface ifs [] ret storage postcs contracts =
  [ Behaviour name Pass creates contract iface (mconcat ifs) (mconcat postcs) contracts storage ret ]
splitCase name creates contract iface ifs iffs ret storage postcs contracts =
  [ Behaviour name Pass creates contract iface (mconcat (ifs <> iffs)) (mconcat postcs) contracts storage ret,
    Behaviour name Fail creates contract iface (And (mconcat ifs) (Neg (mconcat iffs))) (mconcat postcs) contracts storage Nothing ]

-- extracts bounds on Integer values in storage, returns Iff or Exp Bool
-- representations for use in either pre or post conditions
getStorageBounds :: Env -> ([Exp Bool], [IffH])
getStorageBounds (ours, _, _) =
  unzip $ catMaybes $ fmap getBound $ Map.toList ours
  where
    getBound :: (Id, SlotType) -> Maybe (Exp Bool, IffH)
    getBound (id, (StorageValue typ)) = case metaType typ of
      Integer -> Just $ (bound typ (IntVar id), IffIn nowhere typ [EntryExp nowhere id []])
      _ -> Nothing
    getBound (_, _) = Nothing

-- extract a list of iff headers from the size of the types in a list of calldata declarations
getCallDataBounds :: [Decl] -> [IffH]
getCallDataBounds decls =
  join $
    fmap
      ( \(Decl typ id) -> case metaType typ of
          Integer -> [IffIn nowhere typ [EntryExp nowhere id []]]
          _ -> []
      )
      decls

-- ensures that key types match value types in an assign
checkAssign :: Env -> Assign -> Err (Id, [StorageUpdate])
checkAssign env (AssignVal (StorageVar (StorageValue typ) id) expr)
  = case metaType typ of
    Integer -> do
      val <- checkInt env expr
      return (id, [IntUpdate (DirectInt id) val])
    Boolean -> do
      val <- checkBool env expr
      return (id, [BoolUpdate (DirectBool id) val])
    ByteStr -> do
      val <- checkBytes env expr
      return (id, [BytesUpdate (DirectBytes id) val])
checkAssign env (AssignMany (StorageVar (StorageMapping (keyType :| _) valType) id) defns)
  = do updates <- mapM (checkDefn env keyType valType id) defns
       return $ (id, updates)
checkAssign env (AssignVal (StorageVar (StorageMapping _ _) _) _)
  = Bad (nowhere, "Cannot assign a single expression to a composite type")
checkAssign env (AssignMany (StorageVar (StorageValue _) _) _)
  = Bad (nowhere, "Cannot assign multiple values to an atomic type")
checkAssign _ _ = error $ "todo: support struct assignment in constructors"

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Env -> AbiType -> AbiType -> Id -> Defn -> Err StorageUpdate
checkDefn env keyType valType id (Defn k v) = case metaType keyType of
    Integer -> do
      key <- checkInt env k
      checkVal (ExpInt key)
    Boolean -> do
      key <- checkBool env k
      checkVal (ExpBool key)
    ByteStr -> do
      key <- checkBytes env k
      checkVal (ExpBytes key)
    where
      checkVal key = do
        case metaType valType of
          Integer -> do
            val <- checkInt env v
            return $ IntUpdate (MappedInt id (key :| [])) val
          Boolean -> do
            val <- checkBool env v
            return $ BoolUpdate (MappedBool id (key :| [])) val
          ByteStr -> do
            val <- checkBytes env v
            return $ BytesUpdate (MappedBytes id (key :| [])) val

checkPost :: Env -> Id -> Post -> Err (Map Id [Either StorageLocation StorageUpdate], Maybe ReturnExp, [Id])
checkPost env@(ours, theirs, localVars) contract (Post maybeStorage extStorage maybeReturn) =
  do  returnexp <- mapM (inferExpr env) maybeReturn
      ourStorage <- case maybeStorage of
        Just entries -> checkEntries contract entries
        Nothing -> Ok []
      otherStorage <- checkStorages extStorage
      return $ ((Map.fromList $ (contract, ourStorage):otherStorage),
                 returnexp,
                 contract:(map fst otherStorage))
  where checkEntries name entries =
          mapM (\a -> case a of
                   Rewrite loc val -> Right <$> checkStorageExpr (fromMaybe mempty (Map.lookup name theirs), theirs, localVars) loc val
                   Constant loc -> Left <$> checkEntry env loc
               ) entries
        checkStorages :: [ExtStorage] -> Err [(Id, [Either StorageLocation StorageUpdate])]
        checkStorages [] = Ok []
        checkStorages ((ExtStorage name entries):xs) = do p <- checkEntries name entries
                                                          ps <- checkStorages xs
                                                          Ok $ (name, p):ps
        checkStorages ((ExtCreates _ name entries):xs) = error "TODO: check other storages"

checkStorageExpr :: Env -> Entry -> Expr -> Err StorageUpdate
checkStorageExpr env@(ours, _, _) (Entry p id ixs) expr =
    case Map.lookup id ours of
      Just (StorageValue t)  -> case metaType t of
          Integer -> IntUpdate (DirectInt id) <$> checkInt env expr
          Boolean -> BoolUpdate (DirectBool id) <$> checkBool env expr
          ByteStr -> BytesUpdate (DirectBytes id) <$> checkBytes env expr
      Just (StorageMapping argtyps  t) ->
        if length argtyps /= length ixs
        then Bad $ (p, "Argument mismatch for storageitem: " <> id)
        else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr env))
             in case metaType t of
                  Integer -> liftM2 (IntUpdate . MappedInt id) indexExprs (checkInt env expr)
                  Boolean -> liftM2 (BoolUpdate . MappedBool id) indexExprs (checkBool env expr)
                  ByteStr -> liftM2 (BytesUpdate . MappedBytes id) indexExprs (checkBytes env expr)
      Nothing -> Bad $ (p, "Unknown storage variable: " <> show id)

checkEntry :: Env -> Entry -> Err StorageLocation
checkEntry env@(ours, _, _) (Entry p id ixs) =
  case Map.lookup id ours of
    Just (StorageValue t) -> case metaType t of
          Integer -> Ok $ IntLoc (DirectInt id)
          Boolean -> Ok $ BoolLoc (DirectBool id)
          ByteStr -> Ok $ BytesLoc (DirectBytes id)
    Just (StorageMapping argtyps t) ->
      if length argtyps /= length ixs
      then Bad $ (p, "Argument mismatch for storageitem: " <> id)
      else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr env))
           in case metaType t of
                  Integer -> (IntLoc . MappedInt id) <$> indexExprs
                  Boolean -> (BoolLoc . MappedBool id) <$> indexExprs
                  ByteStr -> (BytesLoc . MappedBytes id) <$> indexExprs
    Nothing -> Bad $ (p, "Unknown storage variable: " <> show id)

checkIffs :: Env -> [IffH] -> Err [Exp Bool]
checkIffs env ((Iff pos exps):xs) = do
  head <- mapM (checkBool env) exps
  tail <- checkIffs env xs
  Ok $ head <> tail
checkIffs env ((IffIn pos typ exps):xs) = do
  head <- mapM (checkInt env) exps
  tail <- checkIffs env xs
  Ok $ map (bound typ) head <> tail
checkIffs _ [] = Ok []

bound :: AbiType -> (Exp Int) -> Exp Bool
bound typ exp = And (LEQ (lowerBound typ) exp) $ LEQ exp (upperBound typ)

lowerBound :: AbiType -> Exp Int
lowerBound (AbiIntType a) = LitInt $ 0 - 2 ^ (a - 1)
-- todo: other negatives?
lowerBound _ = LitInt 0

--todo, the rest
upperBound :: AbiType -> Exp Int
upperBound (AbiUIntType n) = LitInt $ 2 ^ n - 1
upperBound (AbiIntType n) = LitInt $ 2 ^ (n - 1) - 1
upperBound AbiAddressType  = LitInt $ 2 ^ 160 - 1

metaType :: AbiType -> MType
metaType (AbiUIntType _)     = Integer
metaType (AbiIntType  _)     = Integer
metaType AbiAddressType      = Integer
metaType AbiBoolType         = Boolean
metaType (AbiBytesType _)    = ByteStr
metaType AbiBytesDynamicType = ByteStr
metaType AbiStringType       = ByteStr
--metaType (AbiArrayDynamicType a) =
--metaType (AbiArrayType        Int AbiType
--metaType (AbiTupleType        (Vector AbiType)
metaType _ = error "TODO"


checkExpr :: Env -> Expr -> AbiType -> Err ReturnExp
checkExpr env e typ = case metaType typ of
  Integer -> ExpInt <$> checkInt env e
  Boolean -> ExpBool <$> checkBool env e
  ByteStr -> ExpBytes <$> checkBytes env e

inferExpr :: Env -> Expr -> Err ReturnExp
inferExpr env@(ours, theirs,thisContext) exp =
                    let intintint op v1 v2 = do w1 <- checkInt env v1
                                                w2 <- checkInt env v2
                                                Ok $ ExpInt $ op w1 w2
                        boolintint op v1 v2 = do w1 <- checkInt env v1
                                                 w2 <- checkInt env v2
                                                 Ok $ ExpBool $ op w1 w2
                        boolboolbool op v1 v2 = do w1 <- checkBool env v1
                                                   w2 <- checkBool env v2
                                                   Ok $ ExpBool $ op w1 w2
                    in case exp of
    ENot _  v1     -> ExpBool . Neg <$> checkBool env v1
    EAnd _  v1 v2 -> boolboolbool And  v1 v2
    EOr _   v1 v2 -> boolboolbool Or   v1 v2
    EImpl _ v1 v2 -> boolboolbool Impl v1 v2
    EEq _   v1 v2 -> boolintint  Eq  v1 v2
    ENeq _  v1 v2 -> boolintint  NEq v1 v2
    ELT _   v1 v2 -> boolintint  LE   v1 v2
    ELEQ _  v1 v2 -> boolintint  LEQ  v1 v2
    EGT _   v1 v2 -> boolintint  GE   v1 v2
    ETrue _ ->  Ok . ExpBool $ LitBool True
    EFalse _ -> Ok . ExpBool $ LitBool False
    -- TODO: make ITE polymorphic
    EITE _ v1 v2 v3 -> do w1 <- checkBool env v1
                          w2 <- checkInt env v2
                          w3 <- checkInt env v3
                          Ok . ExpInt $ ITE w1 w2 w3
    EAdd _ v1 v2 -> intintint Add v1 v2
    ESub _ v1 v2 -> intintint Sub v1 v2
    EMul _ v1 v2 -> intintint Mul v1 v2
    EDiv _ v1 v2 -> intintint Div v1 v2
    EMod _ v1 v2 -> intintint Mod v1 v2
    EExp _ v1 v2 -> intintint Exp v1 v2
    IntLit n -> Ok $ ExpInt $ LitInt n
    BoolLit n -> Ok $ ExpBool $ LitBool n
    EntryExp p id e -> case (Map.lookup id ours, Map.lookup id thisContext) of
        (Nothing, Nothing) -> Bad (p, "Unknown variable: " <> show id)
        (Nothing, Just c) -> case c of
            Integer -> Ok . ExpInt $ IntVar id
            Boolean -> Ok . ExpBool $ BoolVar id
            ByteStr -> Ok . ExpBytes $ ByVar id
        (Just (StorageValue a), Nothing) ->
          case metaType a of
             Integer -> Ok . ExpInt $ TEntry (DirectInt id)
             Boolean -> Ok . ExpBool $ TEntry (DirectBool id)
             ByteStr -> Ok . ExpBytes $ TEntry (DirectBytes id)
        (Just (StorageMapping ts a), Nothing) ->
           let indexExprs = forM (NonEmpty.zip (head e :| tail e) ts)
                                     (uncurry (checkExpr env))
           in case metaType a of
             Integer -> ExpInt . TEntry . (MappedInt id) <$> indexExprs
             Boolean -> ExpBool . TEntry . (MappedBool id) <$> indexExprs
             ByteStr -> ExpBytes . TEntry . (MappedBytes id) <$> indexExprs
        (Just _, Just _) -> Bad (p, "Ambiguous variable: " <> show id)
    EnvExp p v1 -> case lookup v1 defaultStore of
      Just Integer -> Ok . ExpInt $ IntEnv v1
      Just ByteStr -> Ok . ExpBytes $ ByEnv v1
      _            -> Bad (p, "unknown environment variable: " <> show v1)
    -- Var p v -> case Map.lookup v thisContext of
    --   Just Integer -> Ok $ IntVar v
    --   _ -> Bad $ (p, "Unexpected variable: " <> show v <> " of type integer")

    v -> error $ "internal error: infer type of:" <> show v
    -- Wild ->
    -- Zoom Var Exp
    -- Func Var [Expr]
    -- Look Expr Expr
    -- ECat Expr Expr
    -- ESlice Expr Expr Expr
    -- Newaddr Expr Expr
    -- Newaddr2 Expr Expr Expr
    -- BYHash Expr
    -- BYAbiE Expr
    -- StringLit String

checkBool :: Env -> Expr -> Err (Exp Bool)
checkBool env exp =
  case inferExpr env exp of
    Ok (ExpInt _) -> Bad (nowhere, "expected: bool, got: int")
    Ok (ExpBytes _) -> Bad (nowhere, "expected: bool, got: bytes")
    Ok (ExpBool a) -> Ok a
    Bad e -> Bad e


checkBytes :: Env -> Expr -> Err (Exp ByteString)
checkBytes env exp =
  case inferExpr env exp of
    Ok (ExpInt _) -> Bad (nowhere, "expected: bytes, got: int")
    Ok (ExpBytes a) -> Ok a
    Ok (ExpBool _) -> Bad (nowhere, "expected: bytes, got: bool")
    Bad e -> Bad e

checkInt :: Env -> Expr -> Err (Exp Int)
checkInt env exp =
  case inferExpr env exp of
    Ok (ExpInt a) -> Ok a
    Ok (ExpBytes _) -> Bad (nowhere, "expected: int, got: bytes")
    Ok (ExpBool _) -> Bad (nowhere, "expected: int, got: bool")
    Bad e -> Bad e
