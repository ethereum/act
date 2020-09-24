{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Type (typecheck, metaType, mkStorageBounds, lookupVars) where

import Data.List
import EVM.ABI
import EVM.Solidity (SlotType(..))
import Data.Map.Strict    (Map)
import Data.Maybe
import Data.Either
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map -- abandon in favor of [(a,b)]?

import Data.ByteString (ByteString)

import Control.Monad

import Syntax hiding (Storage)
import ErrM
import Parse
import RefinedAst

typecheck :: [RawBehaviour] -> Err [Claim]
typecheck behvs = let store = lookupVars behvs in
                  do bs <- mapM (splitBehaviour store) behvs
                     return $ S (Storages store):(join bs)

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Store
lookupVars ((Transition {}):bs) = lookupVars bs
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
   (This, Integer),
   (Origin, Integer),
   (Nonce, Integer),
   (Calldepth, Integer)
  ]

type Store = Map Id (Map Id SlotType)

-- typing of vars: this contract name, this contract storage, other contract scopes, calldata args
type Env = (Id, Map Id SlotType, Store, Map Id MType)

-- checks a transition given a typing of its storage variables
splitBehaviour :: Store -> RawBehaviour -> Err [Claim]
splitBehaviour store (Transition name contract iface@(Interface _ decls) iffs' cases maybePost) = do
  -- constrain integer calldata variables (TODO: other types)
  let calldataBounds = getCallDataBounds decls
  iff <- checkIffs env (iffs' <> calldataBounds)
  postcondition <- mapM (checkBool env) (fromMaybe [] maybePost)
  flatten iff postcondition cases
  where
    env :: Env
    env = mkEnv contract store decls

    -- translate wildcards into negation of other cases
    normalize :: [Case] -> Err [Case]
    normalize cases' =
      let wildcard (Case _ WildExp _) = True
          wildcard _ = False
      in case findIndex wildcard cases' of
        Nothing -> return $ snd $ mapAccumL checkCase (BoolLit False) cases'
        Just ind ->
          -- wildcard must be last element
          if ind < length cases' - 1
          then case cases' !! ind of
            (Case p _ _) -> Bad (p, "Wildcard pattern must be last case")
          else return $ snd $ mapAccumL checkCase (BoolLit False) cases'

    checkCase :: Expr -> Case -> (Expr, Case)
    checkCase acc (Case p WildExp post) =
      (error "wildcard not last case",
        Case p (ENot nowhere acc) post)
    checkCase acc (Case p e post) = (EOr nowhere e acc, Case p e post)


    -- flatten case list
    flatten :: [Exp Bool] -> [Exp Bool] -> Cases -> Err [Claim]
    flatten iff postc (Direct post) = do
      (p, maybeReturn) <- checkPost env post
      let preBounds = mkStorageBounds store p
          ethEnvs' = concat $ ethEnvFromExp <$> (iff <> postc)
          ethEnvs'' = ethEnvFromReturnExp $ fromMaybe (ExpBool $ LitBool True) maybeReturn
          ethEnvs''' = concat $ ethEnvFromStorageUpdate <$> (rights p)
          ethEnvBounds = mkEthEnvBounds $ ethEnvs' <> ethEnvs'' <> ethEnvs'''
      return $ splitCase name False contract iface ethEnvBounds (iff <> preBounds) maybeReturn p postc
    flatten iff postc (Branches branches) = do
      branches' <- normalize branches
      cases' <- forM branches' $ \(Case _ cond post) -> do
        if' <- checkBool env cond
        (post', ret) <- checkPost env post
        return (if', post', ret)

      pure . join $ ((\(ifcond, stateUpdates, ret) -> let
          preBounds = mkStorageBounds store stateUpdates
          ethEnvs' = concat $ ethEnvFromExp <$> ([ifcond] <> iff <> postc)
          ethEnvs'' = ethEnvFromReturnExp $ fromMaybe (ExpBool $ LitBool True) ret
          ethEnvs''' = concat $ ethEnvFromStorageUpdate <$> (rights stateUpdates)
          ethEnvBounds = mkEthEnvBounds $ ethEnvs' <> ethEnvs'' <> ethEnvs'''
        in splitCase name False contract iface ([ifcond] <> ethEnvBounds) (iff <> preBounds) ret stateUpdates postc) <$> cases')

splitBehaviour store (Constructor name contract iface@(Interface _ decls) iffs (Creates assigns) extStorage maybeEnsures maybeInvs) = do
  unless (null extStorage) $ error "TODO: support extStorage in constructor"

  let env = mkEnv contract store decls


  rawUpdates <- concat <$> mapM (checkAssign env) assigns
  let stateUpdates = Right <$> rawUpdates

  let calldataBounds = getCallDataBounds decls
  iffs' <- checkIffs env (iffs <> calldataBounds)

  invariants <- mapM (checkBool env) $ fromMaybe [] maybeInvs
  ensures <- mapM (checkBool env) (fromMaybe [] maybeEnsures)

  let ethEnvs' = concat $ ethEnvFromExp <$> concat [iffs', invariants, ensures]
      ethEnvs'' = concat $ ethEnvFromStorageUpdate <$> (rights stateUpdates)
      ethEnvBounds = mkEthEnvBounds $ ethEnvs' <> ethEnvs''

  return $ ((I . (Invariant contract)) <$> invariants)
           <> (splitCase name True contract iface ethEnvBounds iffs' Nothing stateUpdates ensures)

mkEnv :: Id -> Store -> [Decl]-> Env
mkEnv contract store decls = (contract, fromMaybe mempty (Map.lookup contract store), store, abiVars)
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- | split case into pass and fail case
splitCase :: Id -> Bool -> Id -> Interface -> [Exp Bool] -> [Exp Bool] -> Maybe ReturnExp
          -> [Either StorageLocation StorageUpdate] -> [Exp Bool] -> [Claim]
splitCase name creates contract iface if' [] ret storage postcs =
  [ B $ Behaviour name Pass creates contract iface (mconcat if') (mconcat postcs) storage ret ]
splitCase name creates contract iface if' iffs ret storage postcs =
  [ B $ Behaviour name Pass creates contract iface (mconcat (if' <> iffs)) (mconcat postcs) storage ret,
    B $ Behaviour name Fail creates contract iface (And (mconcat if') (Neg (mconcat iffs))) (mconcat postcs) storage Nothing ]

mkEthEnvBounds :: [EthEnv] -> [Exp Bool]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp Bool)
    mkBound e = case lookup e defaultStore of
      Just (Integer) -> Just $ bound (toAbiType e) (IntEnv e)
      _ -> Nothing

    toAbiType :: EthEnv -> AbiType
    toAbiType env = case env of
      Caller -> AbiAddressType
      Callvalue -> AbiUIntType 256
      Calldepth -> AbiUIntType 10
      Origin -> AbiAddressType
      Blockhash -> AbiBytesType 32
      Blocknumber -> AbiUIntType 256
      Difficulty -> AbiUIntType 256
      Chainid -> AbiUIntType 256
      Gaslimit -> AbiUIntType 256
      Coinbase -> AbiAddressType
      Timestamp -> AbiUIntType 256
      This -> AbiAddressType
      Nonce -> AbiUIntType 256

-- | extracts bounds from the AbiTypes of Integer values in storage
mkStorageBounds :: Store -> [Either StorageLocation StorageUpdate] -> [Exp Bool]
mkStorageBounds store refs
  = catMaybes $ mkBound <$> refs
  where
    mkBound :: Either StorageLocation StorageUpdate -> Maybe (Exp Bool)
    mkBound (Left (IntLoc item)) = Just $ fromItem item
    mkBound (Right (IntUpdate item _)) = Just $ fromItem item
    mkBound _ = Nothing

    fromItem :: TStorageItem Integer -> Exp Bool
    fromItem item@(DirectInt contract name) = bound (abiType $ slotType contract name) (TEntry item)
    fromItem item@(MappedInt contract name _) = bound (abiType $ slotType contract name) (TEntry item)

    slotType :: Id -> Id -> SlotType
    slotType contract name = let
        vars = fromMaybe (error $ contract <> " not found in " <> show store) $ Map.lookup contract store
      in fromMaybe (error $ name <> " not found in " <> show vars) $ Map.lookup name vars


    abiType :: SlotType -> AbiType
    abiType (StorageMapping _ typ) = typ
    abiType (StorageValue typ) = typ

-- | extract a list of iff headers from the size of the types in a list of calldata declarations
getCallDataBounds :: [Decl] -> [IffH]
getCallDataBounds decls =
  join $
    fmap
      ( \(Decl typ name) -> case metaType typ of
          Integer -> [IffIn nowhere typ [EntryExp nowhere name []]]
          _ -> []
      )
      decls

-- ensures that key types match value types in an Assign
checkAssign :: Env -> Assign -> Err [StorageUpdate]
checkAssign env@(contract, _, _, _) (AssignVal (StorageVar (StorageValue typ) name) expr)
  = case metaType typ of
    Integer -> do
      val <- checkInt env expr
      return [IntUpdate (DirectInt contract name) val]
    Boolean -> do
      val <- checkBool env expr
      return [BoolUpdate (DirectBool contract name) val]
    ByteStr -> do
      val <- checkBytes env expr
      return [BytesUpdate (DirectBytes contract name) val]
checkAssign env (AssignMany (StorageVar (StorageMapping (keyType :| _) valType) name) defns)
  = mapM (checkDefn env keyType valType name) defns
checkAssign _ (AssignVal (StorageVar (StorageMapping _ _) _) _)
  = Bad (nowhere, "Cannot assign a single expression to a composite type")
checkAssign _ (AssignMany (StorageVar (StorageValue _) _) _)
  = Bad (nowhere, "Cannot assign multiple values to an atomic type")
checkAssign _ _ = error "todo: support struct assignment in constructors"

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Env -> AbiType -> AbiType -> Id -> Defn -> Err StorageUpdate
checkDefn env@(contract, _, _, _) keyType valType name (Defn k v) = case metaType keyType of
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
            return $ IntUpdate (MappedInt contract name (key :| [])) val
          Boolean -> do
            val <- checkBool env v
            return $ BoolUpdate (MappedBool contract name (key :| [])) val
          ByteStr -> do
            val <- checkBytes env v
            return $ BytesUpdate (MappedBytes contract name (key :| [])) val

checkPost :: Env -> Post -> Err ([Either StorageLocation StorageUpdate], Maybe ReturnExp)
checkPost env@(contract, _, theirs, localVars) (Post maybeStorage extStorage maybeReturn) =
  do  returnexp <- mapM (inferExpr env) maybeReturn
      ourStorage <- case maybeStorage of
        Just entries -> checkEntries contract entries
        Nothing -> Ok []
      otherStorage <- checkStorages extStorage
      return (ourStorage <> otherStorage, returnexp)
  where checkEntries name entries =
          mapM (\case
                   Rewrite loc val -> Right <$> checkStorageExpr (name, fromMaybe mempty (Map.lookup name theirs), theirs, localVars) loc val
                   Constant loc -> Left <$> checkEntry env loc
               ) entries
        checkStorages :: [ExtStorage] -> Err [Either StorageLocation StorageUpdate]
        checkStorages [] = Ok []
        checkStorages ((ExtStorage name entries):xs) = do p <- checkEntries name entries
                                                          ps <- checkStorages xs
                                                          Ok $ p <> ps
        checkStorages _ = error "TODO: check other storages"

checkStorageExpr :: Env -> Entry -> Expr -> Err StorageUpdate
checkStorageExpr env@(contract, ours, _, _) (Entry p name ixs) expr =
    case Map.lookup name ours of
      Just (StorageValue t)  -> case metaType t of
          Integer -> IntUpdate (DirectInt contract name) <$> checkInt env expr
          Boolean -> BoolUpdate (DirectBool contract name) <$> checkBool env expr
          ByteStr -> BytesUpdate (DirectBytes contract name) <$> checkBytes env expr
      Just (StorageMapping argtyps  t) ->
        if length argtyps /= length ixs
        then Bad (p, "Argument mismatch for storageitem: " <> name)
        else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr env))
             in case metaType t of
                  Integer -> liftM2 (IntUpdate . MappedInt contract name) indexExprs (checkInt env expr)
                  Boolean -> liftM2 (BoolUpdate . MappedBool contract name) indexExprs (checkBool env expr)
                  ByteStr -> liftM2 (BytesUpdate . MappedBytes contract name) indexExprs (checkBytes env expr)
      Nothing -> Bad (p, "Unknown storage variable: " <> show name)
checkStorageExpr _ Wild _ = error "TODO: add support for wild storage to checkStorageExpr"

checkEntry :: Env -> Entry -> Err StorageLocation
checkEntry env@(contract, ours, _, _) (Entry p name ixs) =
  case Map.lookup name ours of
    Just (StorageValue t) -> case metaType t of
          Integer -> Ok $ IntLoc (DirectInt contract name)
          Boolean -> Ok $ BoolLoc (DirectBool contract name)
          ByteStr -> Ok $ BytesLoc (DirectBytes contract name)
    Just (StorageMapping argtyps t) ->
      if length argtyps /= length ixs
      then Bad (p, "Argument mismatch for storageitem: " <> name)
      else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr env))
           in case metaType t of
                  Integer -> (IntLoc . MappedInt contract name) <$> indexExprs
                  Boolean -> (BoolLoc . MappedBool contract name) <$> indexExprs
                  ByteStr -> (BytesLoc . MappedBytes contract name) <$> indexExprs
    Nothing -> Bad (p, "Unknown storage variable: " <> show name)
checkEntry _ Wild = error "TODO: checkEntry for Wild storage"

checkIffs :: Env -> [IffH] -> Err [Exp Bool]
checkIffs env ((Iff _ exps):xs) = do
  hd <- mapM (checkBool env) exps
  tl <- checkIffs env xs
  Ok $ hd <> tl
checkIffs env ((IffIn _ typ exps):xs) = do
  hd <- mapM (checkInt env) exps
  tl <- checkIffs env xs
  Ok $ map (bound typ) hd <> tl
checkIffs _ [] = Ok []

bound :: AbiType -> (Exp Integer) -> Exp Bool
bound typ e = And (LEQ (lowerBound typ) e) $ LEQ e (upperBound typ)

lowerBound :: AbiType -> Exp Integer
lowerBound (AbiIntType a) = LitInt $ negate $ 2 ^ (a - 1)
-- todo: other negatives?
lowerBound _ = LitInt 0

--todo, the rest
upperBound :: AbiType -> Exp Integer
upperBound (AbiUIntType n) = LitInt $ 2 ^ n - 1
upperBound (AbiIntType n) = LitInt $ 2 ^ (n - 1) - 1
upperBound AbiAddressType  = LitInt $ 2 ^ (160 :: Integer) - 1
upperBound typ  = error $ "upperBound not implemented for " ++ show typ

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
inferExpr env@(contract, ours, _,thisContext) expr =
  let intintint op v1 v2 = do w1 <- checkInt env v1
                              w2 <- checkInt env v2
                              Ok $ ExpInt $ op w1 w2
      boolintint op v1 v2 = do w1 <- checkInt env v1
                               w2 <- checkInt env v2
                               Ok $ ExpBool $ op w1 w2
      boolboolbool op v1 v2 = do w1 <- checkBool env v1
                                 w2 <- checkBool env v2
                                 Ok $ ExpBool $ op w1 w2
  in case expr of
    ENot _  v1    -> ExpBool . Neg <$> checkBool env v1
    EAnd _  v1 v2 -> boolboolbool And  v1 v2
    EOr _   v1 v2 -> boolboolbool Or   v1 v2
    EImpl _ v1 v2 -> boolboolbool Impl v1 v2
    EEq _   v1 v2 -> boolintint  Eq  v1 v2
    ENeq _  v1 v2 -> boolintint  NEq v1 v2
    ELT _   v1 v2 -> boolintint  LE   v1 v2
    ELEQ _  v1 v2 -> boolintint  LEQ  v1 v2
    EGEQ _  v1 v2 -> boolintint  GEQ  v1 v2
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
    EntryExp p name e -> case (Map.lookup name ours, Map.lookup name thisContext) of
        (Nothing, Nothing) -> Bad (p, "Unknown variable: " <> show name)
        (Nothing, Just c) -> case c of
            Integer -> Ok . ExpInt $ IntVar name
            Boolean -> Ok . ExpBool $ BoolVar name
            ByteStr -> Ok . ExpBytes $ ByVar name
        (Just (StorageValue a), Nothing) ->
          case metaType a of
             Integer -> Ok . ExpInt $ TEntry (DirectInt contract name)
             Boolean -> Ok . ExpBool $ TEntry (DirectBool contract name)
             ByteStr -> Ok . ExpBytes $ TEntry (DirectBytes contract name)
        (Just (StorageMapping ts a), Nothing) ->
           let indexExprs = forM (NonEmpty.zip (head e :| tail e) ts)
                                     (uncurry (checkExpr env))
           in case metaType a of
             Integer -> ExpInt . TEntry . (MappedInt contract name) <$> indexExprs
             Boolean -> ExpBool . TEntry . (MappedBool contract name) <$> indexExprs
             ByteStr -> ExpBytes . TEntry . (MappedBytes contract name) <$> indexExprs
        (Just _, Just _) -> Bad (p, "Ambiguous variable: " <> show name)
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
checkBool env e =
  case inferExpr env e of
    Ok (ExpInt _) -> Bad (nowhere, "expected: bool, got: int")
    Ok (ExpBytes _) -> Bad (nowhere, "expected: bool, got: bytes")
    Ok (ExpBool a) -> Ok a
    Bad err -> Bad err


checkBytes :: Env -> Expr -> Err (Exp ByteString)
checkBytes env e =
  case inferExpr env e of
    Ok (ExpInt _) -> Bad (nowhere, "expected: bytes, got: int")
    Ok (ExpBytes a) -> Ok a
    Ok (ExpBool _) -> Bad (nowhere, "expected: bytes, got: bool")
    Bad err -> Bad err

checkInt :: Env -> Expr -> Err (Exp Integer)
checkInt env e =
  case inferExpr env e of
    Ok (ExpInt a) -> Ok a
    Ok (ExpBytes _) -> Bad (nowhere, "expected: int, got: bytes")
    Ok (ExpBool _) -> Bad (nowhere, "expected: int, got: bool")
    Bad err -> Bad err

ethEnvFromStorageUpdate :: StorageUpdate -> [EthEnv]
ethEnvFromStorageUpdate (IntUpdate _ e)  = ethEnvFromExp e
ethEnvFromStorageUpdate (BoolUpdate _ e) = ethEnvFromExp e
ethEnvFromStorageUpdate (BytesUpdate _ e) = ethEnvFromExp e

ethEnvFromReturnExp :: ReturnExp -> [EthEnv]
ethEnvFromReturnExp (ExpInt e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBool e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBytes e) = ethEnvFromExp e

ethEnvFromExp :: Exp a -> [EthEnv]
ethEnvFromExp e = case e of
  And a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Or a b    -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Impl a b  -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Eq a b    -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  LE a b    -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  LEQ a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  GE a b    -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  GEQ a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  NEq a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Neg a     -> (ethEnvFromExp a)
  Add a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Sub a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Mul a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Div a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Mod a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Exp a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Cat a b   -> (ethEnvFromExp a) <> (ethEnvFromExp b)
  Slice a b c -> (ethEnvFromExp a) <> (ethEnvFromExp b) <> (ethEnvFromExp c)
  ITE a b c -> (ethEnvFromExp a) <> (ethEnvFromExp b) <> (ethEnvFromExp c)
  ByVar _ -> []
  ByStr _ -> []
  ByLit _ -> []
  LitInt _  -> []
  IntVar _  -> []
  LitBool _ -> []
  BoolVar _ -> []
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  IntEnv a -> [a]
  ByEnv a -> [a]
  TEntry a  -> case a of
    MappedInt _ _ ixs -> concat $ ethEnvFromReturnExp <$> NonEmpty.toList ixs
    MappedBool _ _ ixs -> concat $ ethEnvFromReturnExp <$> NonEmpty.toList ixs
    MappedBytes _ _ ixs -> concat $ ethEnvFromReturnExp <$> NonEmpty.toList ixs
    _ -> []
