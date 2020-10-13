{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Type (typecheck, metaType, bound, getLoc, mkLoc, lookupVars, defaultStore, Store) where

import Data.List
import EVM.ABI
import EVM.Solidity (SlotType(..))
import Data.Map.Strict    (Map)
import Data.Maybe
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

type Store = Map Id (Map Id SlotType)

-- typing of vars: this contract name, this contract storage, other contract scopes, calldata args
type Env = (Id, Map Id SlotType, Store, Map Id MType)

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
   --others TODO
  ]

-- checks a transition given a typing of its storage variables
splitBehaviour :: Store -> RawBehaviour -> Err [Claim]
splitBehaviour store (Transition name contract iface@(Interface _ decls) iffs' cases maybePost) = do
  -- constrain integer calldata variables (TODO: other types)
  iff <- checkIffs env iffs'
  postcondition <- mapM (checkBool nowhere env) (fromMaybe [] maybePost)
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
      return $ splitCase name False contract iface [] iff maybeReturn p postc
    flatten iff postc (Branches branches) = do
      branches' <- normalize branches
      cases' <- forM branches' $ \(Case _ cond post) -> do
        if' <- checkBool nowhere env cond
        (post', ret) <- checkPost env post
        return (if', post', ret)

      pure . join $ ((\(ifcond, stateUpdates, ret) ->
        splitCase name False contract iface [ifcond] iff ret stateUpdates postc) <$> cases')

splitBehaviour store (Constructor name contract iface@(Interface _ decls) iffs (Creates assigns) extStorage maybeEnsures maybeInvs) = do
  unless (null extStorage) $ error "TODO: support extStorage in constructor"

  let env = mkEnv contract store decls
  stateUpdates <- concat <$> mapM (checkAssign env) assigns
  let stateUpdates' = Right <$> stateUpdates
  iffs' <- checkIffs env iffs

  invariants <- mapM (checkBool nowhere env) $ fromMaybe [] maybeInvs
  ensures <- mapM (checkBool nowhere env) (fromMaybe [] maybeEnsures)

  -- this forces the smt backend to be run on every spec, ensuring postconditions are checked for every behaviour
  -- TODO: seperate the smt backend into seperate passes so we only run the invariant analysis if required
  let invariants' = if (null invariants) then [LitBool True] else invariants

  return $ ((I . (Invariant contract)) <$> invariants')
           <> (splitCase name True contract iface [] iffs' Nothing stateUpdates' ensures)

mkEnv :: Id -> Store -> [Decl]-> Env
mkEnv contract store decls = (contract, fromMaybe mempty (Map.lookup contract store), store, abiVars)
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- | split case into pass and fail case
splitCase :: Id -> Bool -> Id -> Interface -> [Exp Bool] -> [Exp Bool] -> Maybe ReturnExp
          -> [Either StorageLocation StorageUpdate] -> [Exp Bool] -> [Claim]
splitCase name creates contract iface if' [] ret storage postcs =
  [ B $ Behaviour name Pass creates contract iface if' postcs storage ret ]
splitCase name creates contract iface if' iffs ret storage postcs =
  [ B $ Behaviour name Pass creates contract iface (if' <> iffs) postcs storage ret,
    B $ Behaviour name Fail creates contract iface (if' <> (Neg <$> (iffs))) [] (Left . getLoc <$> storage) Nothing ]

-- ensures that key types match value types in an Assign
checkAssign :: Env -> Assign -> Err [StorageUpdate]
checkAssign env@(contract, _, _, _) (AssignVal (StorageVar (StorageValue typ) name) expr)
  = case metaType typ of
    Integer -> do
      val <- checkInt nowhere env expr
      return [IntUpdate (DirectInt contract name) val]
    Boolean -> do
      val <- checkBool nowhere env expr
      return [BoolUpdate (DirectBool contract name) val]
    ByteStr -> do
      val <- checkBytes nowhere env expr
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
      key <- checkInt nowhere env k
      checkVal (ExpInt key)
    Boolean -> do
      key <- checkBool nowhere env k
      checkVal (ExpBool key)
    ByteStr -> do
      key <- checkBytes nowhere env k
      checkVal (ExpBytes key)
    where
      checkVal key = do
        case metaType valType of
          Integer -> do
            val <- checkInt nowhere env v
            return $ IntUpdate (MappedInt contract name (key :| [])) val
          Boolean -> do
            val <- checkBool nowhere env v
            return $ BoolUpdate (MappedBool contract name (key :| [])) val
          ByteStr -> do
            val <- checkBytes nowhere env v
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
          Integer -> IntUpdate (DirectInt contract name) <$> checkInt p env expr
          Boolean -> BoolUpdate (DirectBool contract name) <$> checkBool p env expr
          ByteStr -> BytesUpdate (DirectBytes contract name) <$> checkBytes p env expr
      Just (StorageMapping argtyps  t) ->
        if length argtyps /= length ixs
        then Bad (p, "Argument mismatch for storageitem: " <> name)
        else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr p env))
             in case metaType t of
                  Integer -> liftM2 (IntUpdate . MappedInt contract name) indexExprs (checkInt p env expr)
                  Boolean -> liftM2 (BoolUpdate . MappedBool contract name) indexExprs (checkBool p env expr)
                  ByteStr -> liftM2 (BytesUpdate . MappedBytes contract name) indexExprs (checkBytes p env expr)
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
      else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr p env))
           in case metaType t of
                  Integer -> (IntLoc . MappedInt contract name) <$> indexExprs
                  Boolean -> (BoolLoc . MappedBool contract name) <$> indexExprs
                  ByteStr -> (BytesLoc . MappedBytes contract name) <$> indexExprs
    Nothing -> Bad (p, "Unknown storage variable: " <> show name)
checkEntry _ Wild = error "TODO: checkEntry for Wild storage"

checkIffs :: Env -> [IffH] -> Err [Exp Bool]
checkIffs env ((Iff p exps):xs) = do
  hd <- mapM (checkBool p env) exps
  tl <- checkIffs env xs
  Ok $ hd <> tl
checkIffs env ((IffIn p typ exps):xs) = do
  hd <- mapM (checkInt p env) exps
  tl <- checkIffs env xs
  Ok $ map (bound typ) hd <> tl
checkIffs _ [] = Ok []

bound :: AbiType -> (Exp Integer) -> Exp Bool
bound typ e = And (LEQ (lowerBound typ) e) $ LEQ e (upperBound typ)

lowerBound :: AbiType -> Exp Integer
lowerBound (AbiIntType a) = IntMin a
-- todo: other negatives?
lowerBound _ = LitInt 0

-- todo, the rest
upperBound :: AbiType -> Exp Integer
upperBound (AbiUIntType n) = UIntMax n
upperBound (AbiIntType n) = IntMax n
upperBound AbiAddressType = UIntMax 160
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


checkExpr :: Pn -> Env -> Expr -> AbiType -> Err ReturnExp
checkExpr p env e typ = case metaType typ of
  Integer -> ExpInt <$> checkInt p env e
  Boolean -> ExpBool <$> checkBool p env e
  ByteStr -> ExpBytes <$> checkBytes p env e

inferExpr :: Env -> Expr -> Err ReturnExp
inferExpr env@(contract, ours, _,thisContext) expr =
  let intintint p op v1 v2 = do w1 <- checkInt p env v1
                                w2 <- checkInt p env v2
                                Ok $ ExpInt $ op w1 w2
      boolintint p op v1 v2 = do w1 <- checkInt p env v1
                                 w2 <- checkInt p env v2
                                 Ok $ ExpBool $ op w1 w2
      boolboolbool p op v1 v2 = do w1 <- checkBool p env v1
                                   w2 <- checkBool p env v2
                                   Ok $ ExpBool $ op w1 w2
  in case expr of
    ENot p  v1    -> ExpBool . Neg <$> checkBool p env v1
    EAnd p  v1 v2 -> boolboolbool p And  v1 v2
    EOr p   v1 v2 -> boolboolbool p Or   v1 v2
    EImpl p v1 v2 -> boolboolbool p Impl v1 v2
    EEq p   v1 v2 -> boolintint  p Eq  v1 v2
    ENeq p  v1 v2 -> boolintint  p NEq v1 v2
    ELT p   v1 v2 -> boolintint  p LE   v1 v2
    ELEQ p  v1 v2 -> boolintint  p LEQ  v1 v2
    EGEQ p  v1 v2 -> boolintint  p GEQ  v1 v2
    EGT p   v1 v2 -> boolintint  p GE   v1 v2
    ETrue _ ->  Ok . ExpBool $ LitBool True
    EFalse _ -> Ok . ExpBool $ LitBool False
    -- TODO: make ITE polymorphic
    EITE p v1 v2 v3 -> do w1 <- checkBool p env v1
                          w2 <- checkInt p env v2
                          w3 <- checkInt p env v3
                          Ok . ExpInt $ ITE w1 w2 w3
    EAdd p v1 v2 -> intintint p Add v1 v2
    ESub p v1 v2 -> intintint p Sub v1 v2
    EMul p v1 v2 -> intintint p Mul v1 v2
    EDiv p v1 v2 -> intintint p Div v1 v2
    EMod p v1 v2 -> intintint p Mod v1 v2
    EExp p v1 v2 -> intintint p Exp v1 v2
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
                                     (uncurry (checkExpr p env))
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

checkBool :: Pn -> Env -> Expr -> Err (Exp Bool)
checkBool p env e =
  case inferExpr env e of
    Ok (ExpInt _) -> Bad (p, "expected: bool, got: int")
    Ok (ExpBytes _) -> Bad (p, "expected: bool, got: bytes")
    Ok (ExpBool a) -> Ok a
    Bad err -> Bad err


checkBytes :: Pn -> Env -> Expr -> Err (Exp ByteString)
checkBytes p env e =
  case inferExpr env e of
    Ok (ExpInt _) -> Bad (p, "expected: bytes, got: int")
    Ok (ExpBytes a) -> Ok a
    Ok (ExpBool _) -> Bad (p, "expected: bytes, got: bool")
    Bad err -> Bad err

checkInt :: Pn -> Env -> Expr -> Err (Exp Integer)
checkInt p env e =
  case inferExpr env e of
    Ok (ExpInt a) -> Ok a
    Ok (ExpBytes _) -> Bad (p, "expected: int, got: bytes")
    Ok (ExpBool _) -> Bad (p, "expected: int, got: bool")
    Bad err -> Bad err

getLoc :: Either StorageLocation StorageUpdate -> StorageLocation
getLoc ref = either id mkLoc ref

mkLoc :: StorageUpdate -> StorageLocation
mkLoc (IntUpdate item _) = IntLoc item
mkLoc (BoolUpdate item _) = BoolLoc item
mkLoc (BytesUpdate item _) = BytesLoc item
