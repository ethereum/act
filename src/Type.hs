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

module Type where

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

import Syntax
import ErrM
import Parse
import RefinedAst

typecheck :: [RawBehaviour] -> Err [Claim]
typecheck behvs = let store = lookupVars behvs in
                  do bs <- mapM (splitBehaviour store) behvs
                     return $ join bs

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Type.Store
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
type Env = (Map Id SlotType, Type.Store, Map Id MType)

andRaw :: [Expr] -> Expr
andRaw [x] = x
andRaw (x:xs) = EAnd nowhere x (andRaw xs)
andRaw [] = BoolLit True

-- checks a transition given a typing of its storage variables
splitBehaviour :: Type.Store -> RawBehaviour -> Err [Claim]
splitBehaviour store (Transition name contract iface@(Interface _ decls) iffs' cases maybePost) = do
  -- constrain integer calldata variables (TODO: other types)
  let calldataBounds = getCallDataBounds decls
      storageBounds = snd $ getStorageBounds env
  iff <- checkIffs env (iffs' <> calldataBounds <> storageBounds)
  postcondition <- mapM (checkBool env) (fromMaybe [] maybePost)
  flatten iff postcondition cases
  where
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
      (p, maybeReturn) <- checkPost env contract post
      return $ splitCase name False contract iface (LitBool True) iff maybeReturn p postc
    flatten iff postc (Branches branches) = do
      branches' <- normalize branches
      cases' <- flip mapM branches' $ \(Case _ cond post) -> do
        if' <- checkBool env cond
        (post', ret) <- checkPost env contract post
        return (if', post', ret)

      pure . join $ ((\(ifcond, stateUpdates, ret) ->
         splitCase name False contract iface ifcond iff ret stateUpdates postc) <$> cases')

splitBehaviour store (Constructor name contract iface@(Interface _ decls) iffs (Creates assigns) extStorage maybeEnsures maybeInvariants) = do
  when (length extStorage > 0) $ error "TODO: support extStorage in constructor"

  let env = mkEnv contract store decls

  rawUpdates <- mapM (checkAssign env) assigns
  let stateUpdates = Map.fromList $ [(contract, Right <$> concat rawUpdates)]

  let calldataBounds = getCallDataBounds decls
  iffs' <- checkIffs env (iffs <> calldataBounds)

  invariants <- mapM (checkBool env) $ fromMaybe [] maybeInvariants
  ensures <- mapM (checkBool env) (fromMaybe [] maybeEnsures)
  let storageBounds = fst $ getStorageBounds env
      postcs = storageBounds <> invariants <> ensures

  return $ ((I . (Invariant contract)) <$> invariants)
           ++ (splitCase name True contract iface (LitBool True) iffs' Nothing stateUpdates postcs)

mkEnv :: Id -> Type.Store -> [Decl]-> Env
mkEnv contract store decls = (fromMaybe mempty (Map.lookup contract store), store, abiVars)
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- split case into pass and fail case
splitCase :: Id -> Bool -> Id -> Interface -> Exp Bool -> [Exp Bool] -> Maybe ReturnExp
          -> Map Id [Either StorageLocation StorageUpdate] -> [Exp Bool] -> [Claim]
splitCase name creates contract iface if' [] ret storage postcs =
  [ B $ Behaviour name Pass creates contract iface if' (mconcat postcs) storage ret ]
splitCase name creates contract iface if' iffs ret storage postcs =
  [ B $ Behaviour name Pass creates contract iface (mconcat (if':iffs)) (mconcat postcs) storage ret,
    B $ Behaviour name Fail creates contract iface (And if' (Neg (mconcat iffs))) (mconcat postcs) storage Nothing ]

-- extracts bounds on Integer values in storage, returns Iff or Exp Bool
-- representations for use in either pre or post conditions
getStorageBounds :: Env -> ([Exp Bool], [IffH])
getStorageBounds (ours, _, _) =
  unzip $ catMaybes $ fmap getBound $ Map.toList ours
  where
    getBound :: (Id, SlotType) -> Maybe (Exp Bool, IffH)
    getBound (name, (StorageValue typ)) = case metaType typ of
      Integer -> Just $ (bound typ (IntVar name), IffIn nowhere typ [EntryExp nowhere name []])
      _ -> Nothing
    getBound (_, _) = Nothing

-- extract a list of iff headers from the size of the types in a list of calldata declarations
getCallDataBounds :: [Decl] -> [IffH]
getCallDataBounds decls =
  join $
    fmap
      ( \(Decl typ name) -> case metaType typ of
          Integer -> [IffIn nowhere typ [EntryExp nowhere name []]]
          _ -> []
      )
      decls

-- ensures that key types match value types in an assign
checkAssign :: Env -> Assign -> Err [StorageUpdate]
checkAssign env (AssignVal (StorageVar (StorageValue typ) name) expr)
  = case metaType typ of
    Integer -> do
      val <- checkInt env expr
      return [IntUpdate (DirectInt name) val]
    Boolean -> do
      val <- checkBool env expr
      return [BoolUpdate (DirectBool name) val]
    ByteStr -> do
      val <- checkBytes env expr
      return [BytesUpdate (DirectBytes name) val]
checkAssign env (AssignMany (StorageVar (StorageMapping (keyType :| _) valType) name) defns)
  = mapM (checkDefn env keyType valType name) defns
checkAssign _ (AssignVal (StorageVar (StorageMapping _ _) _) _)
  = Bad (nowhere, "Cannot assign a single expression to a composite type")
checkAssign _ (AssignMany (StorageVar (StorageValue _) _) _)
  = Bad (nowhere, "Cannot assign multiple values to an atomic type")
checkAssign _ _ = error $ "todo: support struct assignment in constructors"

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Env -> AbiType -> AbiType -> Id -> Defn -> Err StorageUpdate
checkDefn env keyType valType name (Defn k v) = case metaType keyType of
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
            return $ IntUpdate (MappedInt name (key :| [])) val
          Boolean -> do
            val <- checkBool env v
            return $ BoolUpdate (MappedBool name (key :| [])) val
          ByteStr -> do
            val <- checkBytes env v
            return $ BytesUpdate (MappedBytes name (key :| [])) val

checkPost :: Env -> Id -> Post -> Err (Map Id [Either StorageLocation StorageUpdate], Maybe ReturnExp)
checkPost env@(_, theirs, localVars) contract (Post maybeStorage extStorage maybeReturn) =
  do  returnexp <- mapM (inferExpr env) maybeReturn
      ourStorage <- case maybeStorage of
        Just entries -> checkEntries contract entries
        Nothing -> Ok []
      otherStorage <- checkStorages extStorage
      return $ ((Map.fromList $ (contract, ourStorage):otherStorage),
                 returnexp)
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
        checkStorages _ = error "TODO: check other storages"

checkStorageExpr :: Env -> Entry -> Expr -> Err StorageUpdate
checkStorageExpr env@(ours, _, _) (Entry p name ixs) expr =
    case Map.lookup name ours of
      Just (StorageValue t)  -> case metaType t of
          Integer -> IntUpdate (DirectInt name) <$> checkInt env expr
          Boolean -> BoolUpdate (DirectBool name) <$> checkBool env expr
          ByteStr -> BytesUpdate (DirectBytes name) <$> checkBytes env expr
      Just (StorageMapping argtyps  t) ->
        if length argtyps /= length ixs
        then Bad $ (p, "Argument mismatch for storageitem: " <> name)
        else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr env))
             in case metaType t of
                  Integer -> liftM2 (IntUpdate . MappedInt name) indexExprs (checkInt env expr)
                  Boolean -> liftM2 (BoolUpdate . MappedBool name) indexExprs (checkBool env expr)
                  ByteStr -> liftM2 (BytesUpdate . MappedBytes name) indexExprs (checkBytes env expr)
      Nothing -> Bad $ (p, "Unknown storage variable: " <> show name)
checkStorageExpr _ Wild _ = error "TODO: add support for wild storage to checkStorageExpr"

checkEntry :: Env -> Entry -> Err StorageLocation
checkEntry env@(ours, _, _) (Entry p name ixs) =
  case Map.lookup name ours of
    Just (StorageValue t) -> case metaType t of
          Integer -> Ok $ IntLoc (DirectInt name)
          Boolean -> Ok $ BoolLoc (DirectBool name)
          ByteStr -> Ok $ BytesLoc (DirectBytes name)
    Just (StorageMapping argtyps t) ->
      if length argtyps /= length ixs
      then Bad $ (p, "Argument mismatch for storageitem: " <> name)
      else let indexExprs = forM (NonEmpty.zip (head ixs :| tail ixs) argtyps) (uncurry (checkExpr env))
           in case metaType t of
                  Integer -> (IntLoc . MappedInt name) <$> indexExprs
                  Boolean -> (BoolLoc . MappedBool name) <$> indexExprs
                  ByteStr -> (BytesLoc . MappedBytes name) <$> indexExprs
    Nothing -> Bad $ (p, "Unknown storage variable: " <> show name)
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

bound :: AbiType -> (Exp Int) -> Exp Bool
bound typ e = And (LEQ (lowerBound typ) e) $ LEQ e (upperBound typ)

lowerBound :: AbiType -> Exp Int
lowerBound (AbiIntType a) = LitInt $ 0 - 2 ^ (a - 1)
-- todo: other negatives?
lowerBound _ = LitInt 0

--todo, the rest
upperBound :: AbiType -> Exp Int
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
inferExpr env@(ours, _,thisContext) expr =
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
    EntryExp p name e -> case (Map.lookup name ours, Map.lookup name thisContext) of
        (Nothing, Nothing) -> Bad (p, "Unknown variable: " <> show name)
        (Nothing, Just c) -> case c of
            Integer -> Ok . ExpInt $ IntVar name
            Boolean -> Ok . ExpBool $ BoolVar name
            ByteStr -> Ok . ExpBytes $ ByVar name
        (Just (StorageValue a), Nothing) ->
          case metaType a of
             Integer -> Ok . ExpInt $ TEntry (DirectInt name)
             Boolean -> Ok . ExpBool $ TEntry (DirectBool name)
             ByteStr -> Ok . ExpBytes $ TEntry (DirectBytes name)
        (Just (StorageMapping ts a), Nothing) ->
           let indexExprs = forM (NonEmpty.zip (head e :| tail e) ts)
                                     (uncurry (checkExpr env))
           in case metaType a of
             Integer -> ExpInt . TEntry . (MappedInt name) <$> indexExprs
             Boolean -> ExpBool . TEntry . (MappedBool name) <$> indexExprs
             ByteStr -> ExpBytes . TEntry . (MappedBytes name) <$> indexExprs
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

checkInt :: Env -> Expr -> Err (Exp Int)
checkInt env e =
  case inferExpr env e of
    Ok (ExpInt a) -> Ok a
    Ok (ExpBytes _) -> Bad (nowhere, "expected: int, got: bytes")
    Ok (ExpBool _) -> Bad (nowhere, "expected: int, got: bool")
    Bad err -> Bad err
