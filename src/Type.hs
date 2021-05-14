{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Type (typecheck, bound, lookupVars, defaultStore, metaType) where

import Data.List
import EVM.ABI
import EVM.Solidity (SlotType(..))
import Data.Map.Strict    (Map,keys,findWithDefault)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map -- abandon in favor of [(a,b)]?

import Data.ByteString (ByteString)

import Control.Monad

import Syntax hiding (Storage)
import qualified Syntax
import ErrM
import Parse
import Extract
import RefinedAst
import Print (prettyType)

typecheck :: [RawBehaviour] -> Err [Claim]
typecheck behvs = do store <- lookupVars behvs
                     bs <- mapM (splitBehaviour store) behvs
                     return $ (S store):(join bs)

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Err Store
lookupVars ((Transition {}):bs) = lookupVars bs
lookupVars ((Definition contract _ _ (Creates assigns) _ _ _):bs) =
  let assignments = fromAssign <$> assigns
  in case duplicates $ fst <$> assignments of
        [] ->
          let new' = Map.singleton contract (Map.fromList assignments)
           in do old <- lookupVars bs
                 if null (Map.intersection new' old)
                 then pure $ new' <> old
                 else Bad (nowhere, "Multiple definitions given of contract: " <> contract)
        vs -> Bad (nowhere,
                   concatMap (\v -> "Multiple definitions given of state variable: " <> v <> "\n") vs)
lookupVars [] = pure mempty

fromAssign :: Assign -> (Id, SlotType)
fromAssign (AssignVal (StorageVar typ var) _) = (var, typ)
fromAssign (AssignMany (StorageVar typ var) _) = (var, typ)
fromAssign (AssignStruct _ _) = error "TODO: assignstruct"

-- | filters out duplicate entries in list
duplicates :: Eq a => [a] -> [a]
duplicates [] = []
duplicates (x:xs) =
  let e = ([x | x `elem` xs])
  in e <> duplicates xs

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
splitBehaviour store (Transition name contract iface@(Interface _ decls) iffs' cases posts) = do
  -- constrain integer calldata variables (TODO: other types)
  iff <- checkIffs env iffs'
  postcondition <- mapM (\expr -> checkBool (getPosn expr) env expr) posts
  flatten iff postcondition cases
  where
    env :: Env
    env = mkEnv contract store decls

    -- translate wildcards into negation of other cases
    normalize :: [Case] -> Err [Case]
    normalize cases' =
      let wildcard (Case _ (WildExp _) _) = True
          wildcard _ = False
      in case findIndex wildcard cases' of
        Nothing -> return $ snd $ mapAccumL checkCase (BoolLit nowhere False) cases'
        Just ind ->
          -- wildcard must be last element
          if ind < length cases' - 1
          then case cases' !! ind of
            (Case p _ _) -> Bad (p, "Wildcard pattern must be last case")
          else return $ snd $ mapAccumL checkCase (BoolLit nowhere False) cases'

    checkCase :: Expr -> Case -> (Expr, Case)
    checkCase acc (Case p (WildExp _) post) =
      (error "wildcard not last case",
        Case p (ENot nowhere acc) post)
    checkCase acc (Case p e post) = (EOr nowhere e acc, Case p e post)


    -- flatten case list
    flatten :: [Exp Bool] -> [Exp Bool] -> Cases -> Err [Claim]
    flatten iff postc (Direct post) = do
      (p, maybeReturn) <- checkPost env post
      return $ splitCase name contract iface [] iff maybeReturn p postc
    flatten iff postc (Branches branches) = do
      branches' <- normalize branches
      cases' <- forM branches' $ \(Case _ cond post) -> do
        if' <- checkBool (getPosn cond) env cond
        (post', ret) <- checkPost env post
        return (if', post', ret)

      pure $
        (\(ifcond, stateUpdates, ret)
            -> splitCase name contract iface [ifcond] iff ret stateUpdates postc)
           =<< cases'

splitBehaviour store (Definition contract iface@(Interface _ decls) iffs (Creates assigns) extStorage postcs invs) = do
  unless (null extStorage) $ error "TODO: support extStorage in constructor"

  let env = mkEnv contract store decls
  stateUpdates <- concat <$> mapM (checkAssign env) assigns
  iffs' <- checkIffs env iffs

  invariants <- mapM (\expr -> checkBool (getPosn expr) env expr) invs
  ensures <- mapM (\expr -> checkBool (getPosn expr) env expr) postcs

  let cases' = if null iffs' then [C $ Constructor contract Pass iface iffs' ensures stateUpdates []]
               else [ C $ Constructor contract Pass iface iffs' ensures stateUpdates []
                       , C $ Constructor contract Fail iface [Neg (mconcat iffs')] ensures [] []]

  return $ ((I . (Invariant contract [] [])) <$> invariants)
           <> cases'

mkEnv :: Id -> Store -> [Decl]-> Env
mkEnv contract store decls = (contract, fromMaybe mempty (Map.lookup contract store), store, abiVars)
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- | split case into pass and fail case
splitCase :: Id -> Id -> Interface -> [Exp Bool] -> [Exp Bool] -> Maybe ReturnExp
          -> [Either StorageLocation StorageUpdate] -> [Exp Bool] -> [Claim]
splitCase name contract iface if' [] ret storage postcs =
  [ B $ Behaviour name Pass contract iface if' postcs storage ret ]
splitCase name contract iface if' iffs ret storage postcs =
  [ B $ Behaviour name Pass contract iface (if' <> iffs) postcs storage ret,
    B $ Behaviour name Fail contract iface (if' <> [Neg (mconcat iffs)]) [] (Left . getLoc <$> storage) Nothing ]

-- | Ensures that no of the storage variables are read in the supplied `Expr`.
noStorageRead :: Map Id SlotType -> Expr -> Err ()
noStorageRead store expr = forM_ (keys store) $ \name ->
  forM_ (findWithDefault [] name (getIds expr)) $ \pn ->
    Bad (pn,"Cannot read storage in creates block")
  
-- ensures that key types match value types in an Assign
checkAssign :: Env -> Assign -> Err [StorageUpdate]
checkAssign env@(contract, store, _, _) (AssignVal (StorageVar (StorageValue typ) name) expr)
  = noStorageRead store expr >>
  case metaType typ of
    Integer -> do
      val <- checkInt (getPosn expr) env expr
      return [IntUpdate (DirectInt contract name) val]
    Boolean -> do
      val <- checkBool (getPosn expr) env expr
      return [BoolUpdate (DirectBool contract name) val]
    ByteStr -> do
      val <- checkBytes (getPosn expr) env expr
      return [BytesUpdate (DirectBytes contract name) val]
checkAssign env@(_, store, _, _) (AssignMany (StorageVar (StorageMapping (keyType :| _) valType) name) defns)
  = forM defns $ \def@(Defn e1 e2) -> do
      mapM_ (noStorageRead store) [e1,e2]
      checkDefn env keyType valType name def
checkAssign _ (AssignVal (StorageVar (StorageMapping _ _) _) expr)
  = Bad (getPosn expr, "Cannot assign a single expression to a composite type")
checkAssign _ (AssignMany (StorageVar (StorageValue _) _) _)
  = Bad (nowhere, "Cannot assign multiple values to an atomic type")
checkAssign _ _ = error "todo: support struct assignment in constructors"

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Env -> AbiType -> AbiType -> Id -> Defn -> Err StorageUpdate
checkDefn env@(contract, _, _, _) keyType valType name (Defn k v) = case metaType keyType of
    Integer -> do
      key <- checkInt (getPosn k) env k
      checkVal (ExpInt key)
    Boolean -> do
      key <- checkBool (getPosn k) env k
      checkVal (ExpBool key)
    ByteStr -> do
      key <- checkBytes (getPosn k) env k
      checkVal (ExpBytes key)
    where
      checkVal key = do
        case metaType valType of
          Integer -> do
            val <- checkInt (getPosn v) env v
            return $ IntUpdate (MappedInt contract name (key :| [])) val
          Boolean -> do
            val <- checkBool (getPosn v) env v
            return $ BoolUpdate (MappedBool contract name (key :| [])) val
          ByteStr -> do
            val <- checkBytes (getPosn v) env v
            return $ BytesUpdate (MappedBytes contract name (key :| [])) val

checkPost :: Env -> Post -> Err ([Either StorageLocation StorageUpdate], Maybe ReturnExp)
checkPost (contract, _, theirs, calldata) (Post maybeStorage extStorage maybeReturn) =
  do returnexp <- mapM (inferExpr scopedEnv) maybeReturn
     ourStorage <- case maybeStorage of
       Just entries -> checkEntries contract entries
       Nothing -> Ok []
     otherStorage <- checkStorages extStorage
     return (ourStorage <> otherStorage, returnexp)
  where
    checkEntries :: Id -> [Syntax.Storage] -> Err [Either StorageLocation StorageUpdate]
    checkEntries name entries =
      forM entries $ \case
        Constant loc -> Left <$> checkPattern (focus name scopedEnv) loc
        Rewrite loc val -> Right <$> checkStorageExpr (focus name scopedEnv) loc val

    checkStorages :: [ExtStorage] -> Err [Either StorageLocation StorageUpdate]
    checkStorages [] = Ok []
    checkStorages ((ExtStorage name entries):xs) = do p <- checkEntries name entries
                                                      ps <- checkStorages xs
                                                      Ok $ p <> ps
    checkStorages _ = error "TODO: check other storages"

    -- remove storage items from the env that are not mentioned on the LHS of a storage declaration
    scopedEnv :: Env
    scopedEnv = focus contract (mempty, mempty, filtered, calldata)
      where
        filtered = Map.mapWithKey (\name vars ->
            if (name == contract)
            then Map.filterWithKey (\slot _ -> slot `elem` localNames) vars
            else Map.filterWithKey (\slot _ -> slot `elem` (fromMaybe mempty $ Map.lookup name externalNames)) vars
          ) theirs

    focus :: Id -> Env -> Env
    focus name (_, _, theirs', calldata') =
      (name, fromMaybe mempty (Map.lookup name theirs'), theirs', calldata')

    localNames :: [Id]
    localNames = nameFromStorage <$> fromMaybe mempty maybeStorage

    externalNames :: Map Id [Id]
    externalNames = Map.fromList $ mapMaybe (\case
        ExtStorage name storages -> Just (name, nameFromStorage <$> storages)
        ExtCreates {} -> error "TODO: handle ExtCreate"
        WildStorage -> Nothing
      ) extStorage

checkStorageExpr :: Env -> Pattern -> Expr -> Err StorageUpdate
checkStorageExpr env@(contract, ours, _, _) (PEntry p name ixs) expr =
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
checkStorageExpr _ (PWild _) _ = error "TODO: add support for wild storage to checkStorageExpr"

checkPattern :: Env -> Pattern -> Err StorageLocation
checkPattern env@(contract, ours, _, _) (PEntry p name ixs) =
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
checkPattern _ (PWild _) = error "TODO: checkPattern for Wild storage"

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
      boolbytesbytes p op v1 v2 = do w1 <- checkBytes p env v1
                                     w2 <- checkBytes p env v2
                                     Ok $ ExpBool $ op w1 w2
      entry pn name es = case (Map.lookup name ours, Map.lookup name thisContext) of
        (Nothing, Nothing) -> Bad (pn, "Unknown variable: " <> name)
        (Nothing, Just c) -> case c of
          Integer -> Ok . ExpInt $ IntVar name
          Boolean -> Ok . ExpBool $ BoolVar name
          ByteStr -> Ok . ExpBytes $ ByVar name
        (Just (StorageValue a), Nothing) -> case metaType a of
          Integer -> Ok . ExpInt $ TEntry (DirectInt contract name)
          Boolean -> Ok . ExpBool $ TEntry (DirectBool contract name)
          ByteStr -> Ok . ExpBytes $ TEntry (DirectBytes contract name)
        (Just (StorageMapping ts a), Nothing) ->
           let indexExprs = forM (NonEmpty.zip (head es :| tail es) ts)
                                     (uncurry (checkExpr pn env))
           in case metaType a of
             Integer -> ExpInt . TEntry . (MappedInt contract name) <$> indexExprs
             Boolean -> ExpBool . TEntry . (MappedBool contract name) <$> indexExprs
             ByteStr -> ExpBytes . TEntry . (MappedBytes contract name) <$> indexExprs
        (Just _, Just _) -> Bad (pn, "Ambiguous variable: " <> show name)

  in case expr of
    ENot p  v1    -> ExpBool . Neg <$> checkBool p env v1
    EAnd p  v1 v2 -> boolboolbool p And  v1 v2
    EOr p   v1 v2 -> boolboolbool p Or   v1 v2
    EImpl p v1 v2 -> boolboolbool p Impl v1 v2
    EEq p   v1 v2 -> do
      l <- inferExpr env v1
      r <- inferExpr env v2
      case (l, r) of
        (ExpInt _, ExpInt _) -> boolintint p Eq v1 v2
        (ExpBool _, ExpBool _) -> boolboolbool p Eq v1 v2
        (ExpBytes _, ExpBytes _) -> boolbytesbytes p Eq v1 v2
        (_, _) -> Bad (p, "mismatched types: " <> prettyType l <> " == " <> prettyType r)
    ENeq p  v1 v2 -> boolintint  p NEq v1 v2
    ELT p   v1 v2 -> boolintint  p LE   v1 v2
    ELEQ p  v1 v2 -> boolintint  p LEQ  v1 v2
    EGEQ p  v1 v2 -> boolintint  p GEQ  v1 v2
    EGT p   v1 v2 -> boolintint  p GE   v1 v2
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
    IntLit _ n  -> Ok $ ExpInt $ LitInt n
    BoolLit _ n -> Ok $ ExpBool $ LitBool n
    EntryExp p x e  -> entry p x e
    PreEntry p x e  -> entry p x e
    PostEntry p x e -> entry p x e
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
