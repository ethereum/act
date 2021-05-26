{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language KindSignatures #-}
{-# Language ImplicitParams #-}
{-# Language NamedFieldPuns #-}
{-# Language BlockArguments #-}
{-# Language TypeOperators #-}

module Type (typecheck, bound, lookupVars, defaultStore, metaType) where

import Data.List
import EVM.ABI
import EVM.Solidity (SlotType(..))
import Data.Map.Strict    (Map,keys,findWithDefault)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map -- abandon in favor of [(a,b)]?
import Data.Type.Equality
import Data.Typeable
import Data.Functor (($>))

import Data.Coerce (coerce)

import Data.ByteString (ByteString)

import Control.Applicative
import Data.Traversable (for)
import Control.Monad

import Syntax hiding (Storage,Post)
import qualified Syntax
import ErrM
import Parse
import Extract
import RefinedAst
import Print -- (prettyType)

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

data Env = Env
  { contract :: Id
  , store    :: Map Id SlotType
  , theirs   :: Store
  , calldata :: Map Id MType
  }

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
    flatten :: [Exp Untimed Bool] -> [Exp Timed Bool] -> Cases -> Err [Claim]
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
mkEnv contract store decls = Env
  { contract = contract
  , store    = fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = abiVars
  }
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- | split case into pass and fail case
splitCase :: Id -> Id -> Interface -> [Exp Untimed Bool] -> [Exp Untimed Bool] -> Maybe ReturnExp
          -> [Either StorageLocation StorageUpdate] -> [Exp Timed Bool] -> [Claim]
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
checkAssign env@Env{contract, store} (AssignVal (StorageVar (StorageValue typ) name) expr)
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
checkAssign env@Env{store} (AssignMany (StorageVar (StorageMapping (keyType :| _) valType) name) defns)
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
checkDefn env@Env{contract} keyType valType name (Defn k v) = case metaType keyType of
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

checkPost :: Env -> Syntax.Post -> Err ([Either StorageLocation StorageUpdate], Maybe ReturnExp)
checkPost Env{contract,theirs,calldata} (Syntax.Post maybeStorage extStorage maybeReturn) =
  do returnexp <- mapM undefined {- (fmap returnExp . inferExpr scopedEnv) -} maybeReturn
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
    scopedEnv = focus contract $ Env
      { contract = mempty
      , store    = mempty
      , theirs   = filtered
      , calldata = calldata
      }
      where
        filtered = Map.mapWithKey (\name vars ->
            if (name == contract)
            then Map.filterWithKey (\slot _ -> slot `elem` localNames) vars
            else Map.filterWithKey (\slot _ -> slot `elem` (fromMaybe mempty $ Map.lookup name externalNames)) vars
          ) theirs

    focus :: Id -> Env -> Env
    focus name Env{theirs,calldata} = Env
      { contract = name
      , store    = fromMaybe mempty (Map.lookup name theirs)
      , theirs   = theirs
      , calldata = calldata
      }

    localNames :: [Id]
    localNames = nameFromStorage <$> fromMaybe mempty maybeStorage

    externalNames :: Map Id [Id]
    externalNames = Map.fromList $ mapMaybe (\case
        ExtStorage name storages -> Just (name, nameFromStorage <$> storages)
        ExtCreates {} -> error "TODO: handle ExtCreate"
        WildStorage -> Nothing
      ) extStorage

checkStorageExpr :: Env -> Pattern -> Expr -> Err StorageUpdate
checkStorageExpr env@Env{contract,store} (PEntry p name ixs) expr =
    case Map.lookup name store of
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
checkPattern env@Env{contract,store} (PEntry p name ixs) =
  case Map.lookup name store of
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

checkIffs :: Env -> [IffH] -> Err [Exp Untimed Bool]
checkIffs env ((Iff p exps):xs) = do
  hd <- mapM (checkBool p env) exps
  tl <- checkIffs env xs
  Ok $ hd <> tl
checkIffs env ((IffIn p typ exps):xs) = do
  hd <- mapM (checkInt p env) exps
  tl <- checkIffs env xs
  Ok $ map (bound typ) hd <> tl
checkIffs _ [] = Ok []

bound :: AbiType -> Exp time Integer -> Exp time Bool
bound typ e = And (LEQ (lowerBound typ) e) $ LEQ e (upperBound typ)

lowerBound :: AbiType -> Exp time Integer
lowerBound (AbiIntType a) = IntMin a
-- todo: other negatives?
lowerBound _ = LitInt 0

-- todo, the rest
upperBound :: AbiType -> Exp time Integer
upperBound (AbiUIntType n) = UIntMax n
upperBound (AbiIntType n) = IntMax n
upperBound AbiAddressType = UIntMax 160
upperBound typ  = error $ "upperBound not implemented for " ++ show typ

checkExpr :: Pn -> Env -> Expr -> AbiType -> Err ReturnExp
checkExpr p env e typ = case metaType typ of
  Integer -> ExpInt <$> checkInt p env e
  Boolean -> ExpBool <$> checkBool p env e
  ByteStr -> ExpBytes <$> checkBytes p env e

inferExpr :: (Typeable a, Typeable time) => Env -> Expr -> Err (Exp time a)
inferExpr env e = inferExpr' Proxy Proxy env e 

inferExpr' :: forall t a. (Typeable t, Typeable a) => Proxy t -> Proxy a -> Env -> Expr -> Err (Exp t a)
inferExpr' expectedTime expectedType env@Env{contract,store,calldata} expr =
  case expr of
    ENot p  v1       -> check p $ inferExpr @Bool env v1
    EAnd p  v1 v2    -> check p $ And  <$> inferExpr env v1 <*> inferExpr env v2
    EOr p   v1 v2    -> check p $ Or   <$> inferExpr env v1 <*> inferExpr env v2
    EImpl p v1 v2    -> check p $ Impl <$> inferExpr env v1 <*> inferExpr env v2
    EEq p   v1 v2    -> polycheck p Eq v1 v2
    ENeq p  v1 v2    -> polycheck p NEq v1 v2
    ELT p   v1 v2    -> check p $ LE   <$> inferExpr env v1 <*> inferExpr env v2
    ELEQ p  v1 v2    -> check p $ LEQ  <$> inferExpr env v1 <*> inferExpr env v2
    EGEQ p  v1 v2    -> check p $ GEQ  <$> inferExpr env v1 <*> inferExpr env v2
    EGT p   v1 v2    -> check p $ GE   <$> inferExpr env v1 <*> inferExpr env v2
    EITE p  v1 v2 v3 -> ITE <$> inferExpr env v1 <*> inferExpr env v2 <*> inferExpr env v3
    EAdd p  v1 v2    -> check p $ Add  <$> inferExpr env v1 <*> inferExpr env v2
    ESub p  v1 v2    -> check p $ Sub  <$> inferExpr env v1 <*> inferExpr env v2
    EMul p  v1 v2    -> check p $ Mul  <$> inferExpr env v1 <*> inferExpr env v2
    EDiv p  v1 v2    -> check p $ Div  <$> inferExpr env v1 <*> inferExpr env v2
    EMod p  v1 v2    -> check p $ Mod  <$> inferExpr env v1 <*> inferExpr env v2
    EExp p  v1 v2    -> check p $ Exp  <$> inferExpr env v1 <*> inferExpr env v2
    IntLit p     n   -> check p . pure $ LitInt n
    BoolLit p    n   -> check p . pure $ LitBool n
    EUTEntry p   name es -> entry p Nothing name es
    EPreEntry p  name es -> entry p (Just Pre) name es
    EPostEntry p name es -> entry p (Just Post) name es
    EnvExp p v1 -> case lookup v1 defaultStore of
      Just Integer -> check p . pure $ IntEnv v1
      Just ByteStr -> check p . pure $ ByEnv  v1
      _            -> Bad (p, "unknown environment variable: " <> show v1)
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
  where
    check :: (Typeable x)
           => Pn -> Err (Exp t x) -> Err (Exp t a)
    check pn e = leaf Proxy pn =<< e
      where
        -- TODO use `errMessage` here and probably integrate into `check`
        leaf :: Typeable x => Proxy x -> Pn -> Exp t x -> Err (Exp t a)
        leaf actual pn e = maybe
          (Bad (pn,"Type mismatch. Expected " <> show (typeRep expectedType) <> ", got " <> show (typeRep actual)))
          pure
          (gcast e)

    polycheck :: Typeable x
               => Pn -> (forall y. (Eq y, Typeable y) => Exp t y -> Exp t y -> Exp t x) -> Expr -> Expr -> Err (Exp t a)
    polycheck pn cons e1 e2 =
          check pn (cons @Integer    <$> inferExpr env e1 <*> inferExpr env e2)
      <|> check pn (cons @Bool       <$> inferExpr env e1 <*> inferExpr env e2)
      <|> check pn (cons @ByteString <$> inferExpr env e1 <*> inferExpr env e2)
      <|> Bad (pn, "polybranch error")

    entry :: Pn -> Maybe Timing -> Id -> [Expr] -> Err (Exp t a)
    entry pn timing name es =
      let
        makeVar :: Typeable x => (Id -> Exp Untimed x) -> (Id -> Timing -> Exp Timed x) -> Err (Exp t a)
        makeVar untimed timed = check pn
                                $ errMessage (pn, "makeVar error: mismatched times")
                                $ maybe (gcast0 $ untimed name) (gcast0 . timed name) timing

        makeEntry :: Typeable x => (Id -> Id -> TStorageItem x) -> Err (Exp t a)
        makeEntry maker = makeVar (UTEntry . maker contract) (TEntry . maker contract)
      in
      case (Map.lookup name store, Map.lookup name calldata) of
        (Nothing, Nothing) -> Bad (pn, "Unknown variable: " <> name)
        (Just _, Just _)   -> Bad (pn, "Ambiguous variable: " <> name)   
        (Nothing, Just c) -> case c of
          Integer -> makeVar UTIntVar  TIntVar
          Boolean -> makeVar UTBoolVar TBoolVar
          ByteStr -> makeVar UTByVar   TByVar
        (Just (StorageValue a), Nothing) -> case metaType a of
          Integer -> makeEntry DirectInt  
          Boolean -> makeEntry DirectBool 
          ByteStr -> makeEntry DirectBytes
        (Just (StorageMapping ts a), Nothing) ->
          let
            indexExprs = for (NonEmpty.zip (head es :| tail es) ts)
                             (uncurry (checkExpr pn env))
  
            makeMapping :: Typeable x => (Id -> Id -> NonEmpty ReturnExp -> TStorageItem x) -> Err (Exp t a)
            makeMapping maker = do
              ixs <- indexExprs
              makeEntry (\c x -> maker c x ixs)
          in
          case metaType a of
            Integer -> makeMapping MappedInt
            Boolean -> makeMapping MappedBool
            ByteStr -> makeMapping MappedBytes

checkBool :: Typeable time => Pn -> Env -> Expr -> Err (Exp time Bool)
checkBool p env e = inferExpr env e
--  case inferExpr env e of
--    Ok (EInt _) -> Bad (p, "expected: bool, got: int")
--    Ok (EBy _) -> Bad (p, "expected: bool, got: bytes")
--    Ok (EBool a) -> Ok a
--    Bad err -> Bad err
--  where
--    p = getPosn e

checkBytes :: Typeable time => Pn -> Env -> Expr -> Err (Exp time ByteString)
checkBytes p env e = inferExpr env e
--  case inferExpr env e of
--    Ok (EInt _) -> Bad (p, "expected: bytes, got: int")
--    Ok (EBy a) -> Ok a
--    Ok (EBool _) -> Bad (p, "expected: bytes, got: bool")
--    Bad err -> Bad err

checkInt :: Typeable time => Pn -> Env -> Expr -> Err (Exp time Integer)
checkInt p env e = inferExpr env e
--  case inferExpr env e of
--    Ok (EInt a) -> Ok a
--    Ok (EBy _) -> Bad (p, "expected: int, got: bytes")
--    Ok (EBool _) -> Bad (p, "expected: int, got: bool")
--    Bad err -> Bad err

returnExp :: Typeable a => Exp Untimed a -> ReturnExp
returnExp (e :: Exp Untimed a) = fromMaybe (error "returnExp: no suitable type")
  $   pure ExpInt   <*> cast e
  <|> pure ExpBool  <*> cast e
  <|> pure ExpBytes <*> cast e

prettyType :: (Typeable a, Typeable t) => Exp t a -> String
prettyType = show . last . typeRepArgs . typeRep

checkTimed :: (Typeable t, Typeable time', Typeable time) => Pn -> Exp (time :: TimeType) t -> Err (Exp (time' :: TimeType) t)
checkTimed pn (e :: Exp time t) = case cast e of
    Just e' -> Ok e'
    Nothing -> Bad (pn, "Bad timing of expression")

gcast0 :: forall t t' a. (Typeable t, Typeable t')
       => t a -> Maybe (t' a)
gcast0 x = fmap (\Refl -> x) (eqT :: Maybe (t :~: t'))

(.:) f g a b = f (g a b)