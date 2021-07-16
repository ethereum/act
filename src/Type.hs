{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}

module Type (typecheck, bound, lookupVars, defaultStore, metaType) where

import Data.List
import EVM.ABI
import EVM.Solidity (SlotType(..))
import Data.Map.Strict    (Map,keys,findWithDefault)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map -- abandon in favor of [(a,b)]?
import Data.Typeable hiding (typeRep)
import Type.Reflection (typeRep)

import Data.ByteString (ByteString)

import Control.Applicative
import Data.Traversable (for)
import Control.Monad

import Syntax
import Syntax.Timing
import Syntax.Untyped hiding (Post,Constant,Rewrite)
import qualified Syntax.Untyped as Untyped
import Syntax.Typed
import ErrM
import Parse

typecheck :: [RawBehaviour] -> Err [Claim]
typecheck behvs = do store <- lookupVars behvs
                     bs <- mapM (splitBehaviour store) behvs
                     return $ S store : join bs

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
  let e = [x | x `elem` xs]
  in e <> duplicates xs

-- | The type checking environment. 
data Env = Env
  { contract :: Id              -- ^ The name of the current contract.
  , store    :: Map Id SlotType -- ^ This contract's storage entry names and their types.
  , theirs   :: Store           -- ^ Mapping from contract names to a map of their entry names and their types.
  , calldata :: Map Id MType    -- ^ The calldata var names and their types.
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
  postcondition <- mapM (inferExpr env) posts
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
    flatten :: [Exp Bool Untimed] -> [Exp Bool Timed] -> Cases -> Err [Claim]
    flatten iff postc (Direct post) = do
      (p, maybeReturn) <- checkPost env post
      return $ splitCase name contract iface [] iff maybeReturn p postc
    flatten iff postc (Branches branches) = do
      branches' <- normalize branches
      cases' <- forM branches' $ \(Case _ cond post) -> do
        if' <- inferExpr env cond
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

  invariants <- mapM (inferExpr env) invs
  ensures <- mapM (inferExpr env) postcs

  let cases' = if null iffs' then [C $ Constructor contract Pass iface iffs' ensures stateUpdates []]
               else [ C $ Constructor contract Pass iface iffs' ensures stateUpdates []
                       , C $ Constructor contract Fail iface [Neg (mconcat iffs')] ensures [] []]

  return $ ((I . Invariant contract [] []) <$> invariants)
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
splitCase :: Id -> Id -> Interface -> [Exp Bool Untimed] -> [Exp Bool Untimed] -> Maybe (TypedExp Timed)
          -> [Rewrite] -> [Exp Bool Timed] -> [Claim]
splitCase name contract iface if' [] ret storage postcs =
  [ B $ Behaviour name Pass contract iface if' postcs storage ret ]
splitCase name contract iface if' iffs ret storage postcs =
  [ B $ Behaviour name Pass contract iface (if' <> iffs) postcs storage ret,
    B $ Behaviour name Fail contract iface (if' <> [Neg (mconcat iffs)]) [] (Constant . locFromRewrite <$> storage) Nothing ]

-- | Ensures that none of the storage variables are read in the supplied `Expr`.
noStorageRead :: Map Id SlotType -> Expr -> Err ()
noStorageRead store expr = forM_ (keys store) $ \name ->
  forM_ (findWithDefault [] name (idFromRewrites expr)) $ \pn ->
    Bad (pn,"Cannot read storage in creates block")

-- ensures that key types match value types in an Assign
checkAssign :: Env -> Assign -> Err [StorageUpdate]
checkAssign env@Env{contract, store} (AssignVal (StorageVar (StorageValue typ) name) expr) = do
  noStorageRead store expr
  case metaType typ of
    Integer -> return . IntUpdate   (IntItem contract name [])   <$> inferExpr env expr
    Boolean -> return . BoolUpdate  (BoolItem contract name [])  <$> inferExpr env expr
    ByteStr -> return . BytesUpdate (BytesItem contract name []) <$> inferExpr env expr
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
checkDefn env@Env{contract} keyType valType name (Defn k v) = do
  key <- case metaType keyType of
    Integer -> ExpInt   <$> inferExpr env k
    Boolean -> ExpBool  <$> inferExpr env k
    ByteStr -> ExpBytes <$> inferExpr env k
  case metaType valType of
    Integer -> IntUpdate   (IntItem   contract name [key]) <$> inferExpr env v
    Boolean -> BoolUpdate  (BoolItem  contract name [key]) <$> inferExpr env v
    ByteStr -> BytesUpdate (BytesItem contract name [key]) <$> inferExpr env v

checkPost :: Env -> Untyped.Post -> Err ([Rewrite], Maybe (TypedExp Timed))
checkPost env@Env{contract,calldata} (Untyped.Post maybeStorage extStorage maybeReturn) =
  do returnexp <- mapM (typedExp scopedEnv) maybeReturn
     ourStorage <- case maybeStorage of
       Just entries -> checkEntries contract entries
       Nothing -> Ok []
     otherStorage <- checkStorages extStorage
     return (ourStorage <> otherStorage, returnexp)
  where
    checkEntries :: Id -> [Untyped.Storage] -> Err [Rewrite]
    checkEntries name entries =
      forM entries $ \case
        Untyped.Constant loc -> Constant <$> checkPattern (focus name scopedEnv) loc
        Untyped.Rewrite loc val -> Rewrite <$> checkStorageExpr (focus name scopedEnv) loc val

    checkStorages :: [ExtStorage] -> Err [Rewrite]
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
        filtered = flip Map.mapWithKey (theirs env) $ \name vars ->
          if name == contract
            then Map.filterWithKey (\slot _ -> slot `elem` localNames) vars
            else Map.filterWithKey
                  (\slot _ -> slot `elem` Map.findWithDefault [] name externalNames)
                  vars

    focus :: Id -> Env -> Env
    focus name unfocused@Env{theirs} = unfocused
      { contract = name
      , store    = Map.findWithDefault mempty name theirs
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
checkStorageExpr _ (PWild _) _ = error "TODO: add support for wild storage to checkStorageExpr"
checkStorageExpr env@Env{contract,store} (PEntry p name ixs) expr = case Map.lookup name store of
  Just (StorageValue t)  -> makeUpdate t []
  Just (StorageMapping argtyps t) ->
    if length argtyps /= length ixs
      then Bad (p, "Argument mismatch for storageitem: " <> name)
      else makeUpdate t (NonEmpty.toList argtyps)
  Nothing -> Bad (p, "Unknown storage variable: " <> show name)
  where
    makeUpdate typ argtyps = do
      indexExprs <- for (ixs `zip` argtyps) (uncurry $ checkExpr env)
      case metaType typ of
        Integer -> IntUpdate (IntItem contract name indexExprs) <$> inferExpr env expr
        Boolean -> BoolUpdate (BoolItem contract name indexExprs) <$> inferExpr env expr
        ByteStr -> BytesUpdate (BytesItem contract name indexExprs) <$> inferExpr env expr

checkPattern :: Env -> Pattern -> Err StorageLocation
checkPattern env@Env{contract,store} (PEntry p name ixs) =
  case Map.lookup name store of
    Just (StorageValue t) -> case metaType t of
          Integer -> Ok . IntLoc   $ IntItem   contract name []
          Boolean -> Ok . BoolLoc  $ BoolItem  contract name []
          ByteStr -> Ok . BytesLoc $ BytesItem contract name []
    Just (StorageMapping argtyps t) ->
      if length argtyps /= length ixs
      then Bad (p, "Argument mismatch for storageitem: " <> name)
      else let indexExprs = for (ixs `zip` NonEmpty.toList argtyps) (uncurry $ checkExpr env)
           in case metaType t of
                  Integer -> (IntLoc . IntItem contract name) <$> indexExprs
                  Boolean -> (BoolLoc . BoolItem contract name) <$> indexExprs
                  ByteStr -> (BytesLoc . BytesItem contract name) <$> indexExprs
    Nothing -> Bad (p, "Unknown storage variable: " <> show name)
checkPattern _ (PWild _) = error "TODO: checkPattern for Wild storage"

checkIffs :: Env -> [IffH] -> Err [Exp Bool Untimed]
checkIffs env ((Iff _ exps):xs) = do
  hd <- mapM (inferExpr env) exps
  tl <- checkIffs env xs
  Ok $ hd <> tl
checkIffs env ((IffIn _ typ exps):xs) = do
  hd <- mapM (inferExpr env) exps
  tl <- checkIffs env xs
  Ok $ map (bound typ) hd <> tl
checkIffs _ [] = Ok []

bound :: AbiType -> Exp Integer t -> Exp Bool t
bound typ e = And (LEQ (lowerBound typ) e) $ LEQ e (upperBound typ)

lowerBound :: AbiType -> Exp Integer t
lowerBound (AbiIntType a) = IntMin a
-- todo: other negatives?
lowerBound _ = LitInt 0

-- todo, the rest
upperBound :: AbiType -> Exp Integer t
upperBound (AbiUIntType n) = UIntMax n
upperBound (AbiIntType n) = IntMax n
upperBound AbiAddressType = UIntMax 160
upperBound typ  = error $ "upperBound not implemented for " ++ show typ

-- | Attempt to construct a `TypedExp` whose type matches the supplied `AbiType`.
-- The target timing parameter will be whatever is required by the caller.
checkExpr :: Typeable t => Env -> Expr -> AbiType -> Err (TypedExp t)
checkExpr env e typ = case metaType typ of
  Integer -> ExpInt <$> inferExpr env e
  Boolean -> ExpBool <$> inferExpr env e
  ByteStr -> ExpBytes <$> inferExpr env e

-- | Attempt to typecheck an untyped expression as any possible type.
typedExp :: Typeable t => Env -> Expr -> Err (TypedExp t)
typedExp env e = ExpInt   <$> inferExpr env e
             <|> ExpBool  <$> inferExpr env e
             <|> ExpBytes <$> inferExpr env e
             <|> Bad (getPosn e, "TypedExp: no suitable type") -- TODO improve error handling once we've merged the unified stuff!

-- | Attempts to construct an expression with the type and timing required by
-- the caller. If this is impossible, an error is thrown instead.
inferExpr :: forall a t. (Typeable a, Typeable t) => Env -> Expr -> Err (Exp a t)
inferExpr env@Env{contract,store,calldata} expr = case expr of
  ENot    p v1    -> check p $ Neg  <$> inferExpr env v1
  EAnd    p v1 v2 -> check p $ And  <$> inferExpr env v1 <*> inferExpr env v2
  EOr     p v1 v2 -> check p $ Or   <$> inferExpr env v1 <*> inferExpr env v2
  EImpl   p v1 v2 -> check p $ Impl <$> inferExpr env v1 <*> inferExpr env v2
  EEq     p v1 v2 -> polycheck p Eq v1 v2
  ENeq    p v1 v2 -> polycheck p NEq v1 v2
  ELT     p v1 v2 -> check p $ LE   <$> inferExpr env v1 <*> inferExpr env v2
  ELEQ    p v1 v2 -> check p $ LEQ  <$> inferExpr env v1 <*> inferExpr env v2
  EGEQ    p v1 v2 -> check p $ GEQ  <$> inferExpr env v1 <*> inferExpr env v2
  EGT     p v1 v2 -> check p $ GE   <$> inferExpr env v1 <*> inferExpr env v2
  EAdd    p v1 v2 -> check p $ Add  <$> inferExpr env v1 <*> inferExpr env v2
  ESub    p v1 v2 -> check p $ Sub  <$> inferExpr env v1 <*> inferExpr env v2
  EMul    p v1 v2 -> check p $ Mul  <$> inferExpr env v1 <*> inferExpr env v2
  EDiv    p v1 v2 -> check p $ Div  <$> inferExpr env v1 <*> inferExpr env v2
  EMod    p v1 v2 -> check p $ Mod  <$> inferExpr env v1 <*> inferExpr env v2
  EExp    p v1 v2 -> check p $ Exp  <$> inferExpr env v1 <*> inferExpr env v2
  IntLit  p v1    -> check p . pure $ LitInt v1
  BoolLit p v1    -> check p . pure $ LitBool v1
  EITE    _ v1 v2 v3 -> ITE <$> inferExpr env v1 <*> inferExpr env v2 <*> inferExpr env v3
  EUTEntry   p name es -> entry p Neither name es
  EPreEntry  p name es -> entry p Pre     name es
  EPostEntry p name es -> entry p Post    name es
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
    -- Try to cast the type parameter of an expression to the goal of `inferExpr`.
    -- The cast only succeeds if they already are the same.
    check :: forall x. Typeable x => Pn -> Err (Exp x t) -> Err (Exp a t)
    check pn e =
      errMessage (pn,"Type mismatch. Expected " <> show (typeRep @a) <> ", got " <> show (typeRep @x) <> ".")
        =<< castType <$> e

    -- Takes a polymorphic binary AST constructor and specializes it to each of
    -- our types. Those specializations are used in order to guide the
    -- typechecking of the two supplied expressions. Returns at first success.
    polycheck :: Typeable x => Pn -> (forall y. (Eq y, Typeable y) => Exp y t -> Exp y t -> Exp x t) -> Expr -> Expr -> Err (Exp a t)
    polycheck pn cons e1 e2 = check pn (cons @Integer    <$> inferExpr env e1 <*> inferExpr env e2)
                          <|> check pn (cons @Bool       <$> inferExpr env e1 <*> inferExpr env e2)
                          <|> check pn (cons @ByteString <$> inferExpr env e1 <*> inferExpr env e2)
                          <|> Bad (pn, "Couldn't harmonize types!") -- TODO improve error handling once we've merged the unified stuff!

    -- Try to construct a reference to a calldata variable or an item in storage.
    entry :: Typeable t0 => Pn -> Time t0 -> Id -> [Expr] -> Err (Exp a t)
    entry pn timing name es = case (Map.lookup name store, Map.lookup name calldata) of
      (Nothing, Nothing) -> Bad (pn, "Unknown variable: " <> name)
      (Just _, Just _)   -> Bad (pn, "Ambiguous variable: " <> name)
      (Nothing, Just c) -> if isTimed timing then Bad (pn, "Calldata var cannot be pre/post.") else case c of
        -- Create a calldata reference and typecheck it as with normal expressions.
        Integer -> check pn . pure $ IntVar  name
        Boolean -> check pn . pure $ BoolVar name
        ByteStr -> check pn . pure $ ByVar   name
      (Just (StorageValue a), Nothing)      -> makeEntry a []
      (Just (StorageMapping ts a), Nothing) -> makeEntry a $ NonEmpty.toList ts
      where
        makeEntry :: AbiType -> [AbiType] -> Err (Exp a t)
        makeEntry a ts = case metaType a of
          Integer -> makeItem IntItem
          Boolean -> makeItem BoolItem
          ByteStr -> makeItem BytesItem
          where
            -- Given that the indices used in the expression agree with the storage,
            -- create a `TStorageItem` using the supplied constructor, place it
            -- in a `TEntry` and then attempt to cast its timing parameter to the
            -- target timing of `inferExpr`. Finally, `check` the type parameter as
            -- with all other expressions.
            makeItem :: Typeable x => (forall t0. Id -> Id -> [TypedExp t0] -> TStorageItem x t0) -> Err (Exp a t)
            makeItem maker = do
              when (length ts /= length es) $ Bad (pn, "Index mismatch for entry!")
              ixs <- for (es `zip` ts) (uncurry $ checkExpr env)
              check pn
                $ errMessage (pn, (tail . show $ typeRep @t) <> " variable needed here!")
                $ castTime (TEntry (maker contract name ixs) timing)
