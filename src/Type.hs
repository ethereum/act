{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}
{-# LANGUAGE ApplicativeDo, OverloadedLists #-}

module Type (typecheck, bound, lookupVars, defaultStore, metaType, Err) where

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
import Control.Monad (join,unless)
import Control.Monad.Writer
import Data.List.Extra (unsnoc)
import Data.Functor
import Data.Functor.Alt
import Data.Foldable
import Data.Traversable

import Data.Singletons

import Syntax
import Syntax.Timing
import Syntax.Untyped hiding (Post,Constant,Rewrite)
import qualified Syntax.Untyped as Untyped
import Syntax.Typed
import ErrorLogger
import Parse

type Err a = Error TypeErr a

type TypeErr = String

typecheck :: [RawBehaviour] -> Err [Claim]
typecheck behvs = logErrs (lookupVars behvs) $ \store -> do
  bs <- traverse (splitBehaviour store) behvs
  pure $ S store : concat bs

--typecheck' :: [RawBehaviour] -> ErrorLogger TypeErr [Claim]
--typecheck' behvs = logErrs (lookupVars behvs) $ \store -> do
--  bs <- traverse (splitBehaviour store) behvs
--  pure $ S store : concat bs

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Logger TypeErr Store
lookupVars ((Transition {}):bs) = lookupVars bs
lookupVars ((Definition pn contract _ _ (Creates assigns) _ _ _):bs) = do
  let assignments = Map.fromListWith (<>) $ fromAssign <$> assigns

  allVars <- lookupVars bs
  newVars <- flip Map.traverseWithKey assignments $ \var ((p,typ) :| rest) -> pure typ
                      <* for rest (\(pn,_) ->
                            log' (pn, var <> " already defined at " <> showposn p <> "."))

  if contract `Map.member` allVars
    then allVars <$ log' (pn, "Conflicting definitions for " <> contract <> ".")
    else pure $ Map.insert contract newVars allVars
lookupVars [] = pure mempty

fromAssign :: Assign -> (Id, NonEmpty (Pn, SlotType))
fromAssign (AssignVal (StorageVar pn typ var) _) = (var, [(pn, typ)])
fromAssign (AssignMany (StorageVar pn typ var) _) = (var, [(pn, typ)])
fromAssign (AssignStruct _ _) = error "TODO: assignstruct"

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
   (Blockhash, Integer),
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
splitBehaviour store (Transition pn name contract iface@(Interface _ decls) iffs' cases posts) = do
  -- constrain integer calldata variables (TODO: other types)
  checkIffs env iffs' >>=? \iff ->
  traverse (inferExpr env) posts >>=? \postcondition ->
  flatten iff postcondition cases
  where
    env :: Env
    env = mkEnv contract store decls

    -- translate wildcards into negation of other cases
    normalize :: [Case] -> Logger TypeErr [Case]
    normalize []     = pure []
    normalize cases' =
      let 
        Just (rest, Case p _ post) = unsnoc cases'
        (wilds,nowilds) = partition wildcard rest
        normalized = flip (Case p) post $ foldl (\acc (Case nowhere e _) -> EOr nowhere e acc) (BoolLit nowhere False) nowilds
      in
        normalized:rest <$ unless (null wilds) (log' (p, "Wildcard pattern must be last case"))

--    checkCase :: Expr -> Case -> (Expr, Case)
--    checkCase acc c@(Case p e post) | wildcard c = (acc, Case p (ENot nowhere acc) post)
--                                    | otherwise  = (EOr nowhere e acc, Case p e post)


    -- flatten case list
    flatten :: [Exp Bool Untimed] -> [Exp Bool Timed] -> Cases -> Err [Claim]
    flatten iff postc (Direct post)       = uncurry (splitCase name contract iface [] iff postc) <$> checkPost env post
    flatten iff postc (Branches branches) = logErrs (normalize branches) $ \branches' ->
      fmap concat . for branches' $ \(Case _ cond post) -> do
        if' <- inferExpr env cond
        (updates, ret) <- checkPost env post
        pure $ splitCase name contract iface [if'] iff postc updates ret

splitBehaviour store (Definition pn contract iface@(Interface _ decls) iffs (Creates assigns) extStorage postcs invs) =
  if not . null $ extStorage then error "TODO: support extStorage in constructor"
  else let env = mkEnv contract store decls
  in do
    stateUpdates <- concat <$> traverse (checkAssign env) assigns
    iffs' <- checkIffs env iffs
    invariants <- traverse (inferExpr env) invs
    ensures <- traverse (inferExpr env) postcs

    pure $ invrClaims invariants <> ctorClaims stateUpdates iffs' ensures
  where
    invrClaims invariants = I . Invariant contract [] [] <$> invariants
    ctorClaims updates iffs' ensures
      | null iffs' = [ C $ Constructor contract Pass iface []                    ensures updates [] ]
      | otherwise  = [ C $ Constructor contract Pass iface iffs'                 ensures updates []
                     , C $ Constructor contract Fail iface [Neg (mconcat iffs')] ensures []      [] ]

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
splitCase :: Id -> Id -> Interface -> [Exp Bool Untimed] -> [Exp Bool Untimed] -> [Exp Bool Timed]
          -> [Rewrite] -> Maybe (TypedExp Timed) -> [Claim]
splitCase name contract iface if' [] postcs storage ret =
  [ B $ Behaviour name Pass contract iface if' postcs storage ret ]
splitCase name contract iface if' iffs postcs storage ret =
  [ B $ Behaviour name Pass contract iface (if' <> iffs) postcs storage ret,
    B $ Behaviour name Fail contract iface (if' <> [Neg (mconcat iffs)]) [] (Constant . locFromRewrite <$> storage) Nothing ]

-- | Ensures that none of the storage variables are read in the supplied `Expr`.
noStorageRead :: Map Id SlotType -> Expr -> Err ()
noStorageRead store expr = for_ (keys store) $ \name ->
  for_ (findWithDefault [] name (idFromRewrites expr)) $ \pn ->
    throw (pn,"Cannot read storage in creates block")

--makeItemWith :: (Typeable a, Typeable t) => Env -> (TStorageItem a t -> a) -> AbiType -> Id -> [TypedExp t] ->
makeItemWith env@Env{contract} pn name cons itemcons (args,types) new = cons . itemcons <$> makeIxs

-- checkUpdate :: Env -> AbiType -> Id -> [TypedExp Untimed] -> Expr -> Err StorageUpdate
-- checkUpdate env@Env{contract} typ name ixs newVal =
--   case metaType typ of
--     Integer -> IntUpdate   (IntItem   contract name ixs) <$> inferExpr env newVal
--     Boolean -> BoolUpdate  (BoolItem  contract name ixs) <$> inferExpr env newVal
--     ByteStr -> BytesUpdate (BytesItem contract name ixs) <$> inferExpr env newVal

makeUpdate :: Env -> Sing a -> Id -> [TypedExp Untimed] -> Exp a Untimed -> StorageUpdate
makeUpdate env@Env{contract} typ name ixs newVal =
  case typ of
    SInteger -> IntUpdate   (IntItem   contract name ixs) newVal
    SBoolean -> BoolUpdate  (BoolItem  contract name ixs) newVal
    SByteStr -> BytesUpdate (BytesItem contract name ixs) newVal

-- ensures that key types match value types in an Assign
checkAssign :: Env -> Assign -> Err [StorageUpdate]
checkAssign env@Env{contract, store} (AssignVal (StorageVar pn (StorageValue typ) name) expr)
  = withSomeType (metaType typ) $ \stype ->
      sequenceA [makeUpdate env stype name [] <$> inferExpr env expr]
      <* noStorageRead store expr
checkAssign env@Env{store} (AssignMany (StorageVar pn (StorageMapping (keyType :| _) valType) name) defns)
  = for defns $ \def@(Defn e1 e2) -> checkDefn env keyType valType name def
                                     <* noStorageRead store e1
                                     <* noStorageRead store e2
checkAssign _ (AssignVal (StorageVar pn (StorageMapping _ _) _) expr)
  = throw (getPosn expr, "Cannot assign a single expression to a composite type")
checkAssign _ (AssignMany (StorageVar pn (StorageValue _) _) _)
  = throw (pn, "Cannot assign multiple values to an atomic type")
checkAssign _ _ = error "todo: support struct assignment in constructors"

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Env -> AbiType -> AbiType -> Id -> Defn -> Err StorageUpdate
checkDefn env@Env{contract} keyType valType name (Defn k val) = withSomeType (metaType valType) $ \valType' ->
  makeUpdate env valType' name <$> sequenceA [checkExpr env k keyType] <*> inferExpr env val

checkPost :: Env -> Untyped.Post -> Err ([Rewrite], Maybe (TypedExp Timed))
checkPost env@Env{contract,calldata} (Untyped.Post maybeStorage extStorage maybeReturn) =
  do returnexp <- traverse (typedExp scopedEnv) maybeReturn
     ourStorage <- case maybeStorage of
       Just entries -> checkEntries contract entries
       Nothing -> pure []
     otherStorage <- checkStorages extStorage
     pure (ourStorage <> otherStorage, returnexp)
  where
    checkEntries :: Id -> [Untyped.Storage] -> Err [Rewrite]
    checkEntries name entries =
      for entries $ \case
        Untyped.Constant loc -> Constant <$> checkPattern (focus name scopedEnv) loc
        Untyped.Rewrite loc val -> Rewrite <$> checkStorageExpr (focus name scopedEnv) loc val

    checkStorages :: [ExtStorage] -> Err [Rewrite]
    checkStorages [] = pure []
    checkStorages ((ExtStorage name entries):xs) = do p <- checkEntries name entries
                                                      ps <- checkStorages xs
                                                      pure $ p <> ps
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
checkStorageExpr env@Env{contract,store} (PEntry p name args) expr = case Map.lookup name store of
  Just (StorageValue typ) -> withSomeType (metaType typ) $ \stype ->
    makeUpdate env stype name [] <$> inferExpr env expr
  Just (StorageMapping argtyps typ) -> withSomeType (metaType typ) $ \stype ->
    makeUpdate env stype name <$> makeIxs env p args (NonEmpty.toList argtyps) <*> inferExpr env expr
  Nothing -> throw (p, "Unknown storage variable: " <> show name)

checkPattern :: Env -> Pattern -> Err StorageLocation
checkPattern _ (PWild _) = error "TODO: checkPattern for Wild storage"
checkPattern env@Env{contract,store} (PEntry p name args) =
  case Map.lookup name store of
    Just (StorageValue t) -> makeLocation t []
    Just (StorageMapping argtyps t) -> makeLocation t (NonEmpty.toList argtyps)
    Nothing -> throw (p, "Unknown storage variable: " <> show name)
  where
    makeLocation :: AbiType -> [AbiType] -> Err StorageLocation
    makeLocation locType argTypes = do
      indexExprs <- makeIxs env p args argTypes -- TODO possibly output errormsg with `name`
      pure $ case metaType locType of
        Integer -> IntLoc   $ IntItem   contract name indexExprs
        Boolean -> BoolLoc  $ BoolItem  contract name indexExprs
        ByteStr -> BytesLoc $ BytesItem contract name indexExprs


checkIffs :: Env -> [IffH] -> Err [Exp Bool Untimed]
checkIffs env ((Iff _ exps):xs) = do
  hd <- traverse (inferExpr env) exps
  tl <- checkIffs env xs
  pure $ hd <> tl
checkIffs env ((IffIn _ typ exps):xs) = do
  hd <- traverse (inferExpr env) exps
  tl <- checkIffs env xs
  pure $ map (bound typ) hd <> tl
checkIffs _ [] = pure []

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
upperBound (AbiBytesType n) = UIntMax (8 * n)
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
             <!> ExpBool  <$> inferExpr env e
             <!> ExpBytes <$> inferExpr env e
             <!> throw (getPosn e, "TypedExp: no suitable type") -- TODO improve error handling once we've merged the unified stuff!

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
  EUTEntry   p name es -> checkTime p $ entry p Neither name es
  EPreEntry  p name es -> checkTime p $ entry p Pre     name es
  EPostEntry p name es -> checkTime p $ entry p Post    name es
  EnvExp p v1 -> case lookup v1 defaultStore of
    Just Integer -> check p . pure $ IntEnv v1
    Just ByteStr -> check p . pure $ ByEnv  v1
    _            -> throw (p, "unknown environment variable: " <> show v1)
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
    check :: forall x t0. Typeable x => Pn -> Err (Exp x t0) -> Err (Exp a t0)
    check pn = ensure
                [(pn,"Type mismatch. Expected " <> show (typeRep @a) <> ", got " <> show (typeRep @x) <> ".")]
                castType
              
    checkTime :: forall x t0. Typeable t0 => Pn -> Err (Exp x t0) -> Err (Exp x t)
    checkTime pn = ensure
                    [(pn, (tail . show $ typeRep @t) <> " variable needed here!")]
                    castTime

    -- Takes a polymorphic binary AST constructor and specializes it to each of
    -- our types. Those specializations are used in order to guide the
    -- typechecking of the two supplied expressions. Returns at first success.
    polycheck :: Typeable x => Pn -> (forall y. (Eq y, Typeable y) => Exp y t -> Exp y t -> Exp x t) -> Expr -> Expr -> Err (Exp a t)
    polycheck pn cons e1 e2 = check pn (cons @Integer    <$> inferExpr env e1 <*> inferExpr env e2)
                          <!> check pn (cons @Bool       <$> inferExpr env e1 <*> inferExpr env e2)
                          <!> check pn (cons @ByteString <$> inferExpr env e1 <*> inferExpr env e2)
                          <!> throw (pn, "Couldn't harmonize types!") -- TODO improve error handling once we've merged the unified stuff!

    -- Try to construct a reference to a calldata variable or an item in storage.
    entry :: forall t0. Typeable t0 => Pn -> Time t0 -> Id -> [Expr] -> Err (Exp a t0)
    entry pn timing name es = case (Map.lookup name store, Map.lookup name calldata) of
      (Nothing, Nothing) -> throw (pn, "Unknown variable: " <> name)
      (Just _, Just _)   -> throw (pn, "Ambiguous variable: " <> name)
      (Nothing, Just c) -> if isTimed timing then throw (pn, "Calldata var cannot be pre/post.") else case c of
        -- Create a calldata reference and typecheck it as with normal expressions.
        Integer -> check pn . pure $ IntVar  name
        Boolean -> check pn . pure $ BoolVar name
        ByteStr -> check pn . pure $ ByVar   name
      (Just (StorageValue a), Nothing)      -> makeEntry a []
      (Just (StorageMapping ts a), Nothing) -> makeEntry a $ NonEmpty.toList ts
      where
        makeEntry :: AbiType -> [AbiType] -> Err (Exp a t0)
        makeEntry a ts = case metaType a of
          Integer -> check pn $ makeItem IntItem
          Boolean -> check pn $ makeItem BoolItem
          ByteStr -> check pn $ makeItem BytesItem
          where
            -- Given that the indices used in the expression agree with the storage,
            -- create a `TStorageItem` using the supplied constructor, place it
            -- in a `TEntry` and then attempt to cast its timing parameter to the
            -- target timing of `inferExpr`. Finally, `check` the type parameter as
            -- with all other expressions.
            makeItem :: Typeable x => (Id -> Id -> [TypedExp t0] -> TStorageItem x t0) -> Err (Exp x t0)
            makeItem cons = TEntry timing . cons contract name <$> makeIxs env pn es ts

makeIxs :: Typeable t => Env -> Pn -> [Expr] -> [AbiType] -> Err [TypedExp t]
makeIxs env pn exprs types = if length exprs /= length types
                              then throw (pn, "Index mismatch for entry!")
                              else traverse (uncurry $ checkExpr env) (exprs `zip` types)

-- makeIxs' :: Typeable t => Env -> Pn -> [Expr] -> [AbiType] -> Logger TypeErr [TypedExp t]
-- makeIxs' env pn exprs types = traverse (uncurry $ checkExpr env) (exprs `zip` types)
--                           <* when (length exprs /= length types) (log' (pn, "Index mismatch for entry!"))
