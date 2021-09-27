{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}
{-# LANGUAGE ApplicativeDo #-}

module Type (typecheck, bound, lookupVars, defaultStore, metaType, Err) where

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

import Control.Lens.Operators ((??))
import Control.Monad.Writer
import Data.List.Extra (snoc,unsnoc)
import Data.Function (on)
import Data.Functor.Alt
import Data.Foldable
import Data.Traversable

import Syntax
import Syntax.Timing
import Syntax.Untyped (Pn)
import qualified Syntax.Untyped as U
import Syntax.Typed
import Error
import Parse

type Err = Error String

typecheck :: [U.RawBehaviour] -> Err [Claim]
typecheck behvs = (S store:) . concat <$> traverse (splitBehaviour store) behvs
                  <* noDuplicateContracts behvs
                  <* traverse noDuplicateVars [creates | U.Definition _ _ _ _ creates _ _ _ <- behvs]
  where
    store = lookupVars behvs

noDuplicateContracts :: [U.RawBehaviour] -> Err ()
noDuplicateContracts behvs = noDuplicates [(pn,contract) | U.Definition pn contract _ _ _ _ _ _ <- behvs]
                             $ \c -> "Multiple definitions of " <> c

noDuplicateVars :: U.Creates -> Err ()
noDuplicateVars (U.Creates assigns) = noDuplicates (fmap fst . fromAssign <$> assigns)
                                      $ \x -> "Multiple definitions of " <> x

noDuplicates :: [(Pn,Id)] -> (Id -> String) -> Err ()
noDuplicates xs errmsg = traverse_ (throw . fmap errmsg) . duplicatesBy ((==) `on` snd) $ xs

--- Finds storage declarations from constructors
lookupVars :: [U.RawBehaviour] -> Store
lookupVars = foldMap $ \case
  U.Transition {} -> mempty
  U.Definition _ contract _ _ (U.Creates assigns) _ _ _ ->
    Map.singleton contract . Map.fromList $ snd . fromAssign <$> assigns

fromAssign :: U.Assign -> (Pn, (Id, SlotType))
fromAssign (U.AssignVal (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignMany (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignStruct _ _) = error "TODO: assignstruct"

-- | filters out duplicate entries in list
duplicatesBy :: (a -> a -> Bool) -> [a] -> [a]
duplicatesBy _ [] = []
duplicatesBy f (x:xs) =
  let e = [x | any (f x) xs]
  in e <> duplicatesBy f xs

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

mkEnv :: Id -> Store -> [Decl] -> Env
mkEnv contract store decls = Env
  { contract = contract
  , store    = fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = abiVars
  }
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, metaType typ)) decls

-- checks a transition given a typing of its storage variables
splitBehaviour :: Store -> U.RawBehaviour -> Err [Claim]
splitBehaviour store (U.Transition _ name contract iface@(Interface _ decls) iffs cases posts) =
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap concatMap (caseClaims
                    <$> checkIffs env iffs
                    <*> traverse (inferExpr env) posts)
    <*> traverse (checkCase env) normalizedCases
  where
    env :: Env
    env = mkEnv contract store decls

    noIllegalWilds :: Err ()
    noIllegalWilds = case cases of
      U.Direct   _  -> pure ()
      U.Branches bs -> for_ (init bs) $ \c@(U.Case p _ _) ->
                          when (isWild c) (throw (p, "Wildcard pattern must be last case"))  -- TODO test when wildcard isn't last

    -- translate wildcards into negation of other branches and translate a single case to a wildcard 
    normalizedCases :: [U.Case]
    normalizedCases = case cases of
      U.Direct   post -> [U.Case nowhere (U.WildExp nowhere) post]
      U.Branches bs ->
        let
          Just (rest, lastCase@(U.Case pn _ post)) = unsnoc bs
          negation = U.ENot nowhere $
                        foldl (\acc (U.Case _ e _) -> U.EOr nowhere e acc) (U.BoolLit nowhere False) rest
        in rest `snoc` (if isWild lastCase then U.Case pn negation post else lastCase)

    -- | split case into pass and fail case
    caseClaims :: [Exp Bool Untimed] -> [Exp Bool Timed] -> ([Exp Bool Untimed], [Rewrite], Maybe (TypedExp Timed)) -> [Claim]
    caseClaims []   postcs (if',storage,ret) =
      [ B $ Behaviour name Pass contract iface if' postcs storage ret ]
    caseClaims iffs' postcs (if',storage,ret) =
      [ B $ Behaviour name Pass contract iface (if' <> iffs') postcs storage ret,
        B $ Behaviour name Fail contract iface (if' <> [Neg (mconcat iffs')]) [] (Constant . locFromRewrite <$> storage) Nothing ]

splitBehaviour store (U.Definition _ contract iface@(Interface _ decls) iffs (U.Creates assigns) extStorage postcs invs) =
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

checkCase :: Env -> U.Case -> Err ([Exp Bool Untimed], [Rewrite], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  if' <- traverse (inferExpr env) $ if isWild c then [] else [pre]
  (storage,return') <- checkPost env post
  pure (if',storage,return')

-- | Ensures that none of the storage variables are read in the supplied `Expr`.
noStorageRead :: Map Id SlotType -> U.Expr -> Err ()
noStorageRead store expr = for_ (keys store) $ \name ->
  for_ (findWithDefault [] name (idFromRewrites expr)) $ \pn ->
    throw (pn,"Cannot read storage in creates block")

makeUpdate :: Env -> SType a -> Id -> [TypedExp Untimed] -> Exp a Untimed -> StorageUpdate
makeUpdate Env{contract} typ name ixs newVal = let item = Item typ contract name ixs in
  case typ of
    SInteger -> IntUpdate   item newVal
    SBoolean -> BoolUpdate  item newVal--(BoolItem  contract name ixs) newVal
    SByteStr -> BytesUpdate item newVal--(BytesItem contract name ixs) newVal

-- ensures that key types match value types in an U.Assign
checkAssign :: Env -> U.Assign -> Err [StorageUpdate]
checkAssign env@Env{store} (U.AssignVal (U.StorageVar _ (StorageValue (FromAbi typ)) name) expr)
  = sequenceA [makeUpdate env typ name [] <$> inferExpr env expr]
    <* noStorageRead store expr
checkAssign env@Env{store} (U.AssignMany (U.StorageVar _ (StorageMapping (keyType :| _) valType) name) defns)
  = for defns $ \def@(U.Defn e1 e2) -> checkDefn env keyType valType name def
                                       <* noStorageRead store e1
                                       <* noStorageRead store e2
checkAssign _ (U.AssignVal (U.StorageVar _ (StorageMapping _ _) _) expr)
  = throw (getPosn expr, "Cannot assign a single expression to a composite type")
checkAssign _ (U.AssignMany (U.StorageVar pn (StorageValue _) _) _)
  = throw (pn, "Cannot assign multiple values to an atomic type")
checkAssign _ _ = error "todo: support struct assignment in constructors"

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Env -> AbiType -> AbiType -> Id -> U.Defn -> Err StorageUpdate
checkDefn env keyType (FromAbi valType) name (U.Defn k val) =
  makeUpdate env valType name <$> checkIxs env (getPosn k) [k] [keyType] <*> inferExpr env val

checkPost :: Env -> U.Post -> Err ([Rewrite], Maybe (TypedExp Timed))
checkPost env@Env{contract,calldata} (U.Post storage extStorage maybeReturn) = do
  returnexp <- traverse (typedExp scopedEnv) maybeReturn
  ourStorage <- checkEntries contract storage
  otherStorage <- checkStorages extStorage
  pure (ourStorage <> otherStorage, returnexp)
  where
    checkEntries :: Id -> [U.Storage] -> Err [Rewrite]
    checkEntries name entries = for entries $ \case
      U.Constant loc     -> Constant <$> checkPattern     (focus name scopedEnv) loc
      U.Rewrite  loc val -> Rewrite  <$> checkStorageExpr (focus name scopedEnv) loc val

    checkStorages :: [U.ExtStorage] -> Err [Rewrite]
    checkStorages [] = pure []
    checkStorages (U.ExtStorage name entries:xs) = mappend <$> checkEntries name entries <*> checkStorages xs
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
    localNames = nameFromStorage <$> storage

    externalNames :: Map Id [Id]
    externalNames = Map.fromList $ mapMaybe (\case
        U.ExtStorage name storages -> Just (name, nameFromStorage <$> storages)
        U.ExtCreates {} -> error "TODO: handle ExtCreate"
        U.WildStorage -> Nothing
      ) extStorage

checkStorageExpr :: Env -> U.Pattern -> U.Expr -> Err StorageUpdate
checkStorageExpr _ (U.PWild _) _ = error "TODO: add support for wild storage to checkStorageExpr"
checkStorageExpr env@Env{store} (U.PEntry p name args) expr = case Map.lookup name store of
  Just (StorageValue (FromAbi typ)) ->
    makeUpdate env typ name [] <$> inferExpr env expr
  Just (StorageMapping argtyps (FromAbi valType)) ->
    makeUpdate env valType name <$> checkIxs env p args (NonEmpty.toList argtyps) <*> inferExpr env expr
  Nothing -> throw (p, "Unknown storage variable " <> show name)

checkPattern :: Env -> U.Pattern -> Err StorageLocation
checkPattern _ (U.PWild _) = error "TODO: checkPattern for Wild storage"
checkPattern env@Env{contract,store} (U.PEntry p name args) =
  case Map.lookup name store of
    Just (StorageValue t) -> makeLocation t []
    Just (StorageMapping argtyps t) -> makeLocation t (NonEmpty.toList argtyps)
    Nothing -> throw (p, "Unknown storage variable " <> show name)
  where
    makeLocation :: AbiType -> [AbiType] -> Err StorageLocation
    makeLocation (FromAbi locType) argTypes =
      let item = Item locType contract name <$> checkIxs @Untimed env p args argTypes
      in case locType of
        SInteger -> IntLoc   <$> item
        SBoolean -> BoolLoc  <$> item
        SByteStr -> BytesLoc <$> item

checkIffs :: Env -> [U.IffH] -> Err [Exp Bool Untimed]
checkIffs env = foldr check (pure [])
  where
    check (U.Iff   _     exps) acc = mappend <$> traverse (inferExpr env) exps                    <*> acc
    check (U.IffIn _ typ exps) acc = mappend <$> traverse (fmap (bound typ) . inferExpr env) exps <*> acc

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
checkExpr :: Typeable t => Env -> U.Expr -> AbiType -> Err (TypedExp t)
checkExpr env e typ = case metaType typ of
  Integer -> ExpInt   <$> inferExpr env e
  Boolean -> ExpBool  <$> inferExpr env e
  ByteStr -> ExpBytes <$> inferExpr env e

-- | Attempt to typecheck an untyped expression as any possible type.
typedExp :: Typeable t => Env -> U.Expr -> Err (TypedExp t)
typedExp env e = notAtPosn (getPosn e)
    $ A (ExpInt   <$> inferExpr env e)
  <!> A (ExpBool  <$> inferExpr env e)
  <!> A (ExpBytes <$> inferExpr env e)
  <!> error "Internal error: typedExp"

-- | Attempts to construct an expression with the type and timing required by
-- the caller. If this is impossible, an error is thrown instead.
inferExpr :: forall a t. (Typeable a, Typeable t) => Env -> U.Expr -> Err (Exp a t)
inferExpr env@Env{contract,store,calldata} expr = case expr of
  U.ENot    p v1    -> check p <*> (Neg  <$> inferExpr env v1)
  U.EAnd    p v1 v2 -> check p <*> (And  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EOr     p v1 v2 -> check p <*> (Or   <$> inferExpr env v1 <*> inferExpr env v2)
  U.EImpl   p v1 v2 -> check p <*> (Impl <$> inferExpr env v1 <*> inferExpr env v2)
  U.EEq     p v1 v2 -> polycheck p Eq v1 v2
  U.ENeq    p v1 v2 -> polycheck p NEq v1 v2
  U.ELT     p v1 v2 -> check p <*> (LE   <$> inferExpr env v1 <*> inferExpr env v2)
  U.ELEQ    p v1 v2 -> check p <*> (LEQ  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EGEQ    p v1 v2 -> check p <*> (GEQ  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EGT     p v1 v2 -> check p <*> (GE   <$> inferExpr env v1 <*> inferExpr env v2)
  U.EAdd    p v1 v2 -> check p <*> (Add  <$> inferExpr env v1 <*> inferExpr env v2)
  U.ESub    p v1 v2 -> check p <*> (Sub  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EMul    p v1 v2 -> check p <*> (Mul  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EDiv    p v1 v2 -> check p <*> (Div  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EMod    p v1 v2 -> check p <*> (Mod  <$> inferExpr env v1 <*> inferExpr env v2)
  U.EExp    p v1 v2 -> check p <*> (Exp  <$> inferExpr env v1 <*> inferExpr env v2)
  U.IntLit  p v1    -> check p ?? LitInt v1
  U.BoolLit p v1    -> check p ?? LitBool v1
  U.EITE    _ v1 v2 v3 -> ITE <$> inferExpr env v1 <*> inferExpr env v2 <*> inferExpr env v3
  U.EUTEntry   p name es -> entry p Neither name es
  U.EPreEntry  p name es -> entry p Pre     name es
  U.EPostEntry p name es -> entry p Post    name es
  U.EnvExp p v1 -> case lookup v1 defaultStore of
    Just Integer -> check p ?? IntEnv v1
    Just ByteStr -> check p ?? ByEnv  v1
    _            -> throw (p, "unknown environment variable " <> show v1)
  v -> error $ "internal error: infer type of" <> show v
  -- Wild ->
  -- Zoom Var Exp
  -- Func Var [U.Expr]
  -- Look U.Expr U.Expr
  -- ECat U.Expr U.Expr
  -- ESlice U.Expr U.Expr U.Expr
  -- Newaddr U.Expr U.Expr
  -- Newaddr2 U.Expr U.Expr U.Expr
  -- BYHash U.Expr
  -- BYAbiE U.Expr
  -- StringLit String
  where
    check :: forall x t0. Typeable x => Pn -> Err (Exp x t0 -> Exp a t0)
    check pn = case eqT @a @x of
      Just Refl -> pure id
      Nothing   -> throw (pn,"Type mismatch. Expected " <> show (typeRep @a) <> ", got " <> show (typeRep @x))

    checkTime :: forall x t0. (Typeable t0, Typeable x) => Pn -> Err (Exp x t0 -> Exp x t)
    checkTime pn = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

    -- Takes a polymorphic binary AST constructor and specializes it to each of
    -- our types. Those specializations are used in order to guide the
    -- typechecking of the two supplied expressions. Returns at first success.
    polycheck :: Typeable x => Pn -> (forall y. (Eq y, Typeable y) => Exp y t -> Exp y t -> Exp x t) -> U.Expr -> U.Expr -> Err (Exp a t)
    polycheck pn cons e1 e2 = notAtPosn (getPosn e1)
        $ A (check pn <*> (cons @Integer    <$> inferExpr env e1 <*> inferExpr env e2))
      <!> A (check pn <*> (cons @Bool       <$> inferExpr env e1 <*> inferExpr env e2))
      <!> A (check pn <*> (cons @ByteString <$> inferExpr env e1 <*> inferExpr env e2))
      <!> error "Internal error: polycheck" -- throw (pn, "Type mismatch. Left- and right-hand sides do not match")

    -- Try to construct a reference to a calldata variable or an item in storage.
    entry :: forall t0. Typeable t0 => Pn -> Time t0 -> Id -> [U.Expr] -> Err (Exp a t)
    entry pn timing name es = case (Map.lookup name store, Map.lookup name calldata) of
      (Nothing, Nothing) -> throw (pn, "Unknown variable " <> name)
      (Just _, Just _)   -> throw (pn, "Ambiguous variable " <> name)
      (Nothing, Just (FromMeta varType)) ->
        if isTimed timing then throw (pn, "Calldata var cannot be pre/post")
          else check pn ?? Var varType name
          ---- Create a calldata reference and typecheck it as with normal expressions.
         --Integer -> check pn ?? IntVar  name
          --Boolean -> check pn ?? BoolVar name
          --ByteStr -> check pn ?? ByVar   name
      (Just (StorageValue a), Nothing)      -> checkEntry a []
      (Just (StorageMapping ts a), Nothing) -> checkEntry a $ NonEmpty.toList ts
      where
        checkEntry :: AbiType -> [AbiType] -> Err (Exp a t)
        checkEntry (FromAbi entryType) ts = checkTime pn <*> (check pn <*>
          (TEntry timing . Item entryType contract name <$> checkIxs env pn es ts))

checkIxs :: Typeable t => Env -> Pn -> [U.Expr] -> [AbiType] -> Err [TypedExp t]
checkIxs env pn exprs types = if length exprs /= length types
                              then throw (pn, "Index mismatch for entry")
                              else traverse (uncurry $ checkExpr env) (exprs `zip` types)

-- checkIxs' :: Typeable t => Env -> Pn -> [U.Expr] -> [AbiType] -> Logger TypeErr [TypedExp t]
-- checkIxs' env pn exprs types = traverse (uncurry $ checkExpr env) (exprs `zip` types)
--                           <* when (length exprs /= length types) (log' (pn, "Index mismatch for entry!"))
