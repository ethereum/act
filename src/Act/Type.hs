{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# LANGUAGE ApplicativeDo #-}
{-# Language TupleSections #-}

module Act.Type (typecheck, lookupVars, defaultStore, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import Data.Map.Strict    (Map,keys,findWithDefault)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map -- abandon in favor of [(a,b)]?
import Data.Typeable hiding (typeRep)
import Type.Reflection (typeRep)

import Control.Monad (when)
import Data.List.Extra (snoc,unsnoc)
import Data.Function (on)
import Data.Foldable
import Data.Traversable
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OM

import Act.Syntax
import Act.Syntax.Timing
import Act.Syntax.Untyped qualified as U
import Act.Syntax.Typed
import Act.Syntax.Untyped (makeIface)
import Act.Error

import Data.Type.Equality (TestEquality(..))

type Err = Error String

-- | Typecheck and then detect possible circularities in constructor call graph
typecheck :: U.Act -> Err Act
typecheck act = typecheck' act `bindValidation` topologicalSort

-- | Main typechecking function.
typecheck' :: U.Act -> Err Act
typecheck' (U.Main contracts) = Act store <$> traverse (checkContract store constructors) contracts
                             <* noDuplicateContracts
                             <* noDuplicateBehaviourNames
                             <* noDuplicateInterfaces
                             <* traverse noDuplicateVars [creates | U.Contract (U.Definition _ _ _ _ _ creates _ _) _ <- contracts]
  where
    store = lookupVars contracts
    constructors = lookupConstructors contracts

    transitions = concatMap (\(U.Contract _ ts) -> ts) contracts

    noDuplicateContracts :: Err ()
    noDuplicateContracts = noDuplicates [(pn,contract) | U.Contract (U.Definition pn contract _ _ _ _ _ _) _ <- contracts]
                           $ \c -> "Multiple definitions of Contract " <> c

    noDuplicateVars :: U.Creates -> Err ()
    noDuplicateVars (U.Creates assigns) = noDuplicates (fmap fst . fromAssign <$> assigns)
                                          $ \x -> "Multiple definitions of Variable " <> x

    noDuplicateInterfaces :: Err ()
    noDuplicateInterfaces =
      noDuplicates
        [(pn, contract ++ "." ++ (makeIface iface)) | U.Transition pn _ contract iface _ _ _ _ <- transitions]
        $ \c -> "Multiple definitions of Interface " <> c

    noDuplicateBehaviourNames :: Err ()
    noDuplicateBehaviourNames =
      noDuplicates
        [(pn, contract ++ "." ++ behav) | U.Transition pn behav contract _ _ _ _ _ <- transitions]
        $ \c -> "Multiple definitions of Behaviour " <> c

    -- Generic helper
    noDuplicates :: [(Pn,Id)] -> (Id -> String) -> Err ()
    noDuplicates xs errmsg = traverse_ (throw . fmap errmsg) . nub . duplicatesBy ((==) `on` snd) $ xs
      where
        -- gathers duplicate entries in list based on a custom equality predicate.
        duplicatesBy :: Eq a => (a -> a -> Bool) -> [a] -> [a]
        duplicatesBy _ [] = []
        duplicatesBy f (y:ys) =
          let e = [x | x <- ys , f y x]
              prependIfNotEmpty :: [a] -> a -> [a]
              prependIfNotEmpty [] _ = []
              prependIfNotEmpty a b = b : a
          in (prependIfNotEmpty e y) <> duplicatesBy f ys


-- | Sort contracts topologically so there are no backward edges in
-- the constructor call graph. Throw an error if a cycle is detected.
topologicalSort :: Act -> Err Act
topologicalSort (Act store contracts) =
  -- OM.assoc will return the nodes in the reverse order they were
  -- visited (post-order). Reversing this gives as a topological
  -- ordering of the nodes.
  Act store . reverse . map snd . OM.assocs <$> foldValidation doDFS OM.empty (map fst calls)
  where
    doDFS :: OMap Id Contract -> Id -> Err (OMap Id Contract)
    doDFS visited v = if OM.member v visited then pure visited
      else dfs Set.empty visited v

    dfs :: Set Id -> OMap Id Contract -> Id -> Err (OMap Id Contract)
    dfs stack visited v =
      if Set.member v stack then throw (nowhere, "Detected cycle in constructor calls")
      else if OM.member v visited then pure visited
      else
        let (ws, code) = adjacent v in
        let stack' = Set.insert v stack in
        (OM.|<) (v, code) <$> foldValidation (dfs stack') visited ws

    adjacent :: Id -> ([Id], Contract)
    adjacent v = case Map.lookup v g of
        Just ws -> ws
        Nothing -> error "Internal error: node must be in the graph"

    calls = fmap findCreates contracts
    g = Map.fromList calls

    -- map a contract name to the list of contracts that it calls and its code
    findCreates :: Contract -> (Id, ([Id], Contract))
    findCreates c@(Contract (Constructor cname _ _ _ _ _ _) _) = (cname, (createsFromContract c <> pointersFromContract c, c))

--- Finds storage declarations from constructors
lookupVars :: [U.Contract] -> Store
lookupVars = foldMap $ \case
  U.Contract (U.Definition  _ contract _ _ _ (U.Creates assigns) _ _) _ ->
    Map.singleton contract . Map.fromList $ addSlot $ snd . fromAssign <$> assigns
  where
    addSlot :: [(Id, SlotType)] -> [(Id, (SlotType, Integer))]
    addSlot l = zipWith (\(name, typ) slot -> (name, (typ, slot))) l [0..]


lookupConstructors :: [U.Contract] -> Map Id [AbiType]
lookupConstructors = foldMap $ \case
  U.Contract (U.Definition _ contract (Interface _ decls) _ _ _ _ _) _ ->
    Map.singleton contract (map (\(Decl t _) -> t) decls)

-- | Extracts what we need to build a 'Store' and to verify that its names are unique.
-- Kind of stupid return type but it makes it easier to use the same function
-- at both places (without relying on custom functions on triples.)
fromAssign :: U.Assign -> (Pn, (Id, SlotType))
fromAssign (U.AssignVal (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignMany (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignStruct _ _) = error "TODO: assignstruct"

-- | The type checking environment.
data Env = Env
  { contract     :: Id               -- ^ The name of the current contract.
  , store        :: Map Id SlotType  -- ^ This contract's storage entry names and their types.
  , theirs       :: Store            -- ^ Mapping from contract names to a map of their entry names and their types.
  , calldata     :: Map Id AbiType   -- ^ The calldata var names and their types.
  , pointers     :: Map Id Id        -- ^ Maps address calldata variables to their contract type.
  , constructors :: Map Id [AbiType] -- ^ Interfaces of contract contructors (we only allow constructor calls ATM)
  }

-- typing of eth env variables
defaultStore :: [(EthEnv, ActType)]
defaultStore =
  [(Callvalue, AInteger),
   (Caller, AInteger),
   (Blockhash, AInteger),
   (Blocknumber, AInteger),
   (Difficulty, AInteger),
   (Timestamp, AInteger),
   (Gaslimit, AInteger),
   (Coinbase, AInteger),
   (Chainid, AInteger),
   (This, AInteger),
   (Origin, AInteger),
   (Nonce, AInteger),
   (Calldepth, AInteger)
  ]


mkEnv :: Id -> Store -> Map Id [AbiType] -> Env
mkEnv contract store constructors = Env
  { contract = contract
  , store    = Map.map fst $ fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = mempty
  , pointers = mempty
  , constructors = constructors
  }

-- add calldata to environment
addCalldata :: [Decl] -> Env -> Env
addCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, typ)) decls

-- add pointers to environment
addPointers :: [Pointer] -> Env -> Env
addPointers decls env = env{ pointers = ptrs }
  where
   ptrs = Map.fromList $ map (\(PointsTo _ x c) -> (x, c)) decls

checkContract :: Store -> Map Id [AbiType] -> U.Contract -> Err Contract
checkContract store constructors (U.Contract constr@(U.Definition _ cid _ _ _ _ _ _) trans) =
  Contract <$> checkDefinition env constr <*> (concat <$> traverse (checkTransition env) trans) <* namesConsistent
  where
    env :: Env
    env = mkEnv cid store constructors

    namesConsistent :: Err ()
    namesConsistent =
      traverse_ (\(U.Transition pn _ cid' _ _ _ _ _) -> assert (errmsg pn cid') (cid == cid')) trans

    errmsg pn cid' = (pn, "Behavior must belong to contract " <> show cid <> " but belongs to contract " <> cid')


-- checks a transition given a typing of its storage variables
checkTransition :: Env -> U.Transition -> Err [Behaviour]
checkTransition env (U.Transition _ name contract iface@(Interface _ decls) ptrs iffs cases posts) =
  traverse (checkPointer env') ptrs *>
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap fmap (makeBehv <$> checkIffs env' iffs <*> traverse (checkExpr env' SBoolean) posts)
  <*> traverse (checkCase env') normalizedCases
  where
    env' = addPointers ptrs $ addCalldata decls env

    noIllegalWilds :: Err ()
    noIllegalWilds = case cases of
      U.Direct   _  -> pure ()
      U.Branches bs -> for_ (init bs) $ \c@(U.Case p _ _) ->
                          ((when (isWild c) ((throw (p, "Wildcard pattern must be last case")):: Err ())) :: Err ())  -- TODO test when wildcard isn't last

    -- translate wildcards into negation of other branches and translate a single case to a wildcard
    normalizedCases :: [U.Case]
    normalizedCases = case cases of
      U.Direct   post -> [U.Case nowhere (U.WildExp nowhere) post]
      U.Branches bs ->
        let
          (rest, lastCase@(U.Case pn _ post)) = case unsnoc bs of
                                                  Just r -> r
                                                  Nothing -> error "Internal error: branches cannot be empty"
          negation = U.ENot nowhere $
                        foldl (\acc (U.Case _ e _) -> U.EOr nowhere e acc) (U.BoolLit nowhere False) rest
        in rest `snoc` (if isWild lastCase then U.Case pn negation post else lastCase)

    -- | split case into pass and fail case
    makeBehv :: [Exp ABoolean Untimed] -> [Exp ABoolean Timed] -> ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed)) -> Behaviour
    makeBehv iffs' postcs (if',storage,ret) = Behaviour name contract iface ptrs iffs' if' postcs storage ret

checkDefinition :: Env -> U.Definition -> Err Constructor
checkDefinition env (U.Definition _ contract (Interface _ decls) ptrs iffs (U.Creates assigns) postcs invs) =
  do
    _ <- traverse (checkPointer env') ptrs
    stateUpdates <- concat <$> traverse (checkAssign env') assigns
    iffs' <- checkIffs (env'{ store = mempty })  iffs
    _ <- traverse (validStorage env') assigns
    ensures <- traverse (checkExpr env' SBoolean) postcs
    invs' <- fmap (Invariant contract [] []) <$> traverse (checkExpr env' SBoolean) invs
    pure $ Constructor contract (Interface contract decls) ptrs iffs' ensures invs' stateUpdates
  where
    env' = addPointers ptrs $ addCalldata decls env


checkPointer :: Env -> U.Pointer -> Err ()
checkPointer Env{theirs,calldata} (U.PointsTo p x c) =
  maybe (throw (p, "Contract " <> c <> " is not a valid contract type")) (\_ -> pure ()) (Map.lookup c theirs) *>
  case Map.lookup x calldata of
    Just AbiAddressType -> pure ()
    Just  _ -> throw (p, "Variable " <> x <> " does not have an address type")
    Nothing -> throw (p, "Unknown variable " <> x)
  

-- | Check if the types of storage variables are valid
validStorage :: Env -> U.Assign -> Err ()
validStorage env (U.AssignVal (U.StorageVar p t _) _) = validSlotType env p t
validStorage env (U.AssignMany (U.StorageVar p t _) _) = validSlotType env p t
validStorage env (U.AssignStruct (U.StorageVar p t _) _) = validSlotType env p t

-- | Check if the a type is valid in an environment
validType :: Env -> Pn -> ValueType -> Err ()
validType Env{theirs} p (ContractType c) =
  maybe (throw (p, "Contract " <> c <> " is not a valid contract type")) (\_ -> pure ()) $ Map.lookup c theirs
validType _ _ _ = pure ()

validKey :: Pn -> ValueType -> Err ()
validKey p (ContractType _) = throw (p, "Mappings cannot have contract indices")
validKey _ _ = pure ()

validSlotType :: Env -> Pn -> SlotType -> Err ()
validSlotType env p (StorageMapping ks res) = traverse_ (\k -> validType env p k <* validKey p k) ks <* validType env p res
validSlotType env p (StorageValue t) = validType env p t


-- | Typechecks a case, returning typed versions of its preconditions, rewrites and return value.
checkCase :: Env -> U.Case -> Err ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  -- TODO isWild checks for WildExp, but WildExp is never generated
  if' <- traverse (checkExpr env SBoolean) $ if isWild c then [U.BoolLit nowhere True] else [pre]
  (storage,return') <- checkPost env post
  pure (if',storage,return')

-- | Ensures that none of the storage variables are read in the supplied `Expr`.
noStorageRead :: Map Id SlotType -> U.Expr -> Err ()
noStorageRead store expr = for_ (keys store) $ \name ->
  for_ (findWithDefault [] name (idFromRewrites expr)) $ \pn ->
    throw (pn,"Cannot read storage in creates block")

-- ensures that key types match value types in an U.Assign
checkAssign :: Env -> U.Assign -> Err [StorageUpdate]
checkAssign env@Env{contract,store} (U.AssignVal (U.StorageVar pn (StorageValue vt@(FromVType typ)) name) expr)
  = sequenceA [checkExpr env typ expr `bindValidation` \te ->
               checkContractType env typ te `bindValidation` \ctyp ->
               _Update (_Item vt (SVar pn contract name)) te <$ validContractType pn vt ctyp]
    <* noStorageRead store expr

checkAssign env@Env{store} (U.AssignMany (U.StorageVar pn (StorageMapping (keyType :| _) valType) name) defns)
  = for defns $ \def@(U.Defn e1 e2) -> checkDefn pn env keyType valType name def
                                       <* noStorageRead store e1
                                       <* noStorageRead store e2

checkAssign _ (U.AssignVal (U.StorageVar _ (StorageMapping _ _) _) expr)
  = throw (getPosn expr, "Cannot assign a single expression to a composite type")

checkAssign _ (U.AssignMany (U.StorageVar pn (StorageValue _) _) _)
  = throw (pn, "Cannot assign multiple values to an atomic type")

checkAssign _ _ = error "todo: support struct assignment in constructors"


-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Pn -> Env -> ValueType -> ValueType -> Id -> U.Defn -> Err StorageUpdate
checkDefn pn env@Env{contract} keyType vt@(FromVType valType) name (U.Defn k val) =
  _Update
  <$> (_Item vt . SMapping nowhere (SVar pn contract name) <$> checkIxs env (getPosn k) [k] [keyType])
  <*> checkExpr env valType val

-- | Typechecks a postcondition, returning typed versions of its storage updates and return expression.
checkPost :: Env -> U.Post -> Err ([StorageUpdate], Maybe (TypedExp Timed))
checkPost env@Env{contract,theirs} (U.Post storage maybeReturn) = do
  returnexp <- traverse (typedExp $ focus contract) maybeReturn
  storage' <- checkEntries contract storage
  pure (storage', returnexp)
  where
    checkEntries :: Id -> [U.Storage] -> Err [StorageUpdate]
    checkEntries name entries = for entries $ \case
      U.Rewrite  loc val -> checkStorageExpr (focus name) loc val

    focus :: Id -> Env
    focus name = env
      { contract = name
      , store    = Map.map fst $ Map.findWithDefault mempty name theirs
      }

checkEntry :: forall t. Typeable t => Env -> U.Entry -> Err (SlotType, StorageRef t)
checkEntry Env{contract,store,calldata} (U.EVar p name) = case (Map.lookup name store, Map.lookup name calldata) of
  (Just _, Just _) -> throw (p, "Ambiguous variable " <> name)
  (Just typ, Nothing) -> pure (typ, SVar p contract name)
  (Nothing, Just _) -> throw (p, "Variable " <> name <> " is not a storage variable")
  (Nothing, Nothing) -> throw (p, "Unknown storage variable " <> show name)
  -- TODO more consitent check of name overlap between calldata and storage
checkEntry env (U.EMapping p e args) =
  checkEntry env e `bindValidation` \(typ, ref) -> case typ of
    StorageValue _ -> throw (p, "Expression should have a mapping type" <> show e)
    StorageMapping argtyps restyp -> (StorageValue restyp,) . SMapping p ref <$> checkIxs env p args (NonEmpty.toList argtyps)
checkEntry env@Env{theirs} (U.EField p e x) =
  checkEntry env e `bindValidation` \(typ, ref) -> case typ of
    StorageValue (ContractType c) -> case Map.lookup c theirs of
      Just cenv -> case Map.lookup x cenv of
        Just (t, _) -> pure (t, SField p ref c x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Expression should have a contract type" <> show e)

validateEntry :: forall t. Typeable t => Env -> U.Entry -> Err (ValueType, StorageRef t)
validateEntry env entry =
  checkEntry env entry `bindValidation` \(typ, ref) -> case typ of
    StorageValue t -> pure (t, ref)
    -- TODO can mappings be assigned?
    StorageMapping _ _  -> throw (getPosEntry entry, "Top-level expressions cannot have mapping type")


checkVar :: forall t. Typeable t => Env -> U.Entry -> Err (SlotType, Maybe Id, VarRef t)
checkVar Env{store,calldata, pointers} (U.EVar p name) = case (Map.lookup name store, Map.lookup name calldata) of
  (Just _, Just _) -> throw (p, "Ambiguous variable " <> name)
  (Nothing, Just typ) -> do
    pure (StorageValue (PrimitiveType typ), Map.lookup name pointers, VVar p typ name)
  (Just _, Nothing) ->  error $ "Internal error: Variable must be a calldata variable."
  (Nothing, Nothing) -> throw (p, "Unknown variable " <> show name)
  -- TODO more consitent check of name overlap between calldata and storage
checkVar env (U.EMapping p v args) =
  checkVar env v `bindValidation` \(typ, _, ref) -> case typ of
    StorageValue _ -> throw (p, "Expression should have a mapping type" <> show v)
    StorageMapping argtyps restyp ->
      (StorageValue restyp, Nothing,) . VMapping p ref <$> checkIxs env p args (NonEmpty.toList argtyps)
checkVar env@Env{theirs} (U.EField p e x) =
  checkVar env e `bindValidation` \(_, oc, ref) -> case oc of
    Just c -> case Map.lookup c theirs of
      Just cenv -> case Map.lookup x cenv of
        Just (st@(StorageValue (ContractType c')), _) -> pure (st, Just c', VField p st ref c x)
        Just (st, _) -> pure (st, Nothing, VField p st ref c x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Expression should have a contract type" <> show e)


validateVar :: forall t. Typeable t => Env -> U.Entry -> Err (ValueType, VarRef t)
validateVar env var =
  checkVar env var `bindValidation` \(typ, _, ref) -> case typ of
    StorageValue t -> pure (t, ref)
    -- TODO can mappings be assigned?
    StorageMapping _ _  -> throw (getPosEntry var, "Top-level expressions cannot have mapping type")


-- | Typechecks a non-constant rewrite.
checkStorageExpr :: Env -> U.Entry -> U.Expr -> Err StorageUpdate
checkStorageExpr env entry expr =
  validateEntry env entry `bindValidation` \(vt@(FromVType typ), ref) ->
  checkExpr env typ expr `bindValidation` \te ->
  checkContractType env typ te `bindValidation` \ctyp ->
  _Update (_Item vt ref) te <$ validContractType (getPosn expr) vt ctyp


validContractType :: Pn -> ValueType -> Maybe Id -> Err ()
validContractType pn (ContractType c1) (Just c2) =
  assert (pn, "Assignment to storage variable was expected to have contract type " <> c1 <> " but has contract type " <> c2) (c1 == c2)
validContractType pn (ContractType c1) Nothing =
  throw (pn, "Assignment to storage variable was expected to have contract type " <> c1)
validContractType _ _ _ = pure ()


checkIffs :: Env -> [U.IffH] -> Err [Exp ABoolean Untimed]
checkIffs env = foldr check (pure [])
  where
    check (U.Iff   _     exps) acc = mappend <$> traverse (checkExpr env SBoolean) exps <*> acc
    check (U.IffIn _ typ exps) acc = mappend <$> (mconcat <$> traverse (fmap (genInRange typ) . checkExpr env SInteger) exps) <*> acc

genInRange :: AbiType -> Exp AInteger t -> [Exp ABoolean t]
genInRange t e@(LitInt _ _) = [InRange nowhere t e]
genInRange t e@(Var _ _ _)  = [InRange nowhere t e]
genInRange t e@(TEntry _ _ _)  = [InRange nowhere t e]
genInRange t e@(Add _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Sub _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mul _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Div _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mod _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Exp _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(IntEnv _ _) = [InRange nowhere t e]
genInRange _ (Create _ _ _) = []
genInRange _ (IntMin _ _)  = error "Internal error: invalid range expression"
genInRange _ (IntMax _ _)  = error "Internal error: invalid range expression"
genInRange _ (UIntMin _ _) = error "Internal error: invalid range expression"
genInRange _ (UIntMax _ _) = error "Internal error: invalid range expression"
genInRange _ (ITE _ _ _ _) = error "Internal error: invalid range expression"

-- | Attempt to construct a `TypedExp` whose type matches the supplied `ValueType`.
-- The target timing parameter will be whatever is required by the caller.
checkExprVType :: Typeable t => Env -> U.Expr -> ValueType -> Err (TypedExp t)
checkExprVType env e (FromVType typ) = TExp typ <$> checkExpr env typ e

-- | Attempt to typecheck an untyped expression as any possible type.
typedExp :: Typeable t => Env -> U.Expr -> Err (TypedExp t)
typedExp env e = findSuccess (throw (getPosn e, "Cannot find a valid type for expression " <> show e))
                   [ TExp SInteger <$> checkExpr env SInteger e
                   , TExp SBoolean <$> checkExpr env SBoolean e
                   , TExp SByteStr <$> checkExpr env SByteStr e
                   ]

andExps :: [Exp ABoolean t] -> Exp ABoolean t
andExps [] = LitBool nowhere True
andExps (c:cs) = foldl (\cs' c' -> And nowhere c' cs') c cs

-- | Check the type of an expression and construct a typed expression
checkExpr :: forall a t. Typeable t => Env -> SType a -> U.Expr -> Err (Exp a t)
checkExpr env@Env{constructors} typ e = case (typ, e) of
  -- Boolean expressions
  (SBoolean, U.ENot    p v1)    -> Neg  p <$> checkExpr env SBoolean v1
  (SBoolean, U.EAnd    p v1 v2) -> And  p <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  (SBoolean, U.EOr     p v1 v2) -> Or   p <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  (SBoolean, U.EImpl   p v1 v2) -> Impl p <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  (SBoolean, U.ELT     p v1 v2) -> LT  p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.ELEQ    p v1 v2) -> LEQ p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.EGEQ    p v1 v2) -> GEQ p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.EGT     p v1 v2) -> GT  p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.EEq     p v1 v2) -> polycheck p Eq v1 v2
  (SBoolean, U.ENeq    p v1 v2) -> polycheck p NEq v1 v2
  (SBoolean, U.BoolLit p v1)    -> pure $ LitBool p v1
  (SBoolean, U.EInRange _ abityp v) -> andExps <$> genInRange abityp <$> checkExpr env SInteger v

  -- Arithemetic expressions
  (SInteger, U.EAdd    p v1 v2) -> Add p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.ESub    p v1 v2) -> Sub p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EMul    p v1 v2) -> Mul p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EDiv    p v1 v2) -> Div p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EMod    p v1 v2) -> Mod p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EExp    p v1 v2) -> Exp p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.IntLit  p v1)    -> pure $ LitInt  p v1
  -- Constructor calls
  (SInteger, U.ECreate p c args) -> case Map.lookup c constructors of
    -- TODO check contract types
    Just typs -> Create p c <$> checkIxs env p args (fmap PrimitiveType typs)
    Nothing -> throw (p, "Unknown constructor " <> show c)
  -- Control
  (_, U.EITE p v1 v2 v3) ->
    ((,) <$> checkExpr env typ v2 <*> checkExpr env typ v3) `bindValidation` (\(e1, e2) -> do
       b <- checkExpr env SBoolean v1
       pure $ ITE p b e1 e2)
  -- Environment variables
  (SInteger, U.EnvExp p v1) -> case lookup v1 defaultStore of
    Just AInteger -> pure $ IntEnv p v1
    Just AByteStr -> throw (p, "Environment variable " <> show v1 <> " has type bytestring but an expression of type integer is expected.")
    _             -> throw (p, "Unknown environment variable " <> show v1)
  (SByteStr, U.EnvExp p v1) -> case lookup v1 defaultStore of
    Just AInteger -> throw (p, "Environment variable " <> show v1 <> " has type integer but an expression of type bytestring is expected.")
    Just AByteStr -> pure $ ByEnv p v1
    _             -> throw (p, "Unknown environment variable " <> show v1)
  -- Variable referencesΕΙΔΙΚΟΣ ΛΟΓΑΡΙΑΣΜΟΣ ΚΟΝΔΥΛΙΩΝ ΕΡΕΥΝΑΣ Ε.Μ.Π.

  (_, U.EUTEntry entry) | isCalldataEntry env entry -> validateVar env entry `bindValidation` \((FromVType typ'), ref) ->
    Var (getPosEntry entry) typ ref <$ checkEq (getPosEntry entry) typ typ'
  -- Storage references
  (_, U.EUTEntry entry) -> validateEntry env entry `bindValidation` \(vt@(FromVType typ'), ref) ->
    checkTime (getPosEntry entry) <*> (TEntry (getPosEntry entry) Neither (Item typ vt ref) <$ checkEq (getPosEntry entry) typ typ')
  (_, U.EPreEntry entry) -> validateEntry env entry `bindValidation` \(vt@(FromVType typ'), ref) ->
    checkTime (getPosEntry entry) <*> (TEntry (getPosEntry entry) Pre (Item typ vt ref) <$ checkEq (getPosEntry entry) typ typ')
  (_, U.EPostEntry entry) -> validateEntry env entry `bindValidation` \(vt@(FromVType typ'), ref) ->
    checkTime (getPosEntry entry) <*> (TEntry (getPosEntry entry) Post (Item typ vt ref) <$ checkEq (getPosEntry entry) typ typ')

  -- TODO other error for unimplemented
  _ -> throw (getPosn e,"Type mismatch. Expression does not have type " <> show typ)

  where
    polycheck :: Pn -> (forall y. Pn -> SType y -> Exp y t -> Exp y t -> Exp x t) -> U.Expr -> U.Expr -> Err (Exp x t)
    polycheck pn cons v1 v2 = findSuccess (throw (pn, "Cannot match the type of expression " <> show v1 <> " with expression " <> show v2))
      [ cons pn SInteger <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
      , cons pn SBoolean <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
      , cons pn SByteStr <$> checkExpr env SByteStr v1 <*> checkExpr env SByteStr v2
      -- , ((,) <$> checkExpr env SContract v1 <*> checkExpr env SContract v2) `bindValidation` (\(e1,e2) ->
      --     cons pn SContract e1 e2 <$ assert (pn, "Contract type of operands do not match") (contractId e1 == contractId e2))
      ]

    checkTime :: forall t0. Typeable t0 => Pn -> Err (Exp a t0 -> Exp a t)
    checkTime pn = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

    -- TODO FIX
    isCalldataEntry Env{calldata} (U.EVar _ name) = case Map.lookup name calldata of
      Just _  -> True
      _ -> False
    isCalldataEntry _ _ = False


-- | Find the contract id of an expression with contract type
checkContractType :: Env -> SType a -> Exp a t -> Err (Maybe Id)
checkContractType env SInteger (ITE p _ a b) =
  checkContractType env SInteger a `bindValidation` \oc1 ->
  checkContractType env SInteger b `bindValidation` \oc2 ->
  case (oc1, oc2) of
    (Just c1, Just c2) -> Just c1 <$ assert (p, "Type of if-then-else branches does not match") (c1 == c2)
    (_, _ )-> pure Nothing
checkContractType _ SInteger (Create _ c _) = pure $ Just c
checkContractType Env{pointers} SInteger (Var _ _ (VVar _ _ x)) =
  case Map.lookup x pointers of
    Just c -> pure $ Just c
    Nothing -> pure Nothing
checkContractType _ SInteger (Var _ _ (VField _ st _ _ _)) =
  case st of
    StorageValue (ContractType c) -> pure $ Just c
    _ -> pure $ Nothing   
checkContractType _ _ (TEntry _ _ (Item _ (ContractType c) _)) = pure $ Just c
checkContractType _ SInteger _ =  pure Nothing
checkContractType _ SBoolean _ =  pure Nothing
checkContractType _ SByteStr _ =  pure Nothing
-- checkContractType (TEntry _ _ (Item _ _ _)) = error "Internal error: entry does not have contract type"

checkEq :: forall a b. Pn -> SType a -> SType b -> Err ()
checkEq p t1 t2 = maybe err (\Refl -> pure ()) $  testEquality t1 t2
  where
    err = (throw (p, "Type " <> show t1 <> " should match type " <> show t2))


-- | Checks that there are as many expressions as expected by the types,
-- and checks that each one of them agree with its type.
checkIxs :: forall t. Typeable t => Env -> Pn -> [U.Expr] -> [ValueType] -> Err [TypedExp t]
checkIxs env pn exprs types = if length exprs /= length types
                              then throw (pn, "Index mismatch for entry")
                              else traverse (uncurry $ checkExprVType env) (exprs `zip` types)
