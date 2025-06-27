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

module Act.Type (typecheck, lookupVars, globalEnv, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import Data.Map.Strict    (Map)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map
import Data.Typeable hiding (typeRep)
import Type.Reflection (typeRep)

import Control.Monad (when)
import Data.Functor
import Data.List.Extra (unsnoc)
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
import Data.Singletons

import Data.Aeson.Types (typeMismatch)


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
    dfs stack visited v
      | Set.member v stack = throw (nowhere, "Detected cycle in constructor calls")
      | OM.member v visited = pure visited
      | otherwise = let (ws, code) = adjacent v in
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

-- | A map containing the interfaces of all available constructors together with pointer constraints
type Constructors = Map Id [(AbiType, Maybe Id)]

-- | Construct the constructor map for the given spec
lookupConstructors :: [U.Contract] -> Constructors
lookupConstructors = foldMap $ \case
  U.Contract (U.Definition _ contract (Interface _ decls) pointers _ _ _ _) _ ->
    let ptrs = Map.fromList $ map (\(PointsTo _ x c) -> (x, c)) pointers in
    Map.singleton contract (map (\(Decl t x) -> (t, Map.lookup x ptrs)) decls)

-- | Extracts what we need to build a 'Store' and to verify that its names are unique.
-- Kind of stupid return type but it makes it easier to use the same function
-- at both places (without relying on custom functions on triples).
fromAssign :: U.Assign -> (Pn, (Id, SlotType))
fromAssign (U.AssignVal (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignMany (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignStruct _ _) = error "TODO: assignstruct"


-- | The type checking environment.
data Env = Env
  { contract     :: Id                           -- ^ The name of the current contract.
  , store        :: Map Id SlotType              -- ^ This contract's storage entry names and their types.
  , theirs       :: Store                        -- ^ Mapping from contract names to a map of their entry names and their types.
  , calldata     :: Map Id AbiType               -- ^ The calldata var names and their types.
  , pointers     :: Map Id Id                    -- ^ Maps address variables to their contract type.
  , constructors :: Constructors                 -- ^ Interfaces of constructors
  }
  deriving (Show)

-- | Environment with globally available variables.
globalEnv :: [(EthEnv, ActType)]
globalEnv =
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


mkEnv :: Id -> Store -> Constructors -> Env
mkEnv contract store constructors = Env
  { contract = contract
  , store    = Map.map fst $ fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = mempty
  , pointers = mempty
  , constructors = constructors
  }

-- Add calldata to environment
addCalldata :: [Decl] -> Env -> Env
addCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, typ)) decls

-- Add pointers to environment
addPointers :: [Pointer] -> Env -> Env
addPointers decls env = env{ pointers = ptrs }
  where
   ptrs = Map.fromList $ map (\(PointsTo _ x c) -> (x, c)) decls

-- Type check a contract
checkContract :: Store -> Constructors -> U.Contract -> Err Contract
checkContract store constructors (U.Contract constr@(U.Definition _ cid _ _ _ _ _ _) trans) =
  Contract <$> checkConstructor env constr <*> (concat <$> traverse (checkBehavior env) trans) <* namesConsistent
  where
    env :: Env
    env = mkEnv cid store constructors

    namesConsistent :: Err ()
    namesConsistent =
      traverse_ (\(U.Transition pn _ cid' _ _ _ _ _) -> assert (errmsg pn cid') (cid == cid')) trans

    errmsg pn cid' = (pn, "Behavior must belong to contract " <> show cid <> " but belongs to contract " <> cid')


-- Type check a behavior
checkBehavior :: Env -> U.Transition -> Err [Behaviour]
checkBehavior env (U.Transition _ name contract iface@(Interface _ decls) ptrs iffs cases posts) =
  traverse (checkPointer env') ptrs *>
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap fmap (makeBehv <$> checkIffs env' iffs <*> traverse (checkExpr env' SBoolean) posts)
  <*> traverse (checkCase env') normalizedCases
  where
    -- Add calldata variables and pointers to the typing environment
    env' = addPointers ptrs $ addCalldata decls env

    noIllegalWilds :: Err ()
    noIllegalWilds = case cases of
      U.Direct   _  -> pure ()
      U.Branches bs -> for_ (init bs) $ \c@(U.Case p _ _) ->
                          ((when (isWild c) ((throw (p, "Wildcard pattern must be last case")):: Err ())) :: Err ())

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
        in rest ++ [if isWild lastCase then U.Case pn negation post else lastCase]

    -- Construct a behavior node
    makeBehv :: [Exp ABoolean Untimed] -> [Exp ABoolean Timed] -> ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed)) -> Behaviour
    makeBehv pres posts' (casecond,storage,ret) = Behaviour name contract iface ptrs pres casecond posts' storage ret

checkConstructor :: Env -> U.Definition -> Err Constructor
checkConstructor env (U.Definition _ contract (Interface _ decls) ptrs iffs (U.Creates assigns) postcs invs) =
  do
    traverse_ (checkPointer env') ptrs
    stateUpdates <- concat <$> traverse (checkAssign env') assigns
    iffs' <- checkIffs envNoStorage iffs
    traverse_ (validStorage env') assigns
    ensures <- traverse (checkExpr env' SBoolean) postcs
    invs' <- fmap (Invariant contract [] []) <$> traverse (checkExpr env' SBoolean) invs
    pure $ Constructor contract (Interface contract decls) ptrs iffs' ensures invs' stateUpdates
  where
    env' = addPointers ptrs $ addCalldata decls env
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env'{ store = mempty }

-- | Checks that a pointer declaration x |-> A is valid. This consists on
-- checking that x is a calldata variable that has address type and A is a valid
-- contract type.
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

-- | Check if the a contract type is valid in an environment
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


-- | Type checks a case, returning typed versions of its preconditions, rewrites and return value.
checkCase :: Env -> U.Case -> Err ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  -- TODO isWild checks for WildExp, but WildExp is never generated
  if' <- traverse (checkExpr env SBoolean) $ if isWild c then [U.BoolLit nowhere True] else [pre]
  (storage,return') <- checkPost env post
  pure (if',storage,return')

-- Check the initial assignment of a storage variable
checkAssign :: Env -> U.Assign -> Err [StorageUpdate]
checkAssign env@Env{contract} (U.AssignVal (U.StorageVar pn (StorageValue vt@(FromVType typ)) name) expr)
  = sequenceA [checkExpr envNoStorage typ expr `bindValidation` \te ->
               findContractType env te `bindValidation` \ctyp ->
               _Update (_Item vt (SVar pn contract name)) te <$ validContractType pn vt ctyp]
  where
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env { store = mempty }

checkAssign env (U.AssignMany (U.StorageVar pn (StorageMapping (keyType :| _) valType) name) defns)
  = for defns $ \def -> checkDefn pn envNoStorage keyType valType name def
  where
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env { store = mempty }

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

-- | Type checks a postcondition, returning typed versions of its storage updates and return expression.
checkPost :: Env -> U.Post -> Err ([StorageUpdate], Maybe (TypedExp Timed))
checkPost env (U.Post storage maybeReturn) = do
  returnexp <- traverse (inferExpr env) maybeReturn
  storage' <- checkEntries storage
  pure (storage', returnexp)
  where
    checkEntries :: [U.Storage] -> Err [StorageUpdate]
    checkEntries entries = for entries $ \case
      U.Rewrite  loc val -> checkStorageExpr env loc val

checkEntry :: forall t k. Typeable t => Env -> SRefKind k -> U.Entry -> Err (SlotType, Maybe Id, Ref k t)
checkEntry Env{contract,store,calldata, pointers} kind (U.EVar p name) = case (kind, Map.lookup name store, Map.lookup name calldata) of
  (_, Just _, Just _) -> throw (p, "Ambiguous variable " <> name)
  (SStorage, Just typ@(StorageValue (ContractType c)), Nothing) -> pure (typ, Just c, SVar p contract name)
  (SStorage, Just typ, Nothing) -> pure (typ, Nothing, SVar p contract name)
  (SCalldata, Nothing, Just typ) -> pure (StorageValue (PrimitiveType typ), Map.lookup name pointers, CVar p typ name)
  (SStorage, _, Just _) -> error "Internal error: Expected storage variable but found calldata variable"
  (SCalldata, Just _, _) -> error "Internal error: Expected storage variable but found calldata variable"
  (_, Nothing, Nothing) -> throw (p, "Unknown variable " <> show name)
checkEntry env kind (U.EMapping p e args) =
  checkEntry env kind e `bindValidation` \(typ, _, ref) -> case typ of
    StorageValue _ -> throw (p, "Expression should have a mapping type" <> show e)
    StorageMapping argtyps restyp -> (StorageValue restyp, Nothing,) . SMapping p ref <$> checkIxs env p args (NonEmpty.toList argtyps)
checkEntry env@Env{theirs} kind (U.EField p e x) =
  checkEntry env kind e `bindValidation` \(_, oc, ref) -> case oc of
    Just c -> case Map.lookup c theirs of
      Just cenv -> case Map.lookup x cenv of
        Just (st@(StorageValue (ContractType c')), _) -> pure (st, Just c', SField p ref c x)
        Just (st, _) -> pure (st, Nothing, SField p ref c x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Expression should have a contract type" <> show e)

validateEntry :: forall t k. Typeable t => Env -> SRefKind k -> U.Entry -> Err (ValueType, Ref k t)
validateEntry env kind entry =
  checkEntry env kind entry `bindValidation` \(typ, oc, ref) -> case typ of
    StorageValue t -> case oc of
                        Just cid -> pure (ContractType cid, ref)
                        _ -> pure (t, ref)
    StorageMapping _ _  -> throw (getPosEntry entry, "Top-level expressions cannot have mapping type")

-- | Typechecks a non-constant rewrite.
checkStorageExpr :: Env -> U.Entry -> U.Expr -> Err StorageUpdate
checkStorageExpr env entry expr =
  validateEntry env SStorage entry `bindValidation` \(vt@(FromVType typ), ref) ->
  checkExpr env typ expr `bindValidation` \te ->
  findContractType env te `bindValidation` \ctyp ->
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


-- | If an `inrange e` predicate appears in the source code, then the inrange
-- predicate is propagated to all subexpressions of `e`. This elaboration step
-- happens here.
genInRange :: AbiType -> Exp AInteger t -> [Exp ABoolean t]
genInRange t e@(LitInt _ _) = [InRange nowhere t e]
genInRange t e@(TEntry _ _ _ _)  = [InRange nowhere t e]
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
checkExprVType :: forall t. Typeable t => Env -> U.Expr -> ValueType -> Err (TypedExp t)
checkExprVType env e (FromVType typ) = TExp typ <$> checkExpr env typ e


typeMismatchErr :: forall a b res. Pn -> SType a -> SType b -> Err res
typeMismatchErr p t1 t2 = (throw (p, "Type " <> show t1 <> " should match type " <> show t2 <> "\n Env:\n" <> show env))

-- | Check is the given expression can be typed with the given type\\
checkExpr :: forall t a. Typeable t => Env -> SType a -> U.Expr -> Err (Exp a t)
checkExpr env t1 e =
    -- No idea why type annotation is required here
    (inferExpr env e :: Err (TypedExp t)) `bindValidation` (\(TExp t2 te) ->
    maybe (typeMismatchErr (getPosn e) t1 t2) (\Refl -> pure te) $ testEquality t1 t2)

-- | Attempt to infer a type of an expression. If succesfull returns an
-- existential package of the infered typed together with the typed expression.
inferExpr :: forall t. Typeable t => Env -> U.Expr -> Err (TypedExp t)
inferExpr env@Env{calldata, constructors} e = case e of
  -- Boolean expressions
  U.ENot    p v1    -> wrapOp  (Neg  p) <$> checkExpr env SBoolean v1
  U.EAnd    p v1 v2 -> wrapOp2 (And  p) <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  U.EOr     p v1 v2 -> wrapOp2 (Or   p) <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  U.EImpl   p v1 v2 -> wrapOp2 (Impl p) <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  U.ELT     p v1 v2 -> wrapOp2 (LT   p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.ELEQ    p v1 v2 -> wrapOp2 (LEQ  p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EGEQ    p v1 v2 -> wrapOp2 (GEQ  p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EGT     p v1 v2 -> wrapOp2 (GT   p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EEq     p v1 v2 -> TExp SBoolean <$> polycheck p Eq v1 v2
  U.ENeq    p v1 v2 -> TExp SBoolean <$> polycheck p NEq v1 v2
  U.BoolLit p v1    -> pure $ TExp SBoolean (LitBool p v1)
  U.EInRange _ abityp v -> TExp SBoolean . andExps <$> genInRange abityp <$> checkExpr env SInteger v

  -- Arithemetic expressions
  U.EAdd   p v1 v2 -> wrapOp2 (Add p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.ESub   p v1 v2 -> wrapOp2 (Sub p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EMul   p v1 v2 -> wrapOp2 (Mul p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EDiv   p v1 v2 -> wrapOp2 (Div p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EMod   p v1 v2 -> wrapOp2 (Mod p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.EExp   p v1 v2 -> wrapOp2 (Exp p) <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  U.IntLit p v1    -> pure $ TExp SInteger (LitInt p v1)

    -- Constructor calls
  U.ECreate p c args -> case Map.lookup c constructors of
    Just sig ->
      let (typs, ptrs) = unzip sig in
      -- check the types of arguments to constructor call
      checkIxs env p args (fmap PrimitiveType typs) `bindValidation` (\args' ->
      -- then check that all arguments that need to be valid pointers to a contract have a contract type
      traverse_ (uncurry $ checkContractType env) (zip args' ptrs) $>
      TExp SInteger (Create p c args'))
    Nothing -> throw (p, "Unknown constructor " <> show c)

   -- Control
  U.EITE p e1 e2 e3 ->
    checkExpr env SBoolean e1 `bindValidation` \b ->
    polycheck p (\pn t te1 te2 -> TExp t (ITE pn b te1 te2)) e2 e3

  -- Environment variables
  U.EnvExp p v1 -> case lookup v1 globalEnv of
    Just AInteger -> pure $ TExp SInteger $ IntEnv p v1
    Just AByteStr -> pure $ TExp SByteStr $ ByEnv  p v1
    _             -> throw (p, "Unknown environment variable " <> show v1)

  -- Variable references
  -- Note: untimed entries in the untyped AST and in the typed AST have
  -- different meanings. Calldata variables are always untimed in the untimed
  -- AST but they become timed (with pre) in the typed AST whene they are used
  -- in a timed context.
  U.EUTEntry entry | isCalldataEntry entry   -> checkVar entry
  U.EPreEntry entry | isCalldataEntry entry  -> checkVar entry
  U.EPostEntry entry | isCalldataEntry entry -> error $ "Internal error: Variables cannot be post" <> show e
  -- Storage references
  U.EUTEntry entry   -> checkStorage entry Neither
  U.EPreEntry entry  -> checkStorage entry Pre
  U.EPostEntry entry -> checkStorage entry Post

  _ -> throw (getPosn e, "Internal error: Cannot type expression " <> show e)

  where
    wrapOp f e1 = TExp sing (f e1) -- use sign to let Haskell automatically derive the type here
    wrapOp2 f e1 e2 = TExp sing (f e1 e2)

    polycheck :: forall z. Pn -> (forall y. Pn -> SType y -> Exp y t -> Exp y t -> z) -> U.Expr -> U.Expr -> Err z
    polycheck pn cons e1 e2 =
        inferExpr env e1 `bindValidation` \(TExp (t1 :: SType a1) (te1 :: Exp a1 t)) -> -- I don't know why type annotations are required here
        inferExpr env e2 `bindValidation` \(TExp (t2 :: SType a2) (te2 :: Exp a2 t)) ->
        maybe (typeMismatchErr pn t1 t2) (\Refl -> pure $ cons pn t1 te1 te2) $ testEquality t1 t2

    checkVar :: U.Entry -> Err (TypedExp t)
    checkVar entry = case (eqT @t @Timed, eqT @t @Untimed) of
       (Just Refl, _) ->
         (\(vt@(FromVType typ), ref) -> TExp typ $ TEntry (getPosEntry entry) Pre SCalldata (Item typ vt ref)) <$> (validateEntry env SCalldata entry)
       (_, Just Refl) -> validateEntry env SCalldata entry `bindValidation` \(vt@(FromVType typ'), ref) ->
         (\(vt@(FromVType typ), ref) -> TExp typ $ TEntry (getPosEntry entry) Neither SCalldata (Item typ vt ref)) <$> (validateEntry env SCalldata entry)
       (_,_) -> error "Internal error: Timing should be either Timed or Untimed"

    -- Type check a storage variable
    checkStorage :: forall t0.  Typeable t0 => U.Entry -> Time t0 -> Err (TypedExp t)
    checkStorage entry time =
        -- check that the timing is correct
       checkTime (getPosEntry entry) <*>
       ((\(vt@(FromVType typ), ref) -> TExp typ $ TEntry (getPosEntry entry) time SStorage (Item typ vt ref)) <$> validateEntry env SStorage entry)

    -- Check that an expression is typed with the right timing
    checkTime :: forall t0. Typeable t0 => Pn -> Err (TypedExp t0 -> TypedExp t)
    checkTime pn = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

    isCalldataEntry (U.EVar _ name) = case Map.lookup name calldata of
      Just _  -> True
      _ -> False
    isCalldataEntry (U.EMapping _ entry _) = isCalldataEntry entry
    isCalldataEntry (U.EField _ entry _) = isCalldataEntry entry

-- | Helper to create to create a conjunction out of a list of expressions
andExps :: [Exp ABoolean t] -> Exp ABoolean t
andExps [] = LitBool nowhere True
andExps (c:cs) = foldr (And nowhere) c cs


-- | Find the contract id of an expression with contract type
findContractType :: Env -> Exp a t -> Err (Maybe Id)
findContractType env (ITE p _ a b) =
  findContractType env a `bindValidation` \oc1 ->
  findContractType env b `bindValidation` \oc2 ->
  case (oc1, oc2) of
    (Just c1, Just c2) -> Just c1 <$ assert (p, "Type of if-then-else branches does not match") (c1 == c2)
    (_, _ )-> pure Nothing
findContractType _ (Create _ c _) = pure $ Just c
findContractType _ (TEntry _ _ _ (Item _ (ContractType c) _)) = pure $ Just c
findContractType _ _ =  pure Nothing

-- | Check if an expression has the expected contract id, if any
checkContractType :: Env -> TypedExp t -> Maybe Id -> Err ()
checkContractType _ _ Nothing = pure ()
checkContractType env (TExp _ e) (Just c) =
  findContractType env e `bindValidation` \case
    Just c' -> assert (posnFromExp e, "Expression was expected to have contract type " <> c <> " but has contract type " <> c') (c == c')
    Nothing -> throw (posnFromExp e, "Expression was expected to have contract type " <> c)


-- | Checks that there are as many expressions as expected by the types,
-- and checks that each one of them agree with its type.
checkIxs :: forall t. Typeable t => Env -> Pn -> [U.Expr] -> [ValueType] -> Err [TypedExp t]
checkIxs env pn exprs types = if length exprs /= length types
                              then throw (pn, "Index mismatch for entry")
                              else traverse (uncurry $ checkExprVType env) (exprs `zip` types)
