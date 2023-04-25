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

module Type (typecheck, bound, lookupVars, defaultStore, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import Data.Map.Strict    (Map,keys,findWithDefault)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map -- abandon in favor of [(a,b)]?
import Data.Typeable hiding (typeRep)
import Type.Reflection (typeRep)

import Control.Monad.Writer
import Data.List.Extra (snoc,unsnoc)
import Data.Function (on)
import Data.Foldable
import Data.Traversable
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Syntax
import Syntax.Timing
import qualified Syntax.Untyped as U
import Syntax.Typed
import Error

import Data.Type.Equality (TestEquality(..))

type Err = Error String

-- | Typecheck and then detect possible circularities in constructor call graph
typecheck :: U.Act -> Err Act
typecheck act = typecheck' act `bindValidation` \t -> t <$ detectCycle t
  
-- | Main typechecking function.
typecheck' :: U.Act -> Err Act
typecheck' (U.Main contracts) = Act store <$> traverse (checkContract store constructors) contracts
                             <* noDuplicateContracts
                             <* noDuplicateBehaviourNames
                             <* noDuplicateInterfaces
                             <* traverse noDuplicateVars [creates | U.Contract (U.Definition _ _ _ _ creates _ _) _ <- contracts]
  where
    store = lookupVars contracts
    constructors = lookupConstructors contracts

    transitions = concatMap (\(U.Contract _ ts) -> ts) contracts

    noDuplicateContracts :: Err ()
    noDuplicateContracts = noDuplicates [(pn,contract) | U.Contract (U.Definition pn contract _ _ _ _ _) _ <- contracts]
                           $ \c -> "Multiple definitions of Contract " <> c

    noDuplicateVars :: U.Creates -> Err ()
    noDuplicateVars (U.Creates assigns) = noDuplicates (fmap fst . fromAssign <$> assigns)
                                          $ \x -> "Multiple definitions of Variable " <> x

    noDuplicateInterfaces :: Err ()
    noDuplicateInterfaces =
      noDuplicates
        [(pn, contract ++ "." ++ (show iface)) | U.Transition pn _ contract iface _ _ _ <- transitions]
        $ \c -> "Multiple definitions of Interface " <> c
    -- TODO this check allows interface declarations with the same name and argument types but
    -- different argument names (e.g. f(uint x) and f(uint z)). This potentially problematic since
    -- it is not possible to disambiguate. Such declarations are disallowed in Solidity

    noDuplicateBehaviourNames :: Err ()
    noDuplicateBehaviourNames =
      noDuplicates
        [(pn, contract ++ "." ++ behav) | U.Transition pn behav contract _ _ _ _ <- transitions]
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


detectCycle :: Act -> Err ()
detectCycle (Act _ contracts) =
  () <$ foldValidation doDFS Set.empty (map fst calls)
  where
    doDFS :: Set Id -> Id -> Err (Set Id)
    doDFS visited v = if Set.member v visited then pure visited
      else dfs Set.empty visited v
 
    dfs :: Set Id -> Set Id -> Id -> Err (Set Id)
    dfs stack discovered v =
      if Set.member v stack then throw (nowhere, "Detected cycle in constructor calls")
      else if Set.member v discovered then pure discovered
      else
        let ws = adjacent v in
        let stack' = Set.insert v stack in
        let discovered' = Set.insert v discovered in
        foldValidation (dfs stack') discovered' ws

    adjacent :: Id -> [Id]
    adjacent v = case Map.lookup v g of
        Just ws -> ws
        Nothing -> error "Internal error: node must be in the graph"

    calls = fmap findCalls $ contracts
    g = Map.fromList calls
    
    findCalls :: Contract -> (Id, [Id])
    findCalls c@(Contract (Constructor cname _ _ _ _ _ _ _:_) _) = (cname, callsFromContract c)
    findCalls _ = error "Internal error: at least one constructor expected"
  
--- Finds storage declarations from constructors
lookupVars :: [U.Contract] -> Store
lookupVars = foldMap $ \case
  U.Contract (U.Definition  _ contract _ _ (U.Creates assigns) _ _) _ ->
    Map.singleton contract . Map.fromList $ snd . fromAssign <$> assigns

lookupConstructors :: [U.Contract] -> Map Id [AbiType]
lookupConstructors = foldMap $ \case
  U.Contract (U.Definition _ contract (Interface _ decls) _ _ _ _) _ ->
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
  , calldata     :: Map Id ActType   -- ^ The calldata var names and their types.
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
   --others TODO
  ]


mkEnv :: Id -> Store -> Map Id [AbiType] -> Env
mkEnv contract store constructors = Env
  { contract = contract
  , store    = fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = mempty
  , constructors = constructors
  }

-- add calldata to environment
addCalldata :: Env -> [Decl] -> Env
addCalldata env decls = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, fromAbiType typ)) decls



checkContract :: Store -> Map Id [AbiType] -> U.Contract -> Err Contract
checkContract store constructors (U.Contract constr@(U.Definition _ cid _ _ _ _ _) trans) =
  Contract <$> (checkDefinition env constr) <*> (concat <$> traverse (checkTransition env) trans) <* namesConsistent
  where
    env :: Env
    env = mkEnv cid store constructors

    namesConsistent :: Err ()
    namesConsistent = 
      traverse_ (\(U.Transition pn _ cid' _ _ _ _) -> assert (errmsg pn cid') (cid == cid')) trans

    errmsg pn cid' = (pn, "Behavior must belong to contract " <> show cid <> " but belongs to contract " <> cid')


-- checks a transition given a typing of its storage variables
checkTransition :: Env -> U.Transition -> Err [Behaviour]
checkTransition env (U.Transition _ name contract iface@(Interface _ decls) iffs cases posts) =
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap concatMap (caseClaims
                    <$> checkIffs env' iffs
                    <*> traverse (checkExpr env' SBoolean) posts)
    <*> traverse (checkCase env') normalizedCases
  where
    env' = addCalldata env decls

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
    caseClaims :: [Exp ABoolean Untimed] -> [Exp ABoolean Timed] -> ([Exp ABoolean Untimed], [Rewrite], Maybe (TypedExp Timed)) -> [Behaviour]
    caseClaims [] postcs (if',storage,ret) =
      [ Behaviour name Pass contract iface if' postcs storage ret ]
    caseClaims iffs' postcs (if',storage,ret) =
      [ Behaviour name Pass contract iface (if' <> iffs') postcs storage ret,
        Behaviour name Fail contract iface (if' <> [Neg nowhere (mconcat iffs')]) [] (Constant . locFromRewrite <$> storage) Nothing ]

checkDefinition :: Env -> U.Definition -> Err [Constructor]
checkDefinition env (U.Definition _ contract iface@(Interface _ decls) iffs (U.Creates assigns) postcs invs) =
  do
    stateUpdates <- concat <$> traverse (checkAssign env') assigns
    iffs' <- checkIffs env' iffs
    _ <- traverse (validStorage env') assigns
    ensures <- traverse (checkExpr env' SBoolean) postcs
    invs' <- fmap (Invariant contract [] []) <$> traverse (checkExpr env' SBoolean) invs
    pure $ ctorClaims stateUpdates iffs' ensures invs'
  where
    env' = addCalldata env decls

    ctorClaims updates iffs' ensures invs'
      | null iffs' = [ Constructor contract Pass iface [] ensures invs' updates [] ]
      | otherwise  = [ Constructor contract Pass iface iffs'                         ensures invs' updates []
                     , Constructor contract Fail iface [Neg nowhere (mconcat iffs')] ensures invs' []      [] ]

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
checkCase :: Env -> U.Case -> Err ([Exp ABoolean Untimed], [Rewrite], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  -- TODO isWild checks for WildExp, but WildExp is never generated
  if' <- traverse (checkExpr env SBoolean) $ if isWild c then [] else [pre]
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
  = sequenceA [_Update (_Item vt (SVar pn contract name)) <$> checkExpr env typ expr]
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
checkPost :: Env -> U.Post -> Err ([Rewrite], Maybe (TypedExp Timed))
checkPost env@Env{contract,theirs} (U.Post storage maybeReturn) = do
  returnexp <- traverse (typedExp $ focus contract) maybeReturn
  storage' <- checkEntries contract storage
  pure (storage', returnexp)
  where
    checkEntries :: Id -> [U.Storage] -> Err [Rewrite]
    checkEntries name entries = for entries $ \case
      U.Constant loc     -> Constant <$> checkPattern     (focus name) loc
      U.Rewrite  loc val -> Rewrite  <$> checkStorageExpr (focus name) loc val

    focus :: Id -> Env
    focus name = env
      { contract = name
      , store    = Map.findWithDefault mempty name theirs
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
        Just t -> pure (t, SField p ref x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Expression should have a mapping type" <> show e)

validateEntry :: forall t. Typeable t => Env -> U.Entry -> Err (ValueType, StorageRef t)
validateEntry env entry =
  checkEntry env entry `bindValidation` \(typ, ref) -> case typ of
    StorageValue t -> pure (t, ref)
    StorageMapping _ _  -> throw (getPosEntry entry, "Top-level expressions cannot have mapping type")

-- | Typechecks a non-constant rewrite.
checkStorageExpr :: Env -> U.Entry -> U.Expr -> Err StorageUpdate
checkStorageExpr env entry expr =
  validateEntry env entry `bindValidation` \(vt@(FromVType typ), ref) ->
  checkExpr env typ expr `bindValidation` \te ->
  _Update (_Item vt ref) te <$ validContractType (getPosn expr) vt typ te

  where
    validContractType :: Pn -> ValueType -> SType a -> Exp a t -> Err ()
    validContractType p (ContractType c) SContract e =
      let c' = contractId e in
      assert (p, "Expression is expected to be a contract " <> show c <> " but it is a contract " <> show c) (c == c')
    validContractType _ _ _ _ = pure ()

checkPattern :: Env -> U.Entry -> Err StorageLocation
checkPattern env entry =
  validateEntry env entry `bindValidation` \(vt@(FromVType loctyp), ref) ->
    pure $ _Loc (Item loctyp vt ref)

checkIffs :: Env -> [U.IffH] -> Err [Exp ABoolean Untimed]
checkIffs env = foldr check (pure [])
  where
    check (U.Iff   _     exps) acc = mappend <$> traverse (checkExpr env SBoolean) exps <*> acc
    check (U.IffIn _ typ exps) acc = mappend <$> traverse (fmap (bound $ PrimitiveType typ) . checkExpr env SInteger) exps <*> acc

bound :: ValueType -> Exp AInteger t -> Exp ABoolean t
bound (PrimitiveType typ) e = And nowhere (LEQ nowhere (lowerBound typ) e) $ LEQ nowhere e (upperBound typ)
bound (ContractType _) _ = error $ "upperBound not implemented for constract types"

lowerBound :: AbiType -> Exp AInteger t
lowerBound (AbiIntType a) = IntMin nowhere a
-- todo: other negatives?
lowerBound _ = LitInt nowhere 0

-- todo, the rest
upperBound :: AbiType -> Exp AInteger t
upperBound (AbiUIntType  n) = UIntMax nowhere n
upperBound (AbiIntType   n) = IntMax nowhere n
upperBound AbiAddressType   = UIntMax nowhere 160
upperBound (AbiBytesType n) = UIntMax nowhere (8 * n)
upperBound typ = error $ "upperBound not implemented for " ++ show typ

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
                   , TExp SContract  <$> checkExpr env SContract e
                   ]

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
  -- Arithemetic expressions
  (SInteger, U.EAdd    p v1 v2) -> Add p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.ESub    p v1 v2) -> Sub p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EMul    p v1 v2) -> Mul p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EDiv    p v1 v2) -> Div p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EMod    p v1 v2) -> Mod p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EExp    p v1 v2) -> Exp p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.IntLit  p v1)    -> pure $ LitInt  p v1
  -- Constructor calls
  (SContract, U.ECreate p c args) -> case Map.lookup c constructors of
    Just typs -> Create p SContract c <$> checkIxs env p args (fmap PrimitiveType typs)
    Nothing -> throw (p, "Unknown constructor " <> show c)
  -- Control
  (_, U.EITE p v1 v2 v3) ->
    ((,) <$> checkExpr env typ v2 <*> checkExpr env typ v3) `bindValidation` (\(e1, e2) -> do
       _ <- checkITE p typ e1 e2
       b <- checkExpr env SBoolean v1
       pure $ ITE p b e1 e2)
  -- Environment variables
  (SInteger, U.EnvExp p v1) -> case lookup v1 defaultStore of
    Just AInteger -> pure $ IntEnv p v1
    Just AByteStr -> throw (p, "Environment variable " <> show v1 <> " has type bytestring but an expression of type integer is expected.")
    _            -> throw (p, "Unknown environment variable " <> show v1)
  (SByteStr, U.EnvExp p v1) -> case lookup v1 defaultStore of
    Just AInteger -> throw (p, "Environment variable " <> show v1 <> " has type integer but an expression of type bytestring is expected.")
    Just AByteStr -> pure $ ByEnv p v1
    _             -> throw (p, "Unknown environment variable " <> show v1)
  -- Variable references
  (_, U.EUTEntry entry) | isCalldataEntry env entry -> checkCalldataEntry env entry
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
      , ((,) <$> checkExpr env SContract v1 <*> checkExpr env SContract v2) `bindValidation` (\(e1,e2) ->
          cons pn SContract e1 e2 <$ assert (pn, "Contract type of operands do not match") (contractId e1 == contractId e2))
      ]

    checkTime :: forall t0. Typeable t0 => Pn -> Err (Exp a t0 -> Exp a t)
    checkTime pn = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

    isCalldataEntry Env{calldata} (U.EVar _ name) = case Map.lookup name calldata of
      Just _  -> True
      _ -> False
    isCalldataEntry _ _ = False

    checkCalldataEntry Env{store,calldata} (U.EVar p name) = case (Map.lookup name store, Map.lookup name calldata) of
      (Nothing, Nothing) -> throw (p, "Unknown variable " <> name)
      (Just _, Just _)   -> throw (p, "Ambiguous variable " <> name)
      (Nothing, Just (FromAct varType)) -> Var p typ name <$ checkEq p typ varType
      (Just _, Nothing) -> error "Internal error: variable must be in calldata"
    checkCalldataEntry _ _ =  error "Internal error: variable cannot be mapping or contract field"


-- | Find the contract id of an expression with contract type
contractId :: Exp AContract t -> Id
contractId (ITE _ _ a _) = contractId a
contractId (Var _ _ _) = error "Internal error: calldata variables cannot have contract types"
contractId (Create _ _ c _) = c
contractId (TEntry _ _ (Item _ (ContractType c) _)) = c
contractId (TEntry _ _ (Item _ _ _)) = error "Internal error: entry does not have contract type"

-- | Check that if both branches of an ITE have a contract type then it is the same contract type
checkITE :: Pn -> SType a -> Exp a t -> Exp a t -> Err ()
checkITE p SContract e1 e2 =
  assert (p, "Contract type of if then else branches do not match") (contractId e1 == contractId e2)
checkITE _ _ _ _ = pure ()

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
