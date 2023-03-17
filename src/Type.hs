{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# LANGUAGE ApplicativeDo #-}

module Type (typecheck, bound, lookupVars, defaultStore, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import EVM.Solidity (SlotType(..))
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

import Syntax
import Syntax.Timing
import qualified Syntax.Untyped as U
import Syntax.Typed
import Error

type Err = Error String

-- | Main typechecking function.
typecheck :: [U.RawBehaviour] -> Err [Claim]
typecheck behvs = (S store:) . concat <$> traverse (splitBehaviour store) behvs
                  <* noDuplicateContracts
                  <* noDuplicateBehaviourNames
                  <* noDuplicateInterfaces
                  <* traverse noDuplicateVars [creates | U.Definition _ _ _ _ creates _ _ _ <- behvs]
  where
    store = lookupVars behvs

    noDuplicateContracts :: Err ()
    noDuplicateContracts = noDuplicates [(pn,contract) | U.Definition pn contract _ _ _ _ _ _ <- behvs]
                           $ \c -> "Multiple definitions of Contract " <> c

    noDuplicateVars :: U.Creates -> Err ()
    noDuplicateVars (U.Creates assigns) = noDuplicates (fmap fst . fromAssign <$> assigns)
                           $ \x -> "Multiple definitions of Variable " <> x

    noDuplicateInterfaces :: Err ()
    noDuplicateInterfaces =
      noDuplicates
        [(pn, contract ++ "." ++ (show iface)) | U.Transition pn _ contract iface _ _ _ <- behvs]
        $ \c -> "Multiple definitions of Interface " <> c

    noDuplicateBehaviourNames :: Err ()
    noDuplicateBehaviourNames =
      noDuplicates
        [(pn, contract ++ "." ++ behav) | U.Transition pn behav contract _ _ _ _ <- behvs]
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

--- Finds storage declarations from constructors
lookupVars :: [U.RawBehaviour] -> Store
lookupVars = foldMap $ \case
  U.Transition {} -> mempty
  U.Definition _ contract _ _ (U.Creates assigns) _ _ _ ->
    Map.singleton contract . Map.fromList $ snd . fromAssign <$> assigns

-- | Extracts what we need to build a 'Store' and to verify that its names are unique.
-- Kind of stupid return type but it makes it easier to use the same function
-- at both places (without relying on custom functions on triples.)
fromAssign :: U.Assign -> (Pn, (Id, SlotType))
fromAssign (U.AssignVal (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignMany (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignStruct _ _) = error "TODO: assignstruct"

-- | The type checking environment.
data Env = Env
  { contract :: Id              -- ^ The name of the current contract.
  , store    :: Map Id SlotType -- ^ This contract's storage entry names and their types.
  , theirs   :: Store           -- ^ Mapping from contract names to a map of their entry names and their types.
  , calldata :: Map Id ActType    -- ^ The calldata var names and their types.
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

mkEnv :: Id -> Store -> [Decl] -> Env
mkEnv contract store decls = Env
  { contract = contract
  , store    = fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = abiVars
  }
 where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, actType typ)) decls

-- checks a transition given a typing of its storage variables
splitBehaviour :: Store -> U.RawBehaviour -> Err [Claim]
splitBehaviour store (U.Transition _ name contract iface@(Interface _ decls) iffs cases posts) =
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap concatMap (caseClaims
                    <$> checkIffs env iffs
                    <*> traverse (checkExpr env SBoolean) posts)
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
    caseClaims :: [Exp ABoolean Untimed] -> [Exp ABoolean Timed] -> ([Exp ABoolean Untimed], [Rewrite], Maybe (TypedExp Timed)) -> [Claim]
    caseClaims []   postcs (if',storage,ret) =
      [ B $ Behaviour name Pass contract iface if' postcs storage ret ]
    caseClaims iffs' postcs (if',storage,ret) =
      [ B $ Behaviour name Pass contract iface (if' <> iffs') postcs storage ret,
        B $ Behaviour name Fail contract iface (if' <> [Neg nowhere (mconcat iffs')]) [] (Constant . locFromRewrite <$> storage) Nothing ]

splitBehaviour store (U.Definition _ contract iface@(Interface _ decls) iffs (U.Creates assigns) extStorage postcs invs) =
  if not . null $ extStorage then error "TODO: support extStorage in constructor"
  else let env = mkEnv contract store decls
  in do
    stateUpdates <- concat <$> traverse (checkAssign env) assigns
    iffs' <- checkIffs env iffs
    invariants <- traverse (checkExpr env SBoolean) invs
    ensures <- traverse (checkExpr env SBoolean) postcs

    pure $ invrClaims invariants <> ctorClaims stateUpdates iffs' ensures
  where
    invrClaims invariants = I . Invariant contract [] [] <$> invariants
    ctorClaims updates iffs' ensures
      | null iffs' = [ C $ Constructor contract Pass iface []                            ensures updates [] ]
      | otherwise  = [ C $ Constructor contract Pass iface iffs'                         ensures updates []
                     , C $ Constructor contract Fail iface [Neg nowhere (mconcat iffs')] ensures []      [] ]

-- | Typechecks a case, returning typed versions of its preconditions, rewrites and return value.
checkCase :: Env -> U.Case -> Err ([Exp ABoolean Untimed], [Rewrite], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  -- XXX isWild checks for WildExp, but WildExp is never generated
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
checkAssign env@Env{contract,store} (U.AssignVal (U.StorageVar _ (StorageValue (FromAbi typ)) name) expr)
  = sequenceA [Update typ (Item typ contract name []) <$> checkExpr env typ expr]
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
checkDefn env@Env{contract} keyType (FromAbi valType) name (U.Defn k val) =
  Update valType
  <$> (Item valType contract name <$> checkIxs (getPosn k) env [k] [keyType])
  <*> checkExpr env valType val

-- | Typechecks a postcondition, returning typed versions of its storage updates and return expression.
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

-- | Typechecks a non-constant rewrite.
checkStorageExpr :: Env -> U.Pattern -> U.Expr -> Err StorageUpdate
checkStorageExpr _ (U.PWild _) _ = error "TODO: add support for wild storage to checkStorageExpr"
checkStorageExpr env@Env{contract,store} (U.PEntry p name args) expr = case Map.lookup name store of
  Just (StorageValue (FromAbi typ)) ->
    Update typ (Item typ contract name []) <$> checkExpr env typ expr
  Just (StorageMapping argtyps (FromAbi valType)) ->
    Update valType
    <$> (Item valType contract name <$> checkIxs p env args (NonEmpty.toList argtyps))
    <*> checkExpr env valType expr
  Nothing ->
    throw (p, "Unknown storage variable " <> show name)

checkPattern :: Env -> U.Pattern -> Err StorageLocation
checkPattern _ (U.PWild _) = error "TODO: checkPattern for Wild storage"
checkPattern env@Env{contract,store} (U.PEntry p name args) =
  case Map.lookup name store of
    Just (StorageValue t)           -> makeLocation t []
    Just (StorageMapping argtyps t) -> makeLocation t (NonEmpty.toList argtyps)
    Nothing                         -> throw (p, "Unknown storage variable " <> show name)
  where
    makeLocation :: AbiType -> [AbiType] -> Err StorageLocation
    makeLocation (FromAbi locType) argTypes =
      Loc locType . Item locType contract name <$> checkIxs @Untimed p env args argTypes

checkIffs :: Env -> [U.IffH] -> Err [Exp ABoolean Untimed]
checkIffs env = foldr check (pure [])
  where
    check (U.Iff   _     exps) acc = mappend <$> traverse (checkExpr env SBoolean) exps <*> acc
    check (U.IffIn _ typ exps) acc = mappend <$> traverse (fmap (bound typ) . checkExpr env SInteger) exps <*> acc

bound :: AbiType -> Exp AInteger t -> Exp ABoolean t
bound typ e = And nowhere (LEQ nowhere (lowerBound typ) e) $ LEQ nowhere e (upperBound typ)

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

-- | Attempt to construct a `TypedExp` whose type matches the supplied `AbiType`.
-- The target timing parameter will be whatever is required by the caller.
checkAbiExpr :: Typeable t => Env -> U.Expr -> AbiType -> Err (TypedExp t)
checkAbiExpr env e (FromAbi typ) = TExp typ <$> checkExpr env typ e

-- | Attempt to typecheck an untyped expression as any possible type.
typedExp :: Typeable t => Env -> U.Expr -> Err (TypedExp t)
typedExp env e = fromMaybe (error $ "Internal error: Type.typedExp. Expr: " <> show e)
                 $ notAtPosn (getPosn e)
                 [ TExp SInteger <$> checkExpr env SInteger e
                 , TExp SBoolean <$> checkExpr env SBoolean e
                 , TExp SByteStr <$> checkExpr env SByteStr e
                 ]

-- | Check the type of an expression and construct a typed expression
checkExpr :: forall a t. Typeable t => Env -> SType a -> U.Expr -> Err (Exp a t)
checkExpr env typ e = case (typ, e) of
  -- Boolean expressions
  (SBoolean, U.ENot    p v1)    -> Neg  p <$> checkExpr env SBoolean v1
  (SBoolean, U.EAnd    p v1 v2) -> And  p <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  (SBoolean, U.EOr     p v1 v2) -> Or   p <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  (SBoolean, U.EImpl   p v1 v2) -> Impl p <$> checkExpr env SBoolean v1 <*> checkExpr env SBoolean v2
  (SBoolean, U.ELT     p v1 v2) -> LT  p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.ELEQ    p v1 v2) -> LEQ p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.EGEQ    p v1 v2) -> GEQ p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.EGT     p v1 v2) -> GT  p  <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SBoolean, U.EEq     p v1 v2) -> polycheck p env Eq v1 v2
  (SBoolean, U.ENeq    p v1 v2) -> polycheck p env NEq v1 v2
  (SBoolean, U.BoolLit p v1)    -> pure $ LitBool p v1
  -- Arithemetic expressions
  (SInteger, U.EAdd    p v1 v2) -> Add p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.ESub    p v1 v2) -> Sub p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EMul    p v1 v2) -> Mul p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EDiv    p v1 v2) -> Div p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.EMod    p v1 v2) -> Mod p <$> checkExpr env SInteger v1 <*> checkExpr env SInteger v2
  (SInteger, U.IntLit  p v1 )   -> pure $ LitInt  p v1
  -- Control
  (typ, U.EITE p v1 v2 v3) -> ITE p <$> checkExpr env SBoolean v1 <*> checkExpr env typ v2 <*> checkExpr env typ v3
  -- Environment variables
  (SInteger, U.EnvExp p v1) -> case lookup v1 defaultStore of
    Just AInteger -> pure $ IntEnv p v1
    Just AByteStr -> throw (p, "Environment variable " <> show v1 <> " has type bytestring but an expression of type integer is expected.")
    _            -> throw (p, "Unknown environment variable " <> show v1)
  (SByteStr, U.EnvExp p v1) -> case lookup v1 defaultStore of
    Just AInteger -> throw (p, "Environment variable " <> show v1 <> " has type integer but an expression of type bytestring is expected.")
    Just AByteStr -> pure $ ByEnv p v1
    _            -> throw (p, "Unknown environment variable " <> show v1)
  -- Variable references
  (_, U.EUTEntry   p name es) -> checkEntry p env Neither name typ es
  (_, U.EPreEntry  p name es) -> checkEntry p env Pre name typ es
  (_, U.EPostEntry p name es) -> checkEntry p env Post name typ es
  -- TODO other error for unimplemented
  _ -> throw (getPosn e,"Type mismatch. Expression " <> show e <> " does not have type " <> show typ)

polycheck :: Typeable t => Pn -> Env -> (forall y. Pn -> SType y -> Exp y t -> Exp y t -> Exp x t) -> U.Expr -> U.Expr -> Err (Exp x t)
polycheck pn env cons e1 e2 = fromMaybe (error $ "Internal error: Type.polycheck. Expr1: " <> show e1)
  $ notAtPosn (getPosn e1)
  [ cons pn SInteger <$> checkExpr env SInteger e1 <*> checkExpr env SInteger e2
  , cons pn SBoolean <$> checkExpr env SBoolean e1 <*> checkExpr env SBoolean e2
  , cons pn SByteStr <$> checkExpr env SByteStr e1 <*> checkExpr env SByteStr e2
  ]


checkEq :: forall a b. Pn -> SType a -> SType b -> Err ()
checkEq _ SInteger SInteger = pure ()
checkEq _ SBoolean SBoolean = pure ()
checkEq _ SByteStr SByteStr = pure ()
checkEq pn t1 t2 = throw (pn, "Type " <> show t1 <> " should match type " <> show t2)

-- XXX why different t t0
-- Try to construct a reference to a calldata variable or an item in storage.
checkEntry :: forall t a t0. Typeable t => Typeable t0 => Pn -> Env -> Time t0 -> Id -> SType a -> [U.Expr] -> Err (Exp a t)
checkEntry pn env@Env{contract,store,calldata} timing name typ es = case (Map.lookup name store, Map.lookup name calldata) of
  (Nothing, Nothing) -> throw (pn, "Unknown variable " <> name)
  (Just _, Just _)   -> throw (pn, "Ambiguous variable " <> name)
  (Nothing, Just (FromAct varType)) ->
    if isTimed timing then throw (pn, "Calldata var cannot be pre/post")
    else Var pn typ name <$ checkEq pn typ varType
  (Just (StorageValue (FromAbi varTyp)), Nothing)      -> makeEntry typ [] <* checkEq pn typ varTyp
  (Just (StorageMapping ts (FromAbi varTyp)), Nothing) -> makeEntry typ (NonEmpty.toList ts) <* checkEq pn typ varTyp
  where
    makeEntry :: SType a -> [AbiType] -> Err (Exp a t)
    makeEntry entryType ts = checkTime <*> (TEntry pn timing . Item entryType contract name <$> checkIxs pn env es ts)

    checkTime :: Err (Exp x t0 -> Exp x t)
    checkTime = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

 
-- | Checks that there are as many expressions as expected by the types,
-- and checks that each one of them agree with its type.
checkIxs :: forall t. Typeable t => Pn -> Env -> [U.Expr] -> [AbiType] -> Err [TypedExp t]
checkIxs pn env exprs types = if length exprs /= length types
                              then throw (pn, "Index mismatch for entry")
                              else traverse (uncurry $ checkAbiExpr env) (exprs `zip` types)
