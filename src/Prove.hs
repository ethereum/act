{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language DeriveDataTypeable #-}
{-# Language DeriveAnyClass #-}

module Prove
  ( queries
  , Ctx(..)
  , When(..)
  , SMType(..)
  , Method
  , getLoc
  , get
  , mkContext
  , mkConstraint
  , symExpBool
  , symExpInt
  , symExpBytes
  , symExp
  , nameFromItem
  , nameFromEnv
  , nameFromDecl
  , concatMapM
  ) where

import Control.Monad (when, foldM)
import Data.ByteString (ByteString)
import Data.ByteString.UTF8 (toString)
import Data.List ((\\), nub)
import Data.Data
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), (!!))
import Data.Map.Strict as Map (Map, lookup, fromList, toList, empty, insert)
import Data.Maybe

import Data.SBV hiding (name)
import Data.SBV.Either (either)
import Data.SBV.Tuple (tuple)
import Data.SBV.String ((.++), subStr)

import RefinedAst
import Syntax (Id, Interface(..), Decl(..), EthEnv(..))
import Type (metaType)
import Print (prettyEnv)
import Extract (locsFromExp, getLoc)

-- *** Interface *** --


{-|
   For each invariant claim, we build an SMT query for each pass behaviour in the transtion system.

   If the behaviour is a constructor, the query asks the solver to find instances where:

   - the preconditions hold
   - the storage values in the poststate match those specified by the `creates` block of the constructor holds
   - the invariant does not hold over the post state or the postconditions do not hold over the poststate

   If the behaviour is a method, the query asks the solver to find instances where:

   - the invariant holds over the pre state
   - the preconditions hold
   - all storage variables are within the range specified by their type
   - a predicate relating the pre and post state according to the specification in the `storage` block holds
   - the invariant does not hold over the post state or the postconditions do not hold over the poststate

   If all of the queries for an invariant claim return `unsat`, then we have proved two things:

   1. The invariant holds over the post state
   2. The postconditions hold for every method level behaviour
-}
queries :: [Claim] -> [(Invariant, [Symbolic ()])]
queries claims = fmap mkQueries gathered
  where
    gathered = fmap (\inv -> (inv, definition inv, getBehaviours inv)) invariants
    invariants = [i | I i <- claims]
    getBehaviours (Invariant c _ _) = filter (\b -> isPass b && contractMatches c b) [b | B b <- claims]
    definition (Invariant c _ _) = head $ filter (\b -> Pass == _cmode b && _cname b == c) [c' | C c' <- claims]
    contractMatches c b = c == (_contract b)
    isPass b = (_mode b) == Pass


-- *** Data *** --


type Contract = Id
type Method = Id
type Args = Map Id SMType
type Storage = Map Id (SMType, SMType)
type Env = Map Id SMType
data When = Pre | Post
  deriving (Eq, Show)

data Ctx = Ctx Contract Method Args Storage Env

data SAtomic = SymInteger (SBV Integer)
             | SymBool    (SBV Bool)
             | SymBytes   (SBV String)

-- We need this awkward definition to be able to get a HasKind instance,
-- allowing us to use produce the Mapping type below...
type Atomic = Either Integer
             (Either Bool String)

data Idx = One    Atomic
         | Two   (Atomic, Atomic)
         | Three (Atomic, Atomic, Atomic)
         | Four  (Atomic, Atomic, Atomic, Atomic)
         | Five  (Atomic, Atomic, Atomic, Atomic, Atomic)
         | Six   (Atomic, Atomic, Atomic, Atomic, Atomic, Atomic)
         | Seven (Atomic, Atomic, Atomic, Atomic, Atomic, Atomic, Atomic)
         deriving (Data, Read, HasKind)

newtype Mapping = Mapping (SArray Idx Atomic)

data SMType = A SAtomic | M Mapping


-- *** Query Construction *** --


mkQueries :: (Invariant, Constructor, [Behaviour]) -> (Invariant, [Symbolic ()])
mkQueries (inv, constr, behvs) = (inv, inits:methods)
  where
    inits = mkInit inv constr
    methods = mkMethod inv constr <$> behvs

mkInit :: Invariant -> Constructor -> Symbolic ()
mkInit inv@(Invariant _ invConds invExp) constr@(Constructor _ _ _ preConds postConds statedef otherstorages) = do
  ctx <- mkContext inv (Right constr)

  let
    mkBool = symExpBool ctx
    storages = (Right <$> statedef) <> otherstorages
    postInv' = mkBool Post invExp
    preCond' = mkBool Pre (mconcat (nub $ preConds <> invConds))
    postCond' = mkBool Pre (mconcat postConds)
    stateUpdates' = mkStorageConstraints ctx storages (references inv (Right constr))

  constrain $ preCond' .&& sAnd stateUpdates' .&& (sNot postCond' .|| sNot postInv')

mkMethod :: Invariant -> Constructor -> Behaviour -> Symbolic ()
mkMethod inv@(Invariant _ invConds invExp) initBehv behv = do
  ctx@(Ctx c m _ store' env) <- mkContext inv (Left behv)

  let (Interface _ initdecls) = _cinterface initBehv
  initArgs <- mkArgs c m initdecls
  let invCtx = Ctx c m initArgs store' env

  let
    preInv = symExpBool invCtx Pre invExp
    postInv = symExpBool invCtx Post invExp
    invConds' = symExpBool invCtx Pre (mconcat (invConds \\ (_preconditions behv)))
    preCond = symExpBool ctx Pre (mconcat $ _preconditions behv)
    postCond = symExpBool ctx Pre (mconcat $ _postconditions behv)
    stateUpdates = mkStorageConstraints ctx (_stateUpdates behv) (references inv (Left behv))

  constrain $ preInv .&& preCond .&& invConds'
           .&& sAnd stateUpdates
           .&& (sNot postCond .|| sNot postInv)

mkContext :: Invariant -> Either Behaviour Constructor -> Symbolic Ctx
mkContext inv@(Invariant contract _ _) spec = do
  let (c1, decls, method) = Prelude.either
        (\(Behaviour m _ c (Interface _ ds) _ _ _ _) -> (c,ds, m))
        (\(Constructor c _ (Interface _ ds) _ _ _ _) -> (c, ds, "init"))
        spec
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1) $ error "Internal error: contract mismatch"

  store <- foldM (mkSymStorage method) Map.empty (references inv spec)
  env <- mkEnv contract method
  args <- mkArgs contract method decls

  return $ Ctx contract method args store env

mkArgs :: Contract -> Method -> [Decl] -> Symbolic (Map Id SMType)
mkArgs c m ds = Map.fromList <$> mapM (mkSymArg c m) ds

references :: Invariant -> Either Behaviour Constructor -> [StorageLocation]
references (Invariant _ _ invExp) spec
  = nub $ (getLoc <$> updates) <> locsFromExp invExp
      where
        updates = Prelude.either
          (\(Behaviour _ _ _ _ _ _ u _) -> u)
          (\(Constructor _ _ _ _ _ i cs) -> (Right <$> i) <> cs)
          spec

mkSymArg :: Contract -> Method -> Decl -> Symbolic (Id, SMType)
mkSymArg contract method decl@(Decl typ _) = case metaType typ of
  Integer -> do
    v <- sInteger name
    return (name, A $ SymInteger v)
  Boolean -> do
    v <- sBool name
    return (name, A $ SymBool v)
  ByteStr -> do
    v <- sString name
    return (name, A $ SymBytes v)
  where
    name = nameFromDecl contract method decl

mkSymStorage :: Method
             -> Map Id (SMType, SMType)
             -> StorageLocation
             -> Symbolic (Map Id (SMType, SMType))
mkSymStorage method store loc = case loc of
  IntLoc item@DirectInt {} -> do
    v <- A . SymInteger <$> sInteger (pre item)
    w <- A . SymInteger <$> sInteger (post item)
    return $ Map.insert (name item) (v, w) store

  BoolLoc item@DirectBool {} -> do
    v <- A . SymBool <$> sBool (pre item)
    w <- A . SymBool <$> sBool (post item)
    return $ Map.insert (name item) (v, w) store

  BytesLoc item@DirectBytes {} -> do
    v <- A . SymBytes <$> sString (pre item)
    w <- A . SymBytes <$> sString (post item)
    return $ Map.insert (name item) (v, w) store

  IntLoc item@MappedInt {} -> case Map.lookup (name item) store of
      Just (M _, M _) -> return store
      Just (_, _) -> error "internal error: smt type mismatch"
      Nothing -> do
        v <- M . Mapping <$> newArray (pre item) Nothing
        w <- M . Mapping <$> newArray (pre item) Nothing
        return $ Map.insert (name item) (v, w) store

  BoolLoc item@MappedBool {} -> case Map.lookup (name item) store of
      Just (M _, M _) -> return store
      Just (_, _) -> error "internal error: smt type mismatch"
      Nothing -> do
        v <- M . Mapping <$> newArray (pre item) Nothing
        w <- M . Mapping <$> newArray (pre item) Nothing
        return $ Map.insert (name item) (v, w) store

  BytesLoc item@MappedBytes {} -> case Map.lookup (name item) store of
      Just (M _, M _) -> return store
      Just (_, _) -> error "internal error: smt type mismatch"
      Nothing -> do
        v <- M . Mapping <$> newArray (pre item) Nothing
        w <- M . Mapping <$> newArray (pre item) Nothing
        return $ Map.insert (name item) (v, w) store
  where
    name :: TStorageItem a -> Id
    name i = nameFromItem method i

    pre :: TStorageItem a -> Id
    pre i = (name i) ++ "_pre"

    post :: TStorageItem a -> Id
    post i = (name i) ++ "_post"

mkEnv :: Contract -> Method -> Symbolic Env
mkEnv contract method = Map.fromList <$> mapM makeSymbolic
  [ Caller, Callvalue, Calldepth, Origin, Blockhash, Blocknumber
  , Difficulty, Chainid, Gaslimit, Coinbase, Timestamp, This, Nonce ]
  where
    makeSymbolic :: EthEnv -> Symbolic (Id, SMType)
    makeSymbolic Blockhash = mkBytes Blockhash
    makeSymbolic env = mkInt env

    mkInt :: EthEnv -> Symbolic (Id, SMType)
    mkInt env = do
      let k = nameFromEnv contract method env
      v <- A . SymInteger <$> sInteger k
      return (k, v)

    mkBytes :: EthEnv -> Symbolic (Id, SMType)
    mkBytes env = do
      let k = nameFromEnv contract method env
      v <- A . SymBytes <$> sString k
      return (k, v)

-- | TODO: wtf is going on here?
mkStorageConstraints :: Ctx -> [Either StorageLocation StorageUpdate] -> [StorageLocation] -> [SBV Bool]
mkStorageConstraints ctx updates locs
  = mkConstraint ctx <$> (unchanged <> updates)
  where
    unchanged = Left <$> (locs \\ (fmap getLoc updates))

-- | produces an expression that describes the expected value of the poststate for the given storage variable
mkConstraint :: Ctx -> (Either StorageLocation StorageUpdate) -> SBV Bool
mkConstraint ctx (Left loc) = fromLocation ctx loc
mkConstraint ctx (Right update) = fromUpdate ctx update

-- | produces an expression that returns true if the prestate and poststate are equal
fromLocation :: Ctx -> StorageLocation -> SBV Bool
fromLocation ctx loc = case loc of
  IntLoc item -> getVar ctx item (catInts . (fst <$>)) .== getVar ctx item (catInts . (snd <$>))
  BoolLoc item -> getVar ctx item (catBools . (fst <$>)) .== getVar ctx item (catBools . (snd <$>))
  BytesLoc item -> getVar ctx item (catBytes . (fst <$>)) .== getVar ctx item (catBytes . (snd <$>))

-- | produces an expression that returns true if the poststate is equal to the rhs of the update
fromUpdate :: Ctx -> StorageUpdate -> SBV Bool
fromUpdate ctx update = case update of
  IntUpdate item e -> getVar ctx item (catInts . (snd <$>)) .== symExpInt ctx Pre e
  BoolUpdate item e -> getVar ctx item (catBools . (snd <$>)) .== symExpBool ctx Pre e
  BytesUpdate item e -> getVar ctx item (catBytes . (snd <$>)) .== symExpBytes ctx Pre e

getVar :: (Show b) => Ctx -> TStorageItem a -> (Map Id (SMType, SMType) -> Map Id b) -> b
getVar (Ctx _ m _ store _) i f = get (nameFromItem m i) (f store)


-- *** Symbolic Expression Construction *** ---


symExp :: Ctx -> When -> ReturnExp -> SMType
symExp ctx whn ret = case ret of
  ExpInt e -> A . SymInteger $ symExpInt ctx whn e
  ExpBool e -> A . SymBool $ symExpBool ctx whn e
  ExpBytes e -> A . SymBytes $ symExpBytes ctx whn e

symExpBool :: Ctx -> When -> Exp Bool -> SBV Bool
symExpBool ctx@(Ctx c m args store _) w e = case e of
  And a b   -> (symExpBool ctx w a) .&& (symExpBool ctx w b)
  Or a b    -> (symExpBool ctx w a) .|| (symExpBool ctx w b)
  Impl a b  -> (symExpBool ctx w a) .=> (symExpBool ctx w b)
  LE a b    -> (symExpInt ctx w a) .< (symExpInt ctx w b)
  LEQ a b   -> (symExpInt ctx w a) .<= (symExpInt ctx w b)
  GE a b    -> (symExpInt ctx w a) .> (symExpInt ctx w b)
  GEQ a b   -> (symExpInt ctx w a) .>= (symExpInt ctx w b)
  NEq a b   -> sNot (symExpBool ctx w (Eq a b))
  Neg a     -> sNot (symExpBool ctx w a)
  LitBool a -> literal a
  BoolVar a -> get (nameFromArg c m a) (catBools args)
  TEntry a  -> get (nameFromItem m a) (catBools store')
  ITE x y z -> ite (symExpBool ctx w x) (symExpBool ctx w y) (symExpBool ctx w z)
  Eq (a :: Exp t) (b :: Exp t) -> case eqT @t @Integer of
    Just Refl -> symExpInt ctx w a .== symExpInt ctx w b
    Nothing -> case eqT @t @Bool of
      Just Refl -> symExpBool ctx w a .== symExpBool ctx w b
      Nothing -> case eqT @t @ByteString of
        Just Refl -> symExpBytes ctx w a .== symExpBytes ctx w b
        Nothing -> error "Internal Error: invalid expression type"
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store

symExpInt :: Ctx -> When -> Exp Integer -> SBV Integer
symExpInt ctx@(Ctx c m args store env) w e = case e of
  Add a b   -> (symExpInt ctx w a) + (symExpInt ctx w b)
  Sub a b   -> (symExpInt ctx w a) - (symExpInt ctx w b)
  Mul a b   -> (symExpInt ctx w a) * (symExpInt ctx w b)
  Div a b   -> (symExpInt ctx w a) `sDiv` (symExpInt ctx w b)
  Mod a b   -> (symExpInt ctx w a) `sMod` (symExpInt ctx w b)
  Exp a b   -> (symExpInt ctx w a) .^ (symExpInt ctx w b)
  LitInt a  -> literal a
  IntMin a  -> literal $ intmin a
  IntMax a  -> literal $ intmax a
  UIntMin a -> literal $ uintmin a
  UIntMax a -> literal $ uintmax a
  IntVar a  -> get (nameFromArg c m a) (catInts args)
  TEntry a  -> case a of
    DirectInt _ _ -> get (nameFromItem m a) (catInts store')
    MappedInt _ _ idxs -> let
        arr = fromJust $ Map.lookup (nameFromItem m a) store'
      in case arr of
        M (Mapping arr') -> let res = readArray arr' (mkIdx ctx w idxs)
                            in Data.SBV.Either.either id (error "fuck") res
        _ -> error "Internal Error: type mismatch"
  IntEnv a -> get (nameFromEnv c m a) (catInts env)
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE x y z -> ite (symExpBool ctx w x) (symExpInt ctx w y) (symExpInt ctx w z)
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store

mkIdx :: NonEmpty ReturnExp -> SBV Idx
mkIdx = One . symbolize . unwrapReturnExp . toTuple1

symbolize :: (a) -> SBV b
symbolize = undefined

unwrapReturnExp :: (ReturnExp) -> (a)
unwrapReturnExp = undefined

toTuple1 :: NonEmpty a -> (a)
toTuple1 = undefined

symExpBytes :: Ctx -> When -> Exp ByteString -> SBV String
symExpBytes ctx@(Ctx c m args store env) w e = case e of
  Cat a b -> (symExpBytes ctx w a) .++ (symExpBytes ctx w b)
  ByVar a  -> get (nameFromArg c m a) (catBytes args)
  ByStr a -> literal a
  ByLit a -> literal $ toString a
  TEntry a  -> get (nameFromItem m a) (catBytes store')
  Slice a x y -> subStr (symExpBytes ctx w a) (symExpInt ctx w x) (symExpInt ctx w y)
  ByEnv a -> get (nameFromEnv c m a) (catBytes env)
  ITE x y z -> ite (symExpBool ctx w x) (symExpBytes ctx w y) (symExpBytes ctx w z)
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store


-- *** SMT Variable Names *** --


nameFromItem :: Method -> TStorageItem a -> Id
nameFromItem method item = case item of
  DirectInt c name -> c @@ method @@ name
  DirectBool c name -> c @@ method @@ name
  DirectBytes c name -> c @@ method @@ name
  MappedInt c name _ -> c @@ method @@ name
  MappedBool c name _ -> c @@ method @@ name
  MappedBytes c name _ -> c @@ method @@ name

nameFromDecl :: Contract -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: Contract -> Method -> Id -> Id
nameFromArg contract method name = contract @@ method @@ name

nameFromEnv :: Contract -> Method -> EthEnv -> Id
nameFromEnv contract method e = contract @@ method @@ (prettyEnv e)

(@@) :: Id -> Id -> Id
x @@ y = x <> "_" <> y


-- *** Utils *** --


get :: (Show a, Ord a, Show b) => a -> Map a b -> b
get name vars = fromMaybe (error (show name <> " not found in " <> show vars)) $ Map.lookup name vars

catInts :: Map Id SMType -> Map Id (SBV Integer)
catInts m = Map.fromList [(name, i) | (name, A (SymInteger i)) <- Map.toList m]

catBools :: Map Id SMType -> Map Id (SBV Bool)
catBools m = Map.fromList [(name, i) | (name, A (SymBool i)) <- Map.toList m]

catBytes :: Map Id SMType -> Map Id (SBV String)
catBytes m = Map.fromList [(name, i) | (name, A (SymBytes i)) <- Map.toList m]

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM op' = foldr f (pure [])
    where f x xs = do x' <- op' x; if null x' then xs else do xs' <- xs; pure $ x'++xs'
