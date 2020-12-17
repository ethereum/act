{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}

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
  , getContractId
  , getContainerId
  , getContainerIxs
  , contractsInvolved
  , concatMapM
  ) where

import Control.Monad (when)
import Data.ByteString (ByteString)
import Data.ByteString.UTF8 (toString)
import Data.List (intercalate, (\\), nub)
import Data.List.NonEmpty as NonEmpty (toList)
import Data.Map.Strict as Map (Map, lookup, fromList, toList)
import Data.Maybe

import Data.SBV hiding (name)
import Data.SBV.String ((.++), subStr)

import RefinedAst
import Syntax (Id, Interface(..), Decl(..), EthEnv(..))
import Type (metaType, getLoc)
import Enrich (mkStorageBounds)
import Print (prettyEnv)

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
    gathered = fmap (\inv -> (inv, store, definition inv, getBehaviours inv)) invariants
    invariants = [i | I i <- claims]
    store = head [s | S s <- claims] -- TODO: refine AST so we don't need this head anymore
    getBehaviours (Invariant c _) = filter (\b -> isPass b && contractMatches c b) [b | B b <- claims]
    definition (Invariant c _) = head $ filter (\b -> Pass == _cmode b && _cname b == c) [c' | C c' <- claims]
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
  deriving (Show)

data SMType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes (SBV String)
  deriving (Show)

instance EqSymbolic SMType where
  SymInteger a .== SymInteger b = a .== b
  SymBool a .== SymBool b = a .== b
  SymBytes a .== SymBytes b = a .== b
  _ .== _ = literal False


-- *** Query Construction *** --


mkQueries :: (Invariant, Store, Constructor, [Behaviour]) -> (Invariant, [Symbolic ()])
mkQueries (inv, store, constr, behvs) = (inv, inits:methods)
  where
    inits = mkInit inv constr
    methods = mkMethod inv store constr <$> behvs

mkInit :: Invariant -> Constructor -> Symbolic ()
mkInit inv@(Invariant _ e) constr@(Constructor _ _ _ preConds postConds statedef otherstorages) = do
  ctx <- mkContext inv (Right constr)

  let
    mkBool = symExpBool ctx
    storages = (Right <$> statedef) <> otherstorages
    postInv' = mkBool Post e
    preCond' = mkBool Pre (mconcat preConds)
    postCond' = mkBool Pre (mconcat postConds)

    stateUpdates' = mkStorageConstraints ctx storages (nub $ (getLoc <$> storages) <> locsFromExp e)

  constrain $ preCond' .&& sAnd stateUpdates' .&& (sNot postCond' .|| sNot postInv')

mkMethod :: Invariant -> Store -> Constructor -> Behaviour -> Symbolic ()
mkMethod inv@(Invariant _ e) store initBehv behv = do
  ctx@(Ctx c m _ store' env) <- mkContext inv (Left behv)

  let (Interface _ initdecls) = _cinterface initBehv
  initArgs <- mkArgs c m initdecls
  let invCtx = Ctx c m initArgs store' env

  let
    locs = references inv behv
    preInv = symExpBool invCtx Pre e
    postInv = symExpBool invCtx Post e
    preCond = symExpBool ctx Pre (mconcat $ _preconditions behv)
    postCond = symExpBool ctx Pre (mconcat $ _postconditions behv)
    stateUpdates = mkStorageConstraints ctx (_stateUpdates behv) locs
    storageBounds = symExpBool ctx Pre $ mconcat <$> mkStorageBounds store $ Left <$> locs

  constrain $ preInv .&& preCond .&& storageBounds
           .&& sAnd stateUpdates
           .&& (sNot postCond .|| sNot postInv)


mkContext :: Invariant -> Either Behaviour Constructor -> Symbolic Ctx
mkContext (Invariant contract e) spec = do
  let (c1, decls, updates, method) = either
        (\(Behaviour m _ c (Interface _ ds) _ _ u _) -> (c,ds, u, m))
        (\(Constructor c _ (Interface _ ds) _ _ init' cs) -> (c, ds, ((Right <$> init') <> cs), "init"))
        spec
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1) $ error "Internal error: contract mismatch"

  let locs = nub $ (getLoc <$> updates) <> locsFromExp e

  store <- Map.fromList <$> mapM (mkSymStorage method) locs
  env <- mkEnv contract method
  args <- mkArgs contract method decls

  return $ Ctx contract method args store env

mkArgs :: Contract -> Method -> [Decl] -> Symbolic (Map Id SMType)
mkArgs c m ds = Map.fromList <$> mapM (mkSymArg c m) ds

references :: Invariant -> Behaviour -> [StorageLocation]
references (Invariant _ inv) (Behaviour _ _ _ _ _ _ updates _)
  = nub $ (getLoc <$> updates) <> locsFromExp inv

mkSymArg :: Contract -> Method -> Decl -> Symbolic (Id, SMType)
mkSymArg contract method decl@(Decl typ _) = case metaType typ of
  Integer -> do
    v <- sInteger name
    return (name, SymInteger v)
  Boolean -> do
    v <- sBool name
    return (name, SymBool v)
  ByteStr -> do
    v <- sString name
    return (name, SymBytes v)
  where
    name = nameFromDecl contract method decl

mkSymStorage :: Method -> StorageLocation -> Symbolic (Id, (SMType, SMType))
mkSymStorage method loc = case loc of
  IntLoc item -> do
    v <- SymInteger <$> sInteger (name item)
    w <- SymInteger <$> sInteger ((name item) ++ "_post")
    return (name item, (v, w))
  BoolLoc item -> do
    v <- SymBool <$> sBool (name item)
    w <- SymBool <$> sBool ((name item) ++ "_post")
    return (name item, (v, w))
  BytesLoc item -> do
    v <- SymBytes <$> sString (name item)
    w <- SymBytes <$> sString ((name item) ++ "_post")
    return (name item, (v, w))
  where
    name :: TStorageItem a -> Id
    name i = nameFromItem method i

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
      v <- SymInteger <$> sInteger k
      return (k, v)

    mkBytes :: EthEnv -> Symbolic (Id, SMType)
    mkBytes env = do
      let k = nameFromEnv contract method env
      v <- SymBytes <$> sString k
      return (k, v)

mkStorageConstraints :: Ctx -> [Either StorageLocation StorageUpdate] -> [StorageLocation] -> [SBV Bool]
mkStorageConstraints ctx updates locs
  = mkConstraint ctx <$> (unchanged <> updates)
  where
    unchanged = Left <$> (locs \\ (fmap getLoc updates))

mkConstraint :: Ctx -> (Either StorageLocation StorageUpdate) -> SBV Bool
mkConstraint ctx (Left loc) = fromLocation ctx loc
mkConstraint ctx (Right update) = fromUpdate ctx update

getVar :: (Show b) => Ctx -> TStorageItem a -> (Map Id (SMType, SMType) -> Map Id b) -> b
getVar (Ctx _ m _ store _) i f = get (nameFromItem m i) (f store)

fromLocation :: Ctx -> StorageLocation -> SBV Bool
fromLocation ctx loc = case loc of
  IntLoc item -> getVar ctx item (catInts . (fst <$>)) .== getVar ctx item (catInts . (snd <$>))
  BoolLoc item -> getVar ctx item (catBools . (fst <$>)) .== getVar ctx item (catBools . (snd <$>))
  BytesLoc item -> getVar ctx item (catBytes . (fst <$>)) .== getVar ctx item (catBytes . (snd <$>))

fromUpdate :: Ctx -> StorageUpdate -> SBV Bool
fromUpdate ctx update = case update of
  IntUpdate item e -> getVar ctx item (catInts . (snd <$>)) .== symExpInt ctx Pre e
  BoolUpdate item e -> getVar ctx item (catBools . (snd <$>)) .== symExpBool ctx Pre e
  BytesUpdate item e -> getVar ctx item (catBytes . (snd <$>)) .== symExpBytes ctx Pre e


-- *** Symbolic Expression Construction *** ---

symExp :: Ctx -> When -> ReturnExp -> SMType
symExp ctx whn ret = case ret of
  ExpInt e -> SymInteger $ symExpInt ctx whn e
  ExpBool e -> SymBool $ symExpBool ctx whn e
  ExpBytes e -> SymBytes $ symExpBytes ctx whn e

symExpBool :: Ctx -> When -> Exp Bool -> SBV Bool
symExpBool ctx@(Ctx c m args store _) w e = case e of
  And a b   -> (symExpBool ctx w a) .&& (symExpBool ctx w b)
  Or a b    -> (symExpBool ctx w a) .|| (symExpBool ctx w b)
  Impl a b  -> (symExpBool ctx w a) .=> (symExpBool ctx w b)
  Eq a b    -> (symExpInt ctx w a) .== (symExpInt ctx w b)
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
  TEntry a  -> get (nameFromItem m a) (catInts store')
  IntEnv a -> get (nameFromEnv c m a) (catInts env)
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE x y z -> ite (symExpBool ctx w x) (symExpInt ctx w y) (symExpInt ctx w z)
 where store' = case w of
         Pre -> fst <$> store
         Post -> snd <$> store

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
  MappedInt c name ixs -> c @@ method @@ name >< showIxs c ixs
  MappedBool c name ixs -> c @@ method @@ name >< showIxs c ixs
  MappedBytes c name ixs -> c @@ method @@ name >< showIxs c ixs
  where
    x >< y = x <> "-" <> y
    showIxs contract ixs = intercalate "-" (NonEmpty.toList $ nameFromExp contract method <$> ixs)

nameFromExp :: Contract -> Method -> ReturnExp -> Id
nameFromExp contract method e = case e of
  ExpInt e' -> nameFromExpInt contract method e'
  ExpBool e' -> nameFromExpBool contract method e'
  ExpBytes e' -> nameFromExpBytes contract method e'

nameFromExpInt :: Contract -> Method -> Exp Integer -> Id
nameFromExpInt c m e = case e of
  Add a b   -> (nameFromExpInt c m a) <> "+" <> (nameFromExpInt c m b)
  Sub a b   -> (nameFromExpInt c m a) <> "-" <> (nameFromExpInt c m b)
  Mul a b   -> (nameFromExpInt c m a) <> "*" <> (nameFromExpInt c m b)
  Div a b   -> (nameFromExpInt c m a) <> "/" <> (nameFromExpInt c m b)
  Mod a b   -> (nameFromExpInt c m a) <> "%" <> (nameFromExpInt c m b)
  Exp a b   -> (nameFromExpInt c m a) <> "^" <> (nameFromExpInt c m b)
  LitInt a  -> show a
  IntMin a  -> show $ intmin a
  IntMax a  -> show $ intmax a
  UIntMin a -> show $ uintmin a
  UIntMax a -> show $ uintmax a
  IntVar a  -> a
  TEntry a  -> nameFromItem m a
  IntEnv a -> nameFromEnv c m a
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE x y z -> "if-" <> nameFromExpBool c m x <> "-then-" <> nameFromExpInt c m y <> "-else-" <> nameFromExpInt c m z

nameFromExpBool :: Contract -> Method -> Exp Bool -> Id
nameFromExpBool c m e = case e of
  And a b   -> nameFromExpBool c m a <> "&&" <> nameFromExpBool c m b
  Or a b    -> nameFromExpBool c m a <> "|" <> nameFromExpBool c m b
  Impl a b  -> nameFromExpBool c m a <> "=>" <> nameFromExpBool c m b
  Eq a b    -> nameFromExpInt c m a <> "==" <> nameFromExpInt c m b
  LE a b    -> nameFromExpInt c m a <> "<" <> nameFromExpInt c m b
  LEQ a b   -> nameFromExpInt c m a <> "<=" <> nameFromExpInt c m b
  GE a b    -> nameFromExpInt c m a <> ">" <> nameFromExpInt c m b
  GEQ a b   -> nameFromExpInt c m a <> ">=" <> nameFromExpInt c m b
  NEq a b   -> nameFromExpInt c m a <> "=/=" <> nameFromExpInt c m b
  Neg a     -> "~" <> nameFromExpBool c m a
  LitBool a -> show a
  BoolVar a -> nameFromArg c m a
  TEntry a  -> nameFromItem m a
  ITE x y z -> "if-" <> nameFromExpBool c m x <> "-then-" <> nameFromExpBool c m y <> "-else-" <> nameFromExpBool c m z

nameFromExpBytes :: Contract -> Method -> Exp ByteString -> Id
nameFromExpBytes c m e = case e of
  Cat a b -> nameFromExpBytes c m a <> "++" <> nameFromExpBytes c m b
  ByVar a  -> nameFromArg c m a
  ByStr a -> show a
  ByLit a -> show a
  TEntry a  -> nameFromItem m a
  Slice a x y -> nameFromExpBytes c m a <> "[" <> show x <> ":" <> show y <> "]"
  ByEnv a -> nameFromEnv c m a
  ITE x y z -> "if-" <> nameFromExpBool c m x <> "-then-" <> nameFromExpBytes c m y <> "-else-" <> nameFromExpBytes c m z

nameFromDecl :: Contract -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: Contract -> Method -> Id -> Id
nameFromArg contract method name = contract @@ method @@ name

nameFromEnv :: Contract -> Method -> EthEnv -> Id
nameFromEnv contract method e = contract @@ method @@ (prettyEnv e)

(@@) :: Id -> Id -> Id
x @@ y = x <> "_" <> y

-- *** Storage Location Extraction *** --

locsFromExp :: Exp a -> [StorageLocation]
locsFromExp e = case e of
  And a b   -> (locsFromExp a) <> (locsFromExp b)
  Or a b    -> (locsFromExp a) <> (locsFromExp b)
  Impl a b  -> (locsFromExp a) <> (locsFromExp b)
  Eq a b    -> (locsFromExp a) <> (locsFromExp b)
  LE a b    -> (locsFromExp a) <> (locsFromExp b)
  LEQ a b   -> (locsFromExp a) <> (locsFromExp b)
  GE a b    -> (locsFromExp a) <> (locsFromExp b)
  GEQ a b   -> (locsFromExp a) <> (locsFromExp b)
  NEq a b   -> (locsFromExp a) <> (locsFromExp b)
  Neg a     -> (locsFromExp a)
  Add a b   -> (locsFromExp a) <> (locsFromExp b)
  Sub a b   -> (locsFromExp a) <> (locsFromExp b)
  Mul a b   -> (locsFromExp a) <> (locsFromExp b)
  Div a b   -> (locsFromExp a) <> (locsFromExp b)
  Mod a b   -> (locsFromExp a) <> (locsFromExp b)
  Exp a b   -> (locsFromExp a) <> (locsFromExp b)
  Cat a b   -> (locsFromExp a) <> (locsFromExp b)
  Slice a b c -> (locsFromExp a) <> (locsFromExp b) <> (locsFromExp c)
  ByVar _ -> []
  ByStr _ -> []
  ByLit _ -> []
  LitInt _  -> []
  IntMin _  -> []
  IntMax _  -> []
  UIntMin _ -> []
  UIntMax _ -> []
  IntVar _  -> []
  LitBool _ -> []
  BoolVar _ -> []
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  IntEnv _ -> []
  ByEnv _ -> []
  ITE x y z -> (locsFromExp x) <> (locsFromExp y) <> (locsFromExp z)
  TEntry a  -> case a of
    DirectInt contract name -> [IntLoc $ DirectInt contract name]
    DirectBool contract slot -> [BoolLoc $ DirectBool contract slot]
    DirectBytes contract slot -> [BytesLoc $ DirectBytes contract slot]
    MappedInt contract name ixs -> [IntLoc $ MappedInt contract name ixs]
    MappedBool contract name ixs -> [BoolLoc $ MappedBool contract name ixs]
    MappedBytes contract name ixs -> [BytesLoc $ MappedBytes contract name ixs]


-- *** Utils *** --


get :: (Show a, Ord a, Show b) => a -> Map a b -> b
get name vars = fromMaybe (error (show name <> " not found in " <> show vars)) $ Map.lookup name vars

catInts :: Map Id SMType -> Map Id (SBV Integer)
catInts m = Map.fromList [(name, i) | (name, SymInteger i) <- Map.toList m]

catBools :: Map Id SMType -> Map Id (SBV Bool)
catBools m = Map.fromList [(name, i) | (name, SymBool i) <- Map.toList m]

catBytes :: Map Id SMType -> Map Id (SBV String)
catBytes m = Map.fromList [(name, i) | (name, SymBytes i) <- Map.toList m]

contractsInvolved :: Behaviour -> [Id]
contractsInvolved beh =
  getContractId . getLoc <$> _stateUpdates beh

-- TODO: write these with fancy patterns or generics?
getContractId :: StorageLocation -> Id
getContractId (IntLoc (DirectInt a _)) = a
getContractId (BoolLoc (DirectBool a _)) = a
getContractId (BytesLoc (DirectBytes a _)) = a
getContractId (IntLoc (MappedInt a _ _)) = a
getContractId (BoolLoc (MappedBool a _ _)) = a
getContractId (BytesLoc (MappedBytes a _ _)) = a

getContainerId :: StorageLocation -> Id
getContainerId (IntLoc (DirectInt _ a)) = a
getContainerId (BoolLoc (DirectBool _ a)) = a
getContainerId (BytesLoc (DirectBytes _ a)) = a
getContainerId (IntLoc (MappedInt _ a _)) = a
getContainerId (BoolLoc (MappedBool _ a _)) = a
getContainerId (BytesLoc (MappedBytes _ a _)) = a

getContainerIxs :: StorageLocation -> [ReturnExp]
getContainerIxs (IntLoc (DirectInt _ _)) = []
getContainerIxs (BoolLoc (DirectBool _ _)) = []
getContainerIxs (BytesLoc (DirectBytes _ _)) = []
getContainerIxs (IntLoc (MappedInt _ _ ixs)) = NonEmpty.toList ixs
getContainerIxs (BoolLoc (MappedBool _ _ ixs)) = NonEmpty.toList ixs
getContainerIxs (BytesLoc (MappedBytes _ _ ixs)) = NonEmpty.toList ixs

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM op' = foldr f (pure [])
    where f x xs = do x' <- op' x; if null x' then xs else do xs' <- xs; pure $ x'++xs'
