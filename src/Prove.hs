{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Prove (queries) where

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
import Type (metaType, mkStorageBounds)

-- *** Interface *** --


{-|
   For each invariant claim, we build an SMT query for that claim for each pass behaviour in the transtion system.

   If the behaviour is a constructor (creation == True), the query asks the
   solver to find instances where the invariant predicate does not hold over
   the post state once the constructor has run.

   If the behaviour is a method (creation == False), the query asks the solver to find instances where the follwing is true:

   - the invariant holds over the pre state
   - a predicate relating the pre and post state holds
   - the invariant does not hold over the post state

   If all of the queries for an invariant claim return `unsat`, then the invariant must hold over the entire transtion system
-}
queries :: [Claim] -> [(Invariant, [Symbolic ()])]
queries claims = fmap mkQueries gathered
  where
    gathered = fmap (\inv -> (inv, store, getBehaviours inv)) invariants
    invariants = catInvs claims
    store = head (catStores claims) -- TODO: refine AST so we don't need this head anymore
    getBehaviours (Invariant c _) = filter (\b -> isPass b && contractMatches c b) (catBehvs claims)
    contractMatches c b = c == (_contract b)
    isPass b = (_mode b) == Pass


-- *** Data *** --


type Contract = Id
type Method = Id
type Args = Map Id SMType
type Store = Map Id SMType
type Env = Map Id SMType
data When = Pre | Post
  deriving (Eq, Show)

data Ctx = Ctx Contract Method Args Store Env When
  deriving (Show)

data SMType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes (SBV String)
  deriving (Show)


-- *** Query Construction *** --


mkQueries :: (Invariant, Storages, [Behaviour]) -> (Invariant, [Symbolic ()])
mkQueries (inv, store, behvs) = (inv, inits <> methods)
  where
    inits = fmap (mkInit inv) $ filter _creation behvs
    methods = fmap (mkMethod inv store) $ filter (not . _creation) behvs

mkInit :: Invariant -> Behaviour -> Symbolic ()
mkInit inv@(Invariant _ e) behv@(Behaviour _ _ _ _ _ preCond postCond stateUpdates _) = do
  (preCtx, postCtx) <- mkContexts inv behv

  let
    locs = references inv behv
    postInv' = symExpBool postCtx e
    preCond' = symExpBool preCtx preCond
    postCond' = symExpBool postCtx postCond
    stateUpdates' = mkStorageConstraints preCtx postCtx stateUpdates locs

  constrain $ preCond' .&& (sAnd stateUpdates') .&& postCond' .&& (sNot postInv')

mkMethod :: Invariant -> Storages -> Behaviour -> Symbolic ()
mkMethod inv@(Invariant _ e) (Storages store) behv@(Behaviour _ _ _ _ _ preCond postCond stateUpdates _) = do
  (preCtx, postCtx) <- mkContexts inv behv

  let
    locs = references inv behv
    preInv = symExpBool preCtx e
    postInv = symExpBool postCtx e
    preCond' = symExpBool preCtx preCond
    postCond' = symExpBool postCtx postCond
    stateUpdates' = mkStorageConstraints preCtx postCtx stateUpdates locs
    storageBounds = symExpBool preCtx $ mconcat <$> mkStorageBounds store $ Left <$> locs

  constrain $ preInv .&& preCond' .&& storageBounds
           .&& (sAnd stateUpdates')
           .&& postCond' .&& (sNot postInv)

mkContexts :: Invariant -> Behaviour -> Symbolic (Ctx, Ctx)
mkContexts inv@(Invariant contract _) behv@(Behaviour method _ _ c1 (Interface _ decls) _ _ _ _) = do
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1) $ error "Internal error: contract mismatch"

  let locs = references inv behv
  calldata <- Map.fromList <$> mapM (mkSymArg contract method) decls
  preStore <- Map.fromList <$> mapM (mkSymStorage method Pre) locs
  postStore <- Map.fromList <$> mapM (mkSymStorage method Post) locs
  env <- mkEnv contract method

  let
    preCtx = Ctx contract method calldata preStore env Pre
    postCtx = Ctx contract method calldata postStore env Post

  return (preCtx, postCtx)

references :: Invariant -> Behaviour -> [StorageLocation]
references (Invariant _ inv) (Behaviour _ _ _ _ _ _ _ updates _)
  = nub $ (getLoc <$> updates) <> locsFromExp inv

mkSymArg :: Contract -> Method -> Decl -> Symbolic (Id, SMType)
mkSymArg contract method decl@(Decl typ _) = case metaType typ of
  Integer -> do
    v <- sInteger name
    return (name, SymInteger v)
  Boolean -> do
    v <- sBool name
    return $ (name, SymBool v)
  ByteStr -> do
    v <- sString name
    return $ (name, SymBytes v)
  where
    name = nameFromDecl contract method decl

mkSymStorage :: Method -> When -> StorageLocation -> Symbolic (Id, SMType)
mkSymStorage method whn loc = case loc of
  IntLoc item -> do
    v <- sInteger (name item)
    return $ ((name item), SymInteger v)
  BoolLoc item -> do
    v <- sBool (name item)
    return $ (name item, SymBool v)
  BytesLoc item -> do
    v <- sString (name item)
    return $ (name item, SymBytes v)
  where
    name :: TStorageItem a -> Id
    name i = nameFromItem method whn i

mkEnv :: Contract -> Method -> Symbolic Env
mkEnv contract method = Map.fromList <$> mapM mkInt
  [ Caller, Callvalue, Calldepth, Origin, Blockhash, Blocknumber
  , Difficulty, Chainid, Gaslimit, Coinbase, Timestamp, Address, Nonce ]
  where
    mkInt :: EthEnv -> Symbolic (Id, SMType)
    mkInt env = do
      let k = nameFromEnv contract method env
      v <- SymInteger <$> sInteger k
      return (k, v)

mkStorageConstraints :: Ctx -> Ctx -> [Either StorageLocation StorageUpdate] -> [StorageLocation] -> [SBV Bool]
mkStorageConstraints preCtx@(Ctx _ m _ preStore _ pre) (Ctx _ _ _ postStore _ post) updates locs
  = fmap mkConstraint $ (unchanged <> updates)
  where
    unchanged = Left <$> (locs \\ (fmap getLoc updates))

    mkConstraint :: (Either StorageLocation StorageUpdate) -> SBV Bool
    mkConstraint (Left loc) = fromLocation loc
    mkConstraint (Right update) = fromUpdate update

    fromLocation :: StorageLocation -> SBV Bool
    fromLocation loc = case loc of
      IntLoc item -> (lhs item catInts) .== (rhs item catInts)
      BoolLoc item -> (lhs item catBools) .== (rhs item catBools)
      BytesLoc item -> (lhs item catBytes) .== (rhs item catBytes)
      where
        lhs :: (Show b) => TStorageItem a -> (Map Id SMType -> Map Id b) -> b
        lhs i f = get (nameFromItem m post i) (f postStore)
        rhs :: (Show b) => TStorageItem a -> (Map Id SMType -> Map Id b) -> b
        rhs i f = get (nameFromItem m pre i) (f preStore)

    fromUpdate :: StorageUpdate -> SBV Bool
    fromUpdate update = case update of
      IntUpdate item e -> (lhs item catInts) .== (symExpInt preCtx e)
      BoolUpdate item e -> (lhs item catBools) .== (symExpBool preCtx e)
      BytesUpdate item e -> (lhs item catBytes) .== (symExpBytes preCtx e)
      where
        lhs :: (Show b) => TStorageItem a -> (Map Id SMType -> Map Id b) -> b
        lhs i f = get (nameFromItem m post i) (f postStore)


-- *** Symbolic Expression Construction *** ---


symExpBool :: Ctx -> Exp Bool -> SBV Bool
symExpBool ctx@(Ctx c m args store _ w) e = case e of
  And a b   -> (symExpBool ctx a) .&& (symExpBool ctx b)
  Or a b    -> (symExpBool ctx a) .|| (symExpBool ctx b)
  Impl a b  -> (symExpBool ctx a) .=> (symExpBool ctx b)
  Eq a b    -> (symExpInt ctx a) .== (symExpInt ctx b)
  LE a b    -> (symExpInt ctx a) .< (symExpInt ctx b)
  LEQ a b   -> (symExpInt ctx a) .<= (symExpInt ctx b)
  GE a b    -> (symExpInt ctx a) .> (symExpInt ctx b)
  GEQ a b   -> (symExpInt ctx a) .>= (symExpInt ctx b)
  NEq a b   -> sNot (symExpBool ctx (Eq a b))
  Neg a     -> sNot (symExpBool ctx a)
  LitBool a -> literal a
  BoolVar a -> get (nameFromArg c m a) (catBools args)
  TEntry a  -> get (nameFromItem m w a) (catBools store)
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

symExpInt :: Ctx -> Exp Integer -> SBV Integer
symExpInt ctx@(Ctx c m args store env w) e = case e of
  Add a b   -> (symExpInt ctx a) + (symExpInt ctx b)
  Sub a b   -> (symExpInt ctx a) - (symExpInt ctx b)
  Mul a b   -> (symExpInt ctx a) * (symExpInt ctx b)
  Div a b   -> (symExpInt ctx a) `sDiv` (symExpInt ctx b)
  Mod a b   -> (symExpInt ctx a) `sMod` (symExpInt ctx b)
  Exp a b   -> (symExpInt ctx a) .^ (symExpInt ctx b)
  LitInt a  -> literal a
  IntVar a  -> get (nameFromArg c m a) (catInts args)
  TEntry a  -> get (nameFromItem m w a) (catInts store)
  IntEnv a -> get (nameFromEnv c m a) (catInts env)
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

symExpBytes :: Ctx -> Exp ByteString -> SBV String
symExpBytes ctx@(Ctx c m args store env w) e = case e of
  Cat a b -> (symExpBytes ctx a) .++ (symExpBytes ctx b)
  ByVar a  -> get (nameFromArg c m a) (catBytes args)
  ByStr a -> literal a
  ByLit a -> literal $ toString a
  TEntry a  -> get (nameFromItem m w a) (catBytes store)
  Slice a x y -> subStr (symExpBytes ctx a) (symExpInt ctx x) (symExpInt ctx y)
  ByEnv a -> get (nameFromEnv c m a) (catBytes env)
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"


-- *** SMT Variable Names *** --


nameFromItem :: Method -> When -> TStorageItem a -> Id
nameFromItem method prePost item = case item of
  DirectInt c name -> c @@ method @@ name @@ show prePost
  DirectBool c name -> c @@ method @@ name @@ show prePost
  DirectBytes c name -> c @@ method @@ name @@ show prePost
  MappedInt c name ixs -> c @@ method @@ name >< showIxs c ixs >< show prePost
  MappedBool c name ixs -> c @@ method @@ name >< showIxs c ixs >< show prePost
  MappedBytes c name ixs -> c @@ method @@ name >< showIxs c ixs >< show prePost
  where
    x >< y = x <> "-" <> y
    showIxs contract ixs = intercalate "-" (NonEmpty.toList $ nameFromExp contract method prePost <$> ixs)

nameFromExp :: Contract -> Method -> When -> ReturnExp -> Id
nameFromExp contract method prePost e = case e of
  ExpInt e' -> nameFromExpInt contract method prePost e'
  ExpBool e' -> nameFromExpBool contract method prePost e'
  ExpBytes e' -> nameFromExpBytes contract method prePost e'

nameFromExpInt :: Contract -> Method -> When -> Exp Integer -> Id
nameFromExpInt c m w e = case e of
  Add a b   -> (nameFromExpInt c m w a) <> "+" <> (nameFromExpInt c m w b)
  Sub a b   -> (nameFromExpInt c m w a) <> "-" <> (nameFromExpInt c m w b)
  Mul a b   -> (nameFromExpInt c m w a) <> "*" <> (nameFromExpInt c m w b)
  Div a b   -> (nameFromExpInt c m w a) <> "/" <> (nameFromExpInt c m w b)
  Mod a b   -> (nameFromExpInt c m w a) <> "%" <> (nameFromExpInt c m w b)
  Exp a b   -> (nameFromExpInt c m w a) <> "^" <> (nameFromExpInt c m w b)
  LitInt a  -> show a
  IntVar a  -> a
  TEntry a  -> nameFromItem m w a
  IntEnv a -> nameFromEnv c m a
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

nameFromExpBool :: Contract -> Method -> When -> Exp Bool -> Id
nameFromExpBool c m w e = case e of
  And a b   -> (nameFromExpBool c m w a) <> "&&" <> (nameFromExpBool c m w b)
  Or a b    -> (nameFromExpBool c m w a) <> "|" <> (nameFromExpBool c m w b)
  Impl a b  -> (nameFromExpBool c m w a) <> "=>" <> (nameFromExpBool c m w b)
  Eq a b    -> (nameFromExpInt c m w a) <> "==" <> (nameFromExpInt c m w b)
  LE a b    -> (nameFromExpInt c m w a) <> "<" <> (nameFromExpInt c m w b)
  LEQ a b   -> (nameFromExpInt c m w a) <> "<=" <> (nameFromExpInt c m w b)
  GE a b    -> (nameFromExpInt c m w a) <> ">" <> (nameFromExpInt c m w b)
  GEQ a b   -> (nameFromExpInt c m w a) <> ">=" <> (nameFromExpInt c m w b)
  NEq a b   -> (nameFromExpInt c m w a) <> "=/=" <> (nameFromExpInt c m w b)
  Neg a     -> "~" <> (nameFromExpBool c m w a)
  LitBool a -> show a
  BoolVar a -> nameFromArg c m a
  TEntry a  -> nameFromItem m w a
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

nameFromExpBytes :: Contract -> Method -> When -> Exp ByteString -> Id
nameFromExpBytes c m w e = case e of
  Cat a b -> (nameFromExpBytes c m w a) <> "++" <> (nameFromExpBytes c m w b)
  ByVar a  -> nameFromArg c m a
  ByStr a -> show a
  ByLit a -> show a
  TEntry a  -> nameFromItem m w a
  Slice a x y -> (nameFromExpBytes c m w a) <> "[" <> show x <> ":" <> show y <> "]"
  ByEnv a -> nameFromEnv c m a
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

nameFromDecl :: Contract -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: Contract -> Method -> Id -> Id
nameFromArg contract method name = contract @@ method @@ name

nameFromEnv :: Contract -> Method -> EthEnv -> Id
nameFromEnv contract method e = contract @@ method @@ name
  where
    name = case e of
      Caller -> "CALLER"
      Callvalue -> "CALLVALUE"
      Calldepth -> "CALLDEPTH"
      Origin -> "ORIGIN"
      Blockhash -> "BLOCKHASH"
      Blocknumber -> "BLOCKNUMBER"
      Difficulty -> "DIFFICULTY"
      Chainid -> "CHAINID"
      Gaslimit -> "GASLIMIT"
      Coinbase -> "COINBASE"
      Timestamp -> "TIMESTAMP"
      Address -> "ADDRESS"
      Nonce -> "NONCE"

(@@) :: Id -> Id -> Id
x @@ y = x <> "_" <> y

-- *** Storage Location Extraction *** --


getLoc :: Either StorageLocation StorageUpdate -> StorageLocation
getLoc ref = case ref of
  Left loc -> loc
  Right update -> case update of
    IntUpdate item _ -> IntLoc item
    BoolUpdate item _ -> BoolLoc item
    BytesUpdate item _ -> BytesLoc item

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
  IntVar _  -> []
  LitBool _ -> []
  BoolVar _ -> []
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  IntEnv _ -> error "TODO: handle blockchain context in SMT expressions"
  ByEnv _ -> error "TODO: handle blockchain context in SMT expressions"
  ITE _ _ _ -> error "TODO: hande ITE in SMT expresssions"
  TEntry a  -> case a of
    DirectInt contract name -> [IntLoc $ DirectInt contract name]
    DirectBool contract slot -> [BoolLoc $ DirectBool contract slot]
    DirectBytes contract slot -> [BytesLoc $ DirectBytes contract slot]
    MappedInt contract name ixs -> [IntLoc $ MappedInt contract name ixs]
    MappedBool contract name ixs -> [BoolLoc $ MappedBool contract name ixs]
    MappedBytes contract name ixs -> [BytesLoc $ MappedBytes contract name ixs]


-- *** Utils *** --


get :: (Show a) => Id -> Map Id a -> a
get name vars = fromMaybe (error (name <> " not found in " <> show vars)) $ Map.lookup name vars

catInts :: Map Id SMType -> Map Id (SBV Integer)
catInts m = Map.fromList $ go $ Map.toList m
  where
    go ((name, SymInteger i):tl) = (name, i):(go tl)
    go (_:tl) = go tl
    go [] = []

catBools :: Map Id SMType -> Map Id (SBV Bool)
catBools m = Map.fromList $ go $ Map.toList m
  where
    go ((name, SymBool b):tl) = (name, b):(go tl)
    go (_:tl) = go tl
    go [] = []

catBytes :: Map Id SMType -> Map Id (SBV String)
catBytes m = Map.fromList $ go $ Map.toList m
  where
    go ((name, SymBytes b):tl) = (name, b):(go tl)
    go (_:tl) = go tl
    go [] = []
