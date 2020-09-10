{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Prove (queries) where

import Control.Monad (when)
import Data.ByteString (ByteString)
import Data.List (intercalate, (\\), nub)
import Data.List.NonEmpty as NonEmpty (toList)
import Data.Map.Strict as Map (Map, lookup, fromList)
import Data.Maybe

import Data.SBV hiding (name)

import RefinedAst
import Syntax (Id, Interface(..), Decl(..))
import Type (metaType, mkStorageBounds)

-- *** Interface *** --


{-|
   For each Invariant claim build an SMT query consisting of:

   - constants for the pre and post versions of all storage variables used by the transition system
   - boolean predicates over the pre and post storage variables for each pass behaviour
   - a boolean predicate for the invariant
   - an assertion that the invariant does not hold if either of the following is true:
      1. The constructor predicate holds
      2. The invariant holds over the prestate and one of the method level predicates holds

   If this query returns `unsat` then the invariant must hold over the transition system
-}
queries :: [Claim] -> [(Invariant, [Symbolic ()])]
queries claims = fmap mkQueries gathered
  where
    gathered = fmap (\inv -> (inv, store, getBehaviours inv)) invariants
    invariants = catInvs claims
    store = head $ (catStores claims) -- TODO: refine AST so we don't need this head anymore
    getBehaviours (Invariant c _) = filter isPass $ filter (contractMatches c) (catBehvs claims)
    contractMatches c b = c == (_contract b)
    isPass b = (_mode b) == Pass


-- *** Data *** --


data When = Pre | Post
  deriving (Eq, Show)

newtype Contract = Contract { unContract :: Id }
  deriving (Show)

newtype Method = Method { unMethod :: Id }
  deriving (Show)

newtype Store = Store { unStore :: [(Id, SMType)] }
  deriving (Show)

newtype Args = Args { unArgs :: [(Id, SMType)] }
  deriving (Show)

data Ctx = Ctx Contract Method Args Store When
  deriving (Show)

type SBytes = SArray Integer (WordN 8)
data SMType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes SBytes
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

  let
    c = Contract contract
    m = Method method
    locs = references inv behv

  calldata <- Args <$> mapM (mkSymArg c m) decls
  preStore <- Store <$> mapM (mkSymStorage m Pre) locs
  postStore <- Store <$> mapM (mkSymStorage m Post) locs

  let
    preCtx = Ctx c m calldata preStore Pre
    postCtx = Ctx c m calldata postStore Post

  return $ (preCtx, postCtx)

references :: Invariant -> Behaviour -> [StorageLocation]
references (Invariant _ inv) (Behaviour _ _ _ _ _ _ _ updates _)
  = nub $ (getLoc <$> updates) <> locsFromExp inv

mkSymArg :: Contract -> Method -> Decl -> Symbolic (Id, SMType)
mkSymArg contract method decl@(Decl typ _) = case metaType typ of
  Integer -> do
    v <- sInteger name
    return $ (name, SymInteger v)
  Boolean -> do
    v <- sBool name
    return $ (name, SymBool v)
  ByteStr -> do
    v <- newArray name Nothing
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
    v <- newArray (name item) Nothing
    return $ (name item, SymBytes v)
  where
    name :: TStorageItem a -> Id
    name i = nameFromItem method whn i

mkStorageConstraints :: Ctx -> Ctx -> [Either StorageLocation StorageUpdate] -> [StorageLocation] -> [SBV Bool]
mkStorageConstraints preCtx@(Ctx _ m _ (Store preStore) pre) (Ctx _ _ _ (Store postStore) post) updates locs
  = fmap mkConstraint $ (unchanged <> updates)
  where
    unchanged = Left <$> locs \\ (fmap getLoc updates)

    mkConstraint :: (Either StorageLocation StorageUpdate) -> SBV Bool
    mkConstraint (Left loc) = fromLocation loc
    mkConstraint (Right update) = fromUpdate update

    fromLocation :: StorageLocation -> SBV Bool
    fromLocation loc = case loc of
      IntLoc item -> (lhs item catInts) .== (rhs item catInts)
      BoolLoc item -> (lhs item catBools) .== (rhs item catBools)
      BytesLoc item -> (lhs item catBytes) .== (rhs item catBytes)
      where
        lhs :: (Show b) => TStorageItem a -> ([(Id, SMType)] -> [(Id, b)]) -> b
        lhs i f = get (nameFromItem m post i) (Map.fromList $ f postStore)
        rhs :: (Show b) => TStorageItem a -> ([(Id, SMType)] -> [(Id, b)]) -> b
        rhs i f = get (nameFromItem m pre i) (Map.fromList $ f preStore)

    fromUpdate :: StorageUpdate -> SBV Bool
    fromUpdate update = case update of
      IntUpdate item e -> (lhs item catInts) .== (symExpInt preCtx e)
      BoolUpdate item e -> (lhs item catBools) .== (symExpBool preCtx e)
      BytesUpdate item e -> (lhs item catBytes) .== (symExpBytes preCtx e)
      where
        lhs :: (Show b) => TStorageItem a -> ([(Id, SMType)] -> [(Id, b)]) -> b
        lhs i f = get (nameFromItem m post i) (Map.fromList $ f postStore)


-- *** Symbolic Expression Construction *** ---


symExpBool :: Ctx -> Exp Bool -> SBV Bool
symExpBool ctx@(Ctx c m (Args args) (Store store) w) e = case e of
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
  BoolVar a -> get (nameFromArg c m a) (Map.fromList $ catBools args)
  TEntry a  -> get (nameFromItem m w a) (Map.fromList $ catBools store)
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

symExpInt :: Ctx -> Exp Integer -> SBV Integer
symExpInt ctx@(Ctx c m (Args args) (Store store) w) e = case e of
  Add a b   -> (symExpInt ctx a) + (symExpInt ctx b)
  Sub a b   -> (symExpInt ctx a) - (symExpInt ctx b)
  Mul a b   -> (symExpInt ctx a) * (symExpInt ctx b)
  Div a b   -> (symExpInt ctx a) `sDiv` (symExpInt ctx b)
  Mod a b   -> (symExpInt ctx a) `sMod` (symExpInt ctx b)
  Exp a b   -> (symExpInt ctx a) .^ (symExpInt ctx b)
  LitInt a  -> literal a
  IntVar a  -> get (nameFromArg c m a) (Map.fromList $ catInts args)
  TEntry a  -> get (nameFromItem m w a) (Map.fromList $ catInts store)
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  IntEnv _ -> error "TODO: handle blockchain context in SMT expressions"
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

symExpBytes :: Ctx -> Exp ByteString -> SBytes
symExpBytes = error "TODO: handle bytestrings in SMT expressions"


-- *** SMT Variable Names *** --


nameFromItem :: Method -> When -> TStorageItem a -> Id
nameFromItem (Method method) prePost item = case item of
  DirectInt contract name -> contract @@ method @@ name @@ show prePost
  DirectBool contract name -> contract @@ method @@ name @@ show prePost
  DirectBytes contract name -> contract @@ method @@ name @@ show prePost
  MappedInt contract name ixs -> contract @@ method @@ name @@ showIxs ixs @@ show prePost
  MappedBool contract name ixs -> contract @@ method @@ name @@ showIxs ixs @@ show prePost
  MappedBytes contract name ixs -> contract @@ method @@ name @@ showIxs ixs @@ show prePost
  where
    x @@ y = x <> "_" <> y
    showIxs ixs = intercalate "_" (NonEmpty.toList $ show <$> ixs)

nameFromDecl :: Contract -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: Contract -> Method -> Id -> Id
nameFromArg (Contract c) (Method m) name = c @@ m @@ name
  where
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
get name vars = fromMaybe (error (show name <> " not found in " <> show vars)) $ Map.lookup name vars

catInts :: [(Id, SMType)] -> [(Id, SBV Integer)]
catInts ((name, SymInteger i):tl) = (name, i):(catInts tl)
catInts (_:tl) = catInts tl
catInts [] = []

catBools :: [(Id, SMType)] -> [(Id, SBV Bool)]
catBools ((name, SymBool b):tl) = (name, b):(catBools tl)
catBools (_:tl) = catBools tl
catBools [] = []

catBytes :: [(Id, SMType)] -> [(Id, SBytes)]
catBytes ((name, SymBytes b):tl) = (name, b):(catBytes tl)
catBytes (_:tl) = catBytes tl
catBytes [] = []
