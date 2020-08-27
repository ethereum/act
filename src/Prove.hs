{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Prove (queries) where

import Debug.Trace

import Data.ByteString (ByteString)
import Data.Either
import Data.List
import Data.List.NonEmpty as NonEmpty (NonEmpty, toList)
import Data.Map.Strict as Map (Map, lookup, fromList, toList, unionWith, empty, keys)
import Data.Maybe

import Data.SBV
import Data.SBV.Trans.Control

import RefinedAst
import Syntax (Id, Interface)
import Type (metaType)

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
queries :: [Claim] -> [Symbolic ()]
queries claims = fmap mkQuery $ gather claims


-- *** Data *** --


data SMType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes (SBV [WordN 8])
  deriving (Show)


catInts :: [(Id, SMType)] -> [(Id, SBV Integer)]
catInts ((name, SymInteger i):tail) = (name, i):(catInts tail)
catInts (_:tail) = catInts tail
catInts [] = []

catBools :: [(Id, SMType)] -> [(Id, SBV Bool)]
catBools ((name, SymBool b):tail) = (name, b):(catBools tail)
catBools (_:tail) = catBools tail
catBools [] = []

catBytes :: [(Id, SMType)] -> [(Id, SBV [WordN 8])]
catBytes ((name, SymBytes b):tail) = (name, b):(catBytes tail)
catBytes (_:tail) = catBytes tail
catBytes [] = []

-- *** Pipeline *** --

trace' x = trace (show x) x

-- |Builds a mapping from Invariants to a list of the Pass Behaviours for the
-- contract referenced by that invariant.
gather :: [Claim] -> [(Invariant, Storage, [Behaviour])]
gather claims = fmap (\i -> (i, getStore i, getBehaviours i)) invariants
  where
    invariants = catInvs claims
    getBehaviours (Invariant c _) = filter isPass $ filter (\b -> c == (_contract b)) (catBehvs claims)
    -- TODO: this head is bad, should probably rework the AST to enforce one Storage per contract
    getStore (Invariant c _) = head $ filter (\(Storage n _) -> c == n) (catStores claims)
    isPass b = (_mode b) == Pass

-- |Builds a query asking for an example where the invariant does not hold.
mkQuery :: (Invariant, Storage, [Behaviour]) -> Symbolic ()
mkQuery (inv, store, behvs) = do
  inits' <- mapM (mkInit inv store) inits
  methods' <- mapM (mkMethod inv store) methods
  constrain $ sOr (inits' <> methods')
  where
    inits = filter _creation behvs
    methods = filter (not . _creation) behvs

-- |Given a creation behaviour return a predicate that holds if the invariant does not
-- hold after the constructor has run
mkInit :: Invariant -> Storage -> Behaviour -> Symbolic (SBV Bool)
mkInit (Invariant contract e) (Storage _ locs) (Behaviour method _ _ _ interface pre _ stateUpdates _) = do
  store <- mapM (makeSymbolic contract method) locs
  inv <- symExpBool contract method store e
  state <- mapM (\(c, u) -> fromUpdate c method store u) updates
  return $ (sAnd state) .&& (sNot inv)
  where
    updates :: [(Id, StorageUpdate)]
    updates = mkPairs $ fmap rights stateUpdates

    mkPairs :: Map Id [StorageUpdate] -> [(Id, StorageUpdate)]
    mkPairs updates = concat $ fmap (\(c, us) -> fmap (\u -> (c, u)) us) (Map.toList updates)

    fromUpdate :: Id -> Id -> [(Id, SMType)] -> StorageUpdate -> Symbolic (SBV Bool)
    fromUpdate c m store update = case update of
      IntUpdate item e -> do
        let vars = Map.fromList $ catInts store
            lhs = fromMaybe
                    (error (show item <> " not found in " <> show store))
                    $ Map.lookup (nameFromItem c m item) vars
        rhs <- symExpInt c m store e
        return $ lhs .== rhs

-- |Given a non creation behaviour return a predicate that holds if:
-- - the invariant holds over the prestate
-- - the method has run
-- - the invariant does not hold over the prestate
mkMethod :: Invariant -> Storage -> Behaviour -> Symbolic (SBV Bool)
mkMethod inv storage behv = return $ sFalse

makeSymbolic :: Id -> Id -> StorageLocation -> Symbolic (Id, SMType)
makeSymbolic contract method loc = case loc of
    IntLoc item -> do
      let name = nameFromItem contract method item
      v <- sInteger name
      return $ (name, SymInteger $ v)
    BoolLoc item -> do
      let name = nameFromItem contract method item
      v <- sBool name
      return $ (name, SymBool $ v)
    l -> error ("TODO: handle " ++ show l ++ " in makeSymbolic")

symExp :: Id -> Id -> [(Id, SMType)] -> ReturnExp -> Symbolic (SMType)
symExp contract method storage expression = case expression of
  ExpInt e -> do
    i <- symExpInt contract method storage e
    return $ SymInteger i
  ExpBool e -> do
    b <- symExpBool contract method storage e
    return $ SymBool b
  ExpBytes e -> do
    b <- symExpBytes contract method storage e
    return $ SymBytes b

symExpBool :: Id -> Id -> [(Id, SMType)] -> Exp Bool -> Symbolic (SBV Bool)
symExpBool c m s e = case e of
  And a b   -> (.&&) <$> (symExpBool c m s a) <*> (symExpBool c m s b)
  Or a b    -> (.||) <$> (symExpBool c m s a) <*> (symExpBool c m s b)
  Impl a b  -> (.=>) <$> (symExpBool c m s a) <*> (symExpBool c m s b)
  Eq a b    -> (.==) <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  LE a b    -> (.<)  <$> (symExpInt c m s a) <*> (symExpInt c m s a)
  LEQ a b   -> (.<=) <$> (symExpInt c m s a) <*> (symExpInt c m s a)
  GE a b    -> (.>)  <$> (symExpInt c m s a) <*> (symExpInt c m s a)
  GEQ a b   -> (.>=) <$> (symExpInt c m s a) <*> (symExpInt c m s a)
  NEq a b   -> sNot  <$> (symExpBool c m s (Eq a b))
  Neg a     -> sNot  <$> (symExpBool c m s a)
  LitBool a -> return $ literal a
  BoolVar a -> sBool a
  TEntry a  -> do
    let vars = Map.fromList $ catBools s
    return
      $ fromMaybe (error (show a <> " not found in " <> show vars))
      $ Map.lookup (nameFromItem c m a) vars

symExpInt :: Id -> Id -> [(Id, SMType)] -> Exp Integer -> Symbolic (SBV Integer)
symExpInt c m s e = case e of
  Add a b -> (+)  <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  Sub a b -> (-)  <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  Mul a b -> (*)  <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  Div a b -> sDiv <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  Mod a b -> sMod <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  Exp a b -> (.^) <$> (symExpInt c m s a) <*> (symExpInt c m s b)
  LitInt a -> return $ literal a
  IntVar a -> sInteger a
  IntEnv _ -> error "TODO: handle blockchain context in SMT expressions"
  TEntry a  -> do
    let vars = Map.fromList $ catInts s
    return
      $ fromMaybe (error (show a <> " not found in " <> show vars))
      $ Map.lookup (nameFromItem c m a) vars

symExpBytes :: Id -> Id -> [(Id, SMType)] -> Exp ByteString -> Symbolic ((SBV [(WordN 8)]))
symExpBytes = error "TODO: handle bytestrings in SMT expressions"

nameFromItem :: Id -> Id -> TStorageItem a -> Id
nameFromItem contract method item = case item of
  DirectInt name -> contract <> "_" <> method <> "_" <> name
  DirectBool name -> contract <> "_" <> method <> "_" <> name
  DirectBytes name -> contract <> "_" <> method <> "_" <> name
  MappedInt name ixs -> contract <> "_" <> method <> "_" <> name <> "_" <> showIxs ixs
  MappedBool name ixs -> contract <> "_" <> method <> "_" <> name <> "_" <> showIxs ixs
  MappedBytes name ixs -> contract <> "_" <> method <> "_" <> name <> "_" <> showIxs ixs
  where
    showIxs :: NonEmpty ReturnExp -> String
    showIxs ixs = intercalate "_" (NonEmpty.toList $ go <$> ixs)
      where
        go (ExpInt (LitInt a)) = show a
        go (ExpInt (IntVar a)) = show a
        go (ExpInt (IntEnv a)) = show a
        go (ExpBool (LitBool a)) = show a
        go (ExpBool (BoolVar a)) = show a
        go (ExpBytes (ByVar a)) = show a
        go (ExpBytes (ByStr a)) = show a
        go (ExpBytes (ByLit a)) = show a
        go a = error $ "Internal Error: could not show: " ++ show a

