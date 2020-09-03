{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Prove (queries) where

import Control.Monad (when)
import Data.ByteString (ByteString)
import Data.Either
import Data.List (intercalate)
import Data.List.NonEmpty as NonEmpty (NonEmpty, toList)
import Data.Map.Strict as Map (Map, lookup, fromList, toList)
import Data.Maybe

import Data.SBV hiding (name)

import RefinedAst
import Syntax (Id)

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


data When = Pre | Post
  deriving (Show)

newtype Contract = Contract { unContract :: Id }
  deriving (Show)

newtype Method = Method { unMethod :: Id }
  deriving (Show)

newtype Store = Store { unStore :: [(Id, SMType)] }
  deriving (Show)

data Ctx = Ctx Contract Method When Store
  deriving (Show)

data SMType
  = SymInteger (SBV Integer)
  | SymBool (SBV Bool)
  | SymBytes (SBV [WordN 8])
  deriving (Show)

catInts :: [(Id, SMType)] -> [(Id, SBV Integer)]
catInts ((name, SymInteger i):tl) = (name, i):(catInts tl)
catInts (_:tl) = catInts tl
catInts [] = []

catBools :: [(Id, SMType)] -> [(Id, SBV Bool)]
catBools ((name, SymBool b):tl) = (name, b):(catBools tl)
catBools (_:tl) = catBools tl
catBools [] = []

catBytes :: [(Id, SMType)] -> [(Id, SBV [WordN 8])]
catBytes ((name, SymBytes b):tl) = (name, b):(catBytes tl)
catBytes (_:tl) = catBytes tl
catBytes [] = []


-- *** Pipeline *** --


-- |Builds a mapping from Invariants to a list of the Pass Behaviours for the
-- contract referenced by that invariant.
gather :: [Claim] -> [(Invariant, Storage, [Behaviour])]
gather claims = fmap (\i -> (i, getStore i, getBehaviours i)) invariants
  where
    invariants = catInvs claims
    getBehaviours (Invariant c _) = filter isPass $ filter (\b -> c == (_contract b)) (catBehvs claims)
    -- TODO: refine AST so we don't need this head anymore
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
mkInit (Invariant contract e) (Storage c1 locs) (Behaviour method _ _ c2 interface preCond postCond stateUpdates _) = do
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1 || contract /= c2 || c1 /= c2) $ error "Internal error: contract mismatch"

  store <- mapM (makeSymbolic (mkCtx contract [])) locs

  inv <- symExpBool (mkCtx contract store) e
  state <- mapM (\(c, u) -> fromUpdate (mkCtx c store) u) (updates stateUpdates)

  -- TODO: handle constructor args
  return $ (sAnd state) .&& (sNot inv)
  where
    mkCtx :: Id -> [(Id, SMType)] -> Ctx
    mkCtx c s = Ctx (Contract c) (Method method) Pre (Store s)

    fromUpdate :: Ctx -> StorageUpdate -> Symbolic (SBV Bool)
    fromUpdate ctx@(Ctx _ _ _ (Store store)) update = case update of
      IntUpdate item e' -> do
        let vars = Map.fromList $ catInts store
            lhs = fromMaybe
                    (error (show item <> " not found in " <> show store))
                    $ Map.lookup (nameFromItem ctx item) vars
        rhs <- symExpInt ctx e'
        return $ lhs .== rhs


-- |Given a non creation behaviour return a predicate that holds if:
-- - the invariant holds over the prestate
-- - the method has run
-- - the invariant does not hold over the prestate
mkMethod :: Invariant -> Storage -> Behaviour -> Symbolic (SBV Bool)
mkMethod (Invariant contract e) (Storage c1 locs) (Behaviour method _ _ c2 interface preCond postCond stateUpdates _) = do
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1 || contract /= c2 || c1 /= c2) $ error "Internal error: contract mismatch"

  preStore <- mapM (makeSymbolic (preCtx contract [])) locs
  postStore <- mapM (makeSymbolic (postCtx contract [])) locs

  preInv <- symExpBool (preCtx contract preStore) e
  postInv <- symExpBool (postCtx contract postStore) e

  state <- mapM (\(c, u) -> fromUpdate (preCtx c preStore) (postCtx c postStore) u) (updates stateUpdates)

  return $ preInv .&& (sAnd state) .&& (sNot postInv)
  where

    preCtx c s = Ctx (Contract c) (Method method) Pre (Store s)
    postCtx c s = Ctx (Contract c) (Method method) Post (Store s)

    fromUpdate :: Ctx -> Ctx -> StorageUpdate -> Symbolic (SBV Bool)
    fromUpdate pre@(Ctx _ _ _ (Store prestate)) post update = case update of
      IntUpdate item e' -> do
        let preVars = Map.fromList $ catInts prestate
            lhs = fromMaybe
                    (error (show item <> " not found in " <> show preVars))
                    $ Map.lookup (nameFromItem pre item) preVars
        rhs <- symExpInt post e'
        return $ lhs .== rhs



updates :: Map Id [Either StorageLocation StorageUpdate] -> [(Id, StorageUpdate)]
-- TODO: handle storage reads as well as writes
updates stateUpdates = mkPairs $ fmap rights stateUpdates
  where
    mkPairs :: Map Id [StorageUpdate] -> [(Id, StorageUpdate)]
    mkPairs updates' = concat $ fmap (\(c, us) -> fmap (\u -> (c, u)) us) (Map.toList updates')

makeSymbolic :: Ctx -> StorageLocation -> Symbolic (Id, SMType)
makeSymbolic ctx loc = case loc of
    IntLoc item -> do
      let name = nameFromItem ctx item
      v <- sInteger name
      return $ (name, SymInteger $ v)
    BoolLoc item -> do
      let name = nameFromItem ctx item
      v <- sBool name
      return $ (name, SymBool $ v)
    l -> error ("TODO: handle " ++ show l ++ " in makeSymbolic")

symExpBool :: Ctx -> Exp Bool -> Symbolic (SBV Bool)
symExpBool ctx@(Ctx _ _ _ (Store store)) e = case e of
  And a b   -> (.&&) <$> (symExpBool ctx a) <*> (symExpBool ctx b)
  Or a b    -> (.||) <$> (symExpBool ctx a) <*> (symExpBool ctx b)
  Impl a b  -> (.=>) <$> (symExpBool ctx a) <*> (symExpBool ctx b)
  Eq a b    -> (.==) <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  LE a b    -> (.<)  <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  LEQ a b   -> (.<=) <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  GE a b    -> (.>)  <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  GEQ a b   -> (.>=) <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  NEq a b   -> sNot  <$> (symExpBool ctx (Eq a b))
  Neg a     -> sNot  <$> (symExpBool ctx a)
  LitBool a -> return $ literal a
  BoolVar a -> sBool a -- TODO: handle calldata args properly
  TEntry a  -> do
    let vars = Map.fromList $ catBools store
    return
      $ fromMaybe (error (show a <> " not found in " <> show vars))
      $ Map.lookup (nameFromItem ctx a) vars

symExpInt :: Ctx -> Exp Integer -> Symbolic (SBV Integer)
symExpInt ctx@(Ctx _ _ _ (Store store)) e = case e of
  Add a b   -> (+)  <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  Sub a b   -> (-)  <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  Mul a b   -> (*)  <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  Div a b   -> sDiv <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  Mod a b   -> sMod <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  Exp a b   -> (.^) <$> (symExpInt ctx a) <*> (symExpInt ctx b)
  LitInt a  -> return $ literal a
  IntVar a  -> sInteger a -- TODO: handle calldata args properly
  IntEnv _  -> error "TODO: handle blockchain context in SMT expressions"
  TEntry a  -> do
    let vars = Map.fromList $ catInts store
    return
      $ fromMaybe (error (show a <> " not found in " <> show vars))
      $ Map.lookup (nameFromItem ctx a) vars

symExpBytes :: Ctx -> Exp ByteString -> Symbolic ((SBV [(WordN 8)]))
symExpBytes = error "TODO: handle bytestrings in SMT expressions"

nameFromItem :: Ctx -> TStorageItem a -> Id
nameFromItem (Ctx (Contract contract) (Method method) prePost _) item = case item of
  DirectInt name -> contract @@ method @@ name @@ show prePost
  DirectBool name -> contract @@ method @@ name @@ show prePost
  DirectBytes name -> contract @@ method @@ name @@ show prePost
  MappedInt name ixs -> contract @@ method @@ name @@ showIxs ixs @@ show prePost
  MappedBool name ixs -> contract @@ method @@ name @@ showIxs ixs @@ show prePost
  MappedBytes name ixs -> contract @@ method @@ name @@ showIxs ixs @@ show prePost
  where
    (@@) :: String -> String -> String
    x @@ y = x <> "_" <> y

    -- TODO: handle nested mappings
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

