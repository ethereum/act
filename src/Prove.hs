{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Prove (queries) where

import Control.Monad (when)
import Data.ByteString (ByteString)
import Data.Either
import Data.List (intercalate, (\\), nub)
import Data.List.NonEmpty as NonEmpty (NonEmpty, toList)
import Data.Map.Strict as Map (Map, lookup, fromList, toList)
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
queries claims = fmap mkQueries $ gather claims

-- *** Data *** --


data When = Pre | Post
  deriving (Eq, Show)

newtype Contract = Contract { unContract :: Id }
  deriving (Show)

newtype Slot = Slot { unSlot :: Id }
  deriving (Show)

newtype Method = Method { unMethod :: Id }
  deriving (Show)

newtype Store = Store { unStore :: [(Id, SMType)] }
  deriving (Show)

newtype Args = Args { unArgs :: [(Id, SMType)] }
  deriving (Show)

data Ctx = Ctx Contract Method Args Store When
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
gather :: [Claim] -> [(Invariant, Storages, [Behaviour])]
gather claims = fmap (\i -> (i, store, getBehaviours i)) invariants
  where
    invariants = catInvs claims
    getBehaviours (Invariant c _) = filter isPass $ filter (\b -> c == (_contract b)) (catBehvs claims)
    -- TODO: refine AST so we don't need this head anymore
    store = head $ (catStores claims)
    isPass b = (_mode b) == Pass

-- |Builds a query asking for an example where the invariant does not hold.
mkQueries :: (Invariant, Storages, [Behaviour]) -> (Invariant, [Symbolic ()])
mkQueries (inv, store, behvs) = (inv, inits' <> methods')
  where
    inits' = fmap (mkInit inv store) inits
    methods' = fmap (mkMethod inv store) methods
    inits = filter _creation behvs
    methods = filter (not . _creation) behvs

-- |Given a creation behaviour return a predicate that holds if the invariant does not
-- hold after the constructor has run
mkInit :: Invariant -> Storages -> Behaviour -> Symbolic ()
mkInit inv@(Invariant contract e) (Storages store) behv@(Behaviour method _ _ c1 (Interface _ decls)  preCond postCond stateUpdates _) = do
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1) $ error "Internal error: contract mismatch"

  calldata <- Args <$> mapM (mkSymArg c m) decls
  preStore <- Store <$> mapM (mkSymStorage c m Pre) locs
  postStore <- Store <$> mapM (mkSymStorage c m Post) locs

  let
    preCtx ctrct = Ctx ctrct m calldata preStore Pre
    postCtx ctrct = Ctx ctrct m calldata postStore Post

    postInv' = symExpBool (postCtx c) e

    storageBounds = symExpBool (postCtx c) $ mconcat <$> mkStorageBounds store contract $ Left <$> locs

    preCond' = symExpBool (preCtx c) preCond
    postCond' = symExpBool (postCtx c) postCond

    unchanged' = fmap
                   (fromLocation (preCtx c) (postCtx c))
                   (unchanged locs (fmap snd $ updated stateUpdates))

    stateUpdates' = fmap
                      (\(ctrct, u) -> fromUpdate (preCtx (Contract ctrct)) (postCtx (Contract ctrct)) u)
                      (updated stateUpdates)

  constrain $ preCond'
            .&& (sAnd stateUpdates') .&& (sAnd unchanged')
            .&& postCond' .&& storageBounds
            .&& (sNot postInv')
  where
    c = Contract contract
    m = Method method
    locs = references inv behv

-- |Given a non creation behaviour return a predicate that holds if:
-- - the invariant holds over the prestate
-- - the method has run
-- - the invariant does not hold over the prestate
mkMethod :: Invariant -> Storages -> Behaviour -> Symbolic ()
mkMethod inv@(Invariant contract e) (Storages store) behv@(Behaviour method _ _ c1 (Interface _ decls) preCond postCond stateUpdates _) = do
  -- TODO: refine AST so we don't need this anymore
  when (contract /= c1) $ error "Internal error: contract mismatch"

  calldata <- Args <$> mapM (mkSymArg c m) decls
  preStore <- Store <$> mapM (mkSymStorage c m Pre) locs
  postStore <- Store <$> mapM (mkSymStorage c m Post) locs

  let
    preCtx ctrct = Ctx ctrct m calldata preStore Pre
    postCtx ctrct = Ctx ctrct m calldata postStore Post

    storageBounds = symExpBool (preCtx c) $ mconcat <$> mkStorageBounds store contract $ Left <$> locs

    preInv = symExpBool (preCtx c) e
    postInv = symExpBool (postCtx c) e

    preCond' = symExpBool (preCtx c) preCond
    postCond' = symExpBool (postCtx c) postCond

    unchanged' = fmap
                   (fromLocation (preCtx c) (postCtx c))
                   (unchanged locs (rights $ fromMaybe [] $ Map.lookup contract stateUpdates))

    stateUpdates' = fmap
                      (\(ctrct, u) -> fromUpdate (preCtx (Contract ctrct)) (postCtx (Contract ctrct)) u)
                      (updated stateUpdates)

  constrain $ preInv .&& preCond' .&& storageBounds
           .&& (sAnd stateUpdates') .&& (sAnd unchanged')
           .&& postCond' .&& (sNot postInv)
  where
    c = Contract contract
    m = Method method
    locs = references inv behv

references :: Invariant -> Behaviour -> [StorageLocation]
references (Invariant _ inv) (Behaviour _ _ _ _ _ _ _ updates _)
  = nub $ (snd <$> locsFromUpdates updates) <> locsFromExp inv

mkSymArg :: Contract -> Method -> Decl -> Symbolic (Id, SMType)
mkSymArg contract method decl@(Decl typ _) = case metaType typ of
    Integer -> do
      let name = nameFromDecl contract method decl
      v <- sInteger name
      return $ (name, SymInteger v)
    Boolean -> do
      let name = nameFromDecl contract method decl
      v <- sBool name
      return $ (name, SymBool v)
    ByteStr -> error ("TODO: handle bytestrings in smt expressions")

mkSymStorage :: Contract -> Method -> When -> StorageLocation -> Symbolic (Id, SMType)
mkSymStorage c m w loc = case loc of
    IntLoc item -> do
      let name = nameFromItem c m w item
      v <- sInteger name
      return $ (name, SymInteger v)
    BoolLoc item -> do
      let name = nameFromItem c m w item
      v <- sBool name
      return $ (name, SymBool v)
    BytesLoc _ -> error ("TODO: handle bytestrings in smt expressions")

updated :: Map Id [Either StorageLocation StorageUpdate] -> [(Id, StorageUpdate)]
updated stateUpdates = mkPairs $ fmap rights stateUpdates
  where
    mkPairs :: Map Id [StorageUpdate] -> [(Id, StorageUpdate)]
    mkPairs updates' = concat $ fmap (\(c, us) -> fmap (\u -> (c, u)) us) (Map.toList updates')

unchanged :: [StorageLocation] -> [StorageUpdate] -> [StorageLocation]
unchanged locations updates = locations \\ (fmap loc updates)
  where
    loc :: StorageUpdate -> StorageLocation
    loc update = case update of
      IntUpdate l _ -> IntLoc l
      BoolUpdate l _ -> BoolLoc l
      BytesUpdate l _ -> BytesLoc l

fromLocation :: Ctx -> Ctx -> StorageLocation -> SBV Bool
fromLocation (Ctx _ _ _ (Store preStore) pre) (Ctx c m _ (Store postStore) post) loc = case loc of
  IntLoc item -> lhs .== rhs
    where
      postVars = Map.fromList $ catInts postStore
      preVars = Map.fromList $ catInts preStore
      lhs = fromMaybe
              (error (show item <> " not found in " <> show postVars))
              $ Map.lookup (nameFromItem c m post item) postVars
      rhs = fromMaybe
              (error (show item <> " not found in " <> show preVars))
              $ Map.lookup (nameFromItem c m pre item) preVars
  BoolLoc _ -> error "TODO: handle bool storage locations"
  BytesLoc _ -> error "TODO: handle bytestring storage locations"

fromUpdate :: Ctx -> Ctx -> StorageUpdate -> SBV Bool
fromUpdate preCtx (Ctx c m _ (Store postStore) post) update = case update of
  IntUpdate item e -> lhs .== rhs
    where
      postVars = Map.fromList $ catInts postStore
      lhs = fromMaybe
             (error (show item <> " not found in " <> show postVars))
             $ Map.lookup (nameFromItem c m post item) postVars
      rhs = symExpInt preCtx e
  BoolUpdate _ _ -> error "TODO: handle bool storage updates"
  BytesUpdate _ _ -> error "TODO: handle bytestring storage updates"

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
  TEntry a  -> get (nameFromItem c m w a) (Map.fromList $ catBools store)
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
  TEntry a  -> get (nameFromItem c m w a) (Map.fromList $ catInts store)
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  IntEnv _ -> error "TODO: handle blockchain context in SMT expressions"
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"

get :: (Show a) => Id -> Map Id a -> a
get name vars = fromMaybe (error (show name <> " not found in " <> show vars)) $ Map.lookup name vars

symExpBytes :: Ctx -> Exp ByteString -> (SBV [(WordN 8)])
symExpBytes = error "TODO: handle bytestrings in SMT expressions"

nameFromItem :: Contract -> Method -> When -> TStorageItem a -> Id
nameFromItem (Contract contract) (Method method) prePost item = case item of
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

nameFromDecl :: Contract -> Method -> Decl -> Id
nameFromDecl c m (Decl _ name) = nameFromArg c m name

nameFromArg :: Contract -> Method -> Id -> Id
nameFromArg (Contract c) (Method m) name = c @@ m @@ name
  where
    x @@ y = x <> "_" <> y

locsFromUpdates :: Map Id [Either StorageLocation StorageUpdate] -> [(Id, StorageLocation)]
locsFromUpdates updates = concat $ fmap merge $ Map.toList $ (fmap getLoc) <$> updates
  where
    merge :: (Id, [StorageLocation]) -> [(Id, StorageLocation)]
    merge (c, locs) = fmap (\l -> (c, l)) locs

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
  ITE _ _ _ -> error "TODO: hande ITE in smt expresssions"
  TEntry a  -> case a of
    DirectInt slot -> [IntLoc $ DirectInt slot]
    DirectBool slot -> [BoolLoc $ DirectBool slot]
    DirectBytes slot -> [BytesLoc $ DirectBytes slot]
    MappedInt m ixs -> [IntLoc $ MappedInt m ixs]
    MappedBool m ixs -> [BoolLoc $ MappedBool m ixs]
    MappedBytes m ixs -> [BytesLoc $ MappedBytes m ixs]
