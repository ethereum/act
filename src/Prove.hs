{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Prove (queries) where

import Debug.Trace

import Data.ByteString (ByteString)
import Data.Either
import Data.List
import Data.List.NonEmpty as NonEmpty (NonEmpty, toList)
import Data.Map.Strict as Map (Map, lookup, fromList, toList, unionWith, empty)
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


-- *** Internals *** --


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
mkInit inv storage behv = trace (show storage <> "\n\n\n" <> show inv <> "\n\n\n" <> show behv) undefined
  where
    makeSymbolic :: TStorageItem a -> Symbolic (SBV a)
    makeSymbolic (DirectInt name) = sInteger name
    makeSymbolic (DirectBool name) = sBool name
    makeSymbolic v = error ("TODO: handle " ++ show v ++ " in makeSymbolic")
--
-- |Given a non creation behaviour return a predicate that holds if:
-- - the invariant holds over the prestate
-- - the method has run
-- - the invariant does not hold over the prestate
mkMethod :: Invariant -> Storage -> Behaviour -> Symbolic (SBV Bool)
mkMethod inv behv = undefined

symExpBool :: Id -> Storage -> Exp Bool -> Symbolic (SBV Bool)
symExpBool c s (And a b) = (.&&) <$> (symExpBool c s a) <*> (symExpBool c s b)
symExpBool c s (Or a b) = (.||) <$> (symExpBool c s a) <*> (symExpBool c s b)
symExpBool c s (Impl a b) = (.=>) <$> (symExpBool c s a) <*> (symExpBool c s b)
symExpBool c s (Eq a b) = (.==) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpBool c s (NEq a b) = sNot <$> (symExpBool c s (Eq a b))
symExpBool c s (Neg a) = sNot <$> (symExpBool c s a)
symExpBool c s (Neg a) = sNot <$> (symExpBool c s a)
symExpBool c s (LE a b) = (.<) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (LEQ a b) = (.<=) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (GE a b) = (.>) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (GEQ a b) = (.>=) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (LitBool a) = return $ literal a
symExpBool c s (BoolVar a) = sBool a
symExpBool c s (TEntry a) = undefined

symExpInt :: Id -> Storage -> Exp Integer -> Symbolic (SBV Integer)
symExpInt c s (Add a b) = (+) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Sub a b) = (-) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Mul a b) = (*) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Div a b) = sDiv <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Mod a b) = sMod <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Exp a b) = (.^) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt _ _ (LitInt a) = return $ literal a
symExpInt _ _ (IntVar a) = sInteger a
symExpInt c s (TEntry a) = undefined
symExpInt _ _ (IntEnv _) = error "TODO: handle blockchain context in SMT expressions"

symExpBytes :: Id -> Storage -> Exp ByteString -> Symbolic ((SBV [(WordN 256)]))
symExpBytes = error "TODO: handle bytestrings in SMT expressions"

{-
symExp :: Id -> (Either Pre Post) -> ReturnExp -> Symbolic SMType
symExp c store (ExpInt e) = return $ SInteger $ symExpInt c store e
symExp c store (ExpBool e) = return $ SBoolean $ symExpBool c store e
symExp c store (ExpBytes e) = return $ SByteStr $ symExpBytes c store e

symExpInt :: Id -> (Either Pre Post) -> Exp Int -> Symbolic (SBV Integer)
symExpInt c s (Add a b) = (+) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Sub a b) = (-) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Mul a b) = (*) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Div a b) = sDiv <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Mod a b) = sMod <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt c s (Exp a b) = (.^) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpInt _ _ (LitInt a) = return $ literal a
symExpInt _ _ (IntVar a) = sInteger a
symExpInt c s (TEntry a) = case getItem s $ nameFromItem c a of
                             SInteger i -> i
                             _ -> (error "Internal error: found non integer storage variable when building integer expression")
symExpInt _ _ (IntEnv _) = error "TODO: handle blockchain context in SMT expressions"

symExpBool :: Id -> (Either Pre Post) -> Exp Bool -> Symbolic (SBV Bool)
symExpBool c s (And a b) = (.&&) <$> (symExpBool c s a) <*> (symExpBool c s b)
symExpBool c s (Or a b) = (.||) <$> (symExpBool c s a) <*> (symExpBool c s b)
symExpBool c s (Impl a b) = (.=>) <$> (symExpBool c s a) <*> (symExpBool c s b)
symExpBool c s (Eq a b) = (.==) <$> (symExpInt c s a) <*> (symExpInt c s b)
symExpBool c s (NEq a b) = sNot <$> (symExpBool c s (Eq a b))
symExpBool c s (Neg a) = sNot <$> (symExpBool c s a)
symExpBool c s (Neg a) = sNot <$> (symExpBool c s a)
symExpBool c s (LE a b) = (.<) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (LEQ a b) = (.<=) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (GE a b) = (.>) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (GEQ a b) = (.>=) <$> (symExpInt c s a) <*> (symExpInt c s a)
symExpBool c s (LitBool a) = return $ literal a
symExpBool c s (BoolVar a) = sBool a
symExpBool c s (TEntry a) = case getItem s $ nameFromItem c a of
                             SBoolean b -> b
                             _ -> (error "Internal error: found non boolean storage variable when building boolean expression")

symExpBytes :: Id -> (Either Pre Post) -> Exp ByteString -> Symbolic ((SBV [(WordN 256)]))
symExpBytes = error "TODO: handle bytestrings in SMT expressions"

getItem :: (Either Pre Post) -> Id -> SMType
getItem (Left pre) name = fromMaybe
  (error $ name ++ " not found in prestate")
  $ Map.lookup name (unPre pre)
getItem (Right post) name = fromMaybe
  (error $ name ++ " not found in poststate:")
  $ Map.lookup name (unPost post)

sVarFromUpdate :: Id -> StorageUpdate -> (Id, SMType)
sVarFromUpdate contract upd@(IntUpdate _ _) = let name = nameFromUpdate contract upd in (name, SInteger $ sInteger $ name)
sVarFromUpdate contract upd@(BoolUpdate _ _) = let name = nameFromUpdate contract upd in (name, SBoolean $ sBool $ name)
sVarFromUpdate contract upd@(BytesUpdate _ _) = error "TODO: handle bytestrings"

nameFromUpdate :: Id -> StorageUpdate -> Id
nameFromUpdate contract update = case update of
  (IntUpdate item _) -> nameFromItem contract item
  (BoolUpdate item _) -> nameFromItem contract item
  (BytesUpdate item _) -> nameFromItem contract item

nameFromItem :: Id -> TStorageItem a -> Id
nameFromItem contract (DirectInt name) = contract <> "_" <> name
nameFromItem contract (DirectBool name) = contract <> "_" <> name
nameFromItem contract (DirectBytes name) = contract <> "_" <> name
nameFromItem contract (MappedInt name ixs) = contract <> "_" <> name <> "_" <> showIxs ixs
nameFromItem contract (MappedBool name ixs) = contract <> "_" <> name <> "_" <> showIxs ixs
nameFromItem contract (MappedBytes name ixs) = contract <> "_" <> name <> "_" <> showIxs ixs

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
-}
