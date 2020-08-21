{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

module Prove where

import Data.List
import Data.List.NonEmpty as NonEmpty (NonEmpty, toList)

import Data.SBV.Trans.Control

import Syntax
import RefinedAst

{-|
   For each Invariant claim builds an SMT query consisting of:

   - constants for the pre and post versions of all storage variables used by the transition system
   - boolean predicates over the pre and post storage variables for each pass behaviour
   - a boolean predicate for the invariant
   - an assertion that the invariant does not hold if either of the following is true:
      1. The constructor predicate holds
      2. The invariant holds over the prestate and one of the method level predicates holds

   If this query returns `unsat` then the invariant must hold over the transition system
-}
queries :: [Claim] -> [QueryT IO CheckSatResult]
queries claims = fmap mkQuery $ gather claims

gather :: [Claim] -> [(Invariant, [Behaviour])]
gather claims = fmap (\i -> (i, getBehaviours i)) invariants
  where
    invariants = catInvs claims
    getBehaviours (Invariant c _) = filter (\b -> c == (_contract b)) (catBehvs claims)

mkQuery :: (Invariant, [Behaviour]) -> QueryT IO CheckSatResult
mkQuery (inv, behvs) = do
  --declareStorageVars behvs
  --defineFunctionPredicates behvs
  --assertInvariant inv behvs
  checkSat

declareStorageVars :: [Behaviour] -> Query ()
declareStorageVars = undefined

defineFunctionPredicates :: [Behaviour] -> Query ()
defineFunctionPredicates = undefined

assertInvariant :: Invariant -> [Behaviour] -> Query ()
assertInvariant = undefined

nameFromLoc :: Id -> Either StorageLocation StorageUpdate -> Id
nameFromLoc contract entry = case entry of
  (Left (IntLoc item)) -> contract <> "_" <> (nameFromItem item)
  (Left (BoolLoc item)) -> contract <> "_" <> (nameFromItem item)
  (Left (BytesLoc item)) -> contract <> "_" <> (nameFromItem item)
  (Right (IntUpdate item _)) -> contract <> "_" <> (nameFromItem item)
  (Right (BoolUpdate item _)) -> contract <> "_" <> (nameFromItem item)
  (Right (BytesUpdate item _)) -> contract <> "_" <> (nameFromItem item)
  where
    nameFromItem :: TStorageItem a -> Id
    nameFromItem (DirectInt name) = name
    nameFromItem (DirectBool name) = name
    nameFromItem (DirectBytes name) = name
    nameFromItem (MappedInt name ixs) = name <> "_" <> showIxs ixs
    nameFromItem (MappedBool name ixs) = name <> "_" <> showIxs ixs
    nameFromItem (MappedBytes name ixs) = name <> "_" <> showIxs ixs

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
