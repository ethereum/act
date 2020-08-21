{-# LANGUAGE GADTs #-}

module Prove where

import Data.Either
import Data.List
import Data.Map.Strict as Map (Map)
import Data.List.NonEmpty as NonEmpty (NonEmpty, toList)

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
queries :: [Claim] -> [QueryT IO CheckSatResult]
queries claims = fmap mkQuery $ gather claims


-- *** Data *** --


newtype Pre = Pre { unPre :: Map Id (SBV MType) }
newtype Post = Post { unPost :: Map Id (SBV MType) }
newtype Args = Args { unArgs :: Map Id (SBV MType) }


-- *** Pipeline *** --


gather :: [Claim] -> [(Invariant, [Behaviour])]
gather claims = fmap (\i -> (i, getBehaviours i)) invariants
  where
    invariants = catInvs claims
    getBehaviours (Invariant c _) = filter (\b -> c == (_contract b)) (catBehvs claims)

mkQuery :: (Invariant, [Behaviour]) -> QueryT IO CheckSatResult
mkQuery (i, behvs) = do
  constrain $
        (init pre .&& (sNot $ inv (Left pre)))
    .|| (inv (Left pre) .&& (sOr (methods pre post)) .&& (sNot $ inv (Right post)))
  checkSat
    where
      (init, methods) = defineFunctionPredicates behvs
      (pre, post) = declareStorageVars behvs
      inv = defineInvariant i

declareStorageVars :: [Behaviour] -> ((Pre, Post))
declareStorageVars behvs = undefined
  where
    updates = fmap ((fmap rights) . _stateUpdates) behvs

defineFunctionPredicates :: [Behaviour] -> (Pre -> SBV Bool, Pre -> Post -> [SBV Bool])
defineFunctionPredicates behvs = (init, methods)
  where
    init = mkInit $ head $ filter isInit behvs -- TODO: fail with multiple constructors
    methods = mkMethods $ filter isMethod behvs
    isInit b = isPass b && _creation b == True
    isMethod b = isPass b && _creation b == False
    isPass b = _mode b == Pass

defineInvariant :: Invariant -> ((Either Pre Post) -> SBV Bool)
defineInvariant = undefined

mkInit :: Behaviour -> Pre -> SBV Bool
mkInit behv store = undefined

mkMethods :: [Behaviour] -> Pre -> Post -> [SBV Bool]
mkMethods pre post = undefined

mkCalldata :: Interface -> Args
mkCalldata iface = undefined

symExp :: (Either Pre Post) -> Args -> Exp Bool -> SBV Bool
symExp store args e = undefined

sVarFromUpdate :: StorageUpdate -> SBV MType
sVarFromUpdate update = undefined

nameFromUpdate :: Id -> StorageUpdate -> Id
nameFromUpdate contract update = case update of
  (IntUpdate item _) -> contract <> "_" <> (nameFromItem item)
  (BoolUpdate item _) -> contract <> "_" <> (nameFromItem item)
  (BytesUpdate item _) -> contract <> "_" <> (nameFromItem item)
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
