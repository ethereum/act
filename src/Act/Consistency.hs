{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}

module Act.Consistency (
  checkCases,
  checkArrayBounds,
  checkRewriteAliasing
) where


import Prelude hiding (GT, LT)

import Data.List
import Prettyprinter hiding (group)
import System.Exit (exitFailure)
import Data.Maybe
import Control.Monad (forM, forM_)
import Data.Semigroup (Arg (..))

import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.SMT as SMT
import Act.Print

import qualified EVM.Solvers as Solvers
import Debug.Trace

-- TODO this is duplicated in hevm Keccak.hs but not exported
combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

-- | Checks non-overlapping cases,
-- For every pair of case conditions we assert that they are true
-- simultaneously. The query must be unsat.
mkNonoverlapAssertion :: [Exp ABoolean] -> Exp ABoolean
mkNonoverlapAssertion caseconds =
  mkOr $ (uncurry $ And nowhere) <$> combine caseconds
  where
--    mkOr [] = LitBool nowhere False
--    mkOr (c:cs) = Or nowhere c (mkOr cs)
      mkOr = foldr (Or nowhere) (LitBool nowhere False)

-- | Checks exhaustiveness of cases.
-- We assert that none of the case conditions are true at the same
-- time. The query must be unsat.
mkExhaustiveAssertion :: [Exp ABoolean] -> Exp ABoolean
mkExhaustiveAssertion caseconds =
  foldl mkAnd (LitBool nowhere True) caseconds
  where
    mkAnd r c = And nowhere (Neg nowhere c) r

-- | Create a query for cases
mkCaseQuery :: ([Exp ABoolean] -> Exp ABoolean) -> [Behaviour] -> (Id, SMTExp, (SolverInstance -> IO Model))
mkCaseQuery props behvs@((Behaviour _ _ (Interface ifaceName decls) _ _ _ _ _ _):_) =
  (ifaceName, mkSMT, getModel)
  where
    locs = nub $ concatMap locsFromExp (preconds <> caseconds)
    env = concatMap ethEnvFromBehaviour behvs
    preconds = concatMap _preconditions behvs
    pres = mkAssert ifaceName <$> preconds
    caseconds = concatMap _caseconditions behvs

    mkSMT = SMTExp
      { _storage = concatMap (declareStorage [Pre]) locs
      , _calldata = declareArg ifaceName <$> decls
      , _environment = declareEthEnv <$> env
      , _assertions = (mkAssert ifaceName $ props caseconds) : pres
      }

    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) locs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _menvironment = environment
        , _minitargs = []
        }
mkCaseQuery _ [] = error "Internal error: behaviours cannot be empty"

-- | Checks nonoverlapping and exhaustiveness of cases
checkCases :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkCases (Act _ contracts) solver' smttimeout debug = do
  let groups = concatMap (\(Contract _ behvs) -> groupBy sameIface behvs) contracts
  let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
  solver <- spawnSolver config
  let qs = mkCaseQuery mkNonoverlapAssertion <$> groups
  r <- forM qs (\(name, q, getModel) -> do
                        res <- checkSat solver getModel q
                        pure (name, res))
  mapM_ (checkRes "nonoverlapping") r
  let qs' = mkCaseQuery mkExhaustiveAssertion <$> groups
  r' <- forM qs' (\(name, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, res))
  mapM_ (checkRes "exhaustive") r'

    where

      sameIface (Behaviour _ _ iface _ _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _ _) =
        makeIface iface == makeIface iface'

      checkRes :: String -> (Id, SMT.SMTResult) -> IO ()
      checkRes check (name, res) =
        case res of
          Sat model -> failMsg ("Cases are not " <> check <> " for behavior " <> name <> ".") (prettyAnsi model)
          Unsat -> pure ()
          Unknown -> errorMsg $ "Solver timeour. Cannot prove that cases are " <> check <> " for behavior " <> name <> "."
          SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that cases are " <>  check <> " for behavior " <> name <> "."

      failMsg str model = render (red (pretty str) <> line <> model <> line) >> exitFailure
      errorMsg str = render (pretty str <> line) >> exitFailure


--- ** Array Bounds Checking ** ---

mkBounds :: TypedExp -> Int -> [Exp ABoolean]
mkBounds (TExp SInteger e) b = [LEQ nowhere (LitInt nowhere 0) e] <> [LT nowhere e (LitInt nowhere $ toInteger b)]
mkBounds _ _ = error "Expected Integral Index"

mkRefBounds :: Ref a -> [Exp ABoolean]
mkRefBounds (SArray _ ref _ tes) = concatMap (uncurry mkBounds) tes <> mkRefBounds ref
mkRefBounds (SMapping _ ref _ _) = mkRefBounds ref
mkRefBounds (SField _ ref _ _) = mkRefBounds ref
mkRefBounds _ = []

mkStorageBounds :: StorageLocation -> [Exp ABoolean]
mkStorageBounds (Loc _ (Item _ _ ref)) = mkRefBounds ref

mkCalldataBounds :: CalldataLocation -> [Exp ABoolean]
mkCalldataBounds (Call _ (Item _ _ ref)) = mkRefBounds ref

-- TODO: There are probably locs that don't need to be checked, e.g. assignment locs cannot be out of bounds
mkConstrArrayBoundsQuery :: Constructor -> (Id, SMTExp, SolverInstance -> IO Model)
mkConstrArrayBoundsQuery constructor@(Constructor _ (Interface ifaceName decls) _ preconds _ _ initialStorage)= (ifaceName, mkSMT, getModel)
  where
    -- declare vars
    activeLocs = traceShowId $ locsFromConstructor constructor
    arrayLocs = filter isArray activeLocs
    activeCallds = calldataFromConstructor constructor
    arrayCallds = filter isCalldataArray activeCallds
    boundsExps = concatMap mkStorageBounds arrayLocs
              <> concatMap mkCalldataBounds arrayCallds
    localLocs = filter ((==) ifaceName . ctorFromLocation) activeLocs

    storage = concatMap declareInitialStorage activeLocs
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCallds
    args = nub ifaceArgs <> activeArgs
    env = ethEnvFromConstructor constructor

    -- constraints
    pres = mkAssert ifaceName <$> preconds
    initialStorage' = encodeUpdate ifaceName <$> initialStorage

    assertion = foldr mkOr (LitBool nowhere False) boundsExps
      where
        mkOr c r = Or nowhere (Neg nowhere c) r

    mkSMT = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = declareEthEnv <$> env
      , _assertions = [mkAssert ifaceName assertion] <> pres <> initialStorage'
      }

    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) (activeLocs \\ localLocs)
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _menvironment = environment
        , _minitargs = []
        }

mkBehvArrayBoundsQuery :: Behaviour -> (Id, SMTExp, SolverInstance -> IO Model)
mkBehvArrayBoundsQuery behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds _ stateUpdates _) = (ifaceName, mkSMT, getModel)
  where
    -- declare vars
    activeLocs = locsFromBehaviour behv
    arrayLocs = filter isArray activeLocs
    activeCallds = calldataFromBehaviour behv
    arrayCallds = filter isCalldataArray activeCallds
    boundsExps = concatMap mkStorageBounds arrayLocs
              <> concatMap mkCalldataBounds arrayCallds

    storage = concatMap declareStorageLocation activeLocs
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCallds
    args = nub ifaceArgs <> activeArgs
    env = ethEnvFromBehaviour behv
    constLocs = (nub activeLocs) \\ (locFromUpdate <$> stateUpdates)

    -- constraints
    pres = mkAssert ifaceName <$> preconds <> caseconds
    updates = encodeUpdate ifaceName <$> stateUpdates
    constants = encodeConstant <$> constLocs

    assertion = foldr mkOr (LitBool nowhere False) boundsExps
      where
        mkOr c r = Or nowhere (Neg nowhere c) r

    mkSMT = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = declareEthEnv <$> env
      , _assertions = [mkAssert ifaceName assertion]  <> pres <> updates <> constants
      }

    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) activeLocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _menvironment = environment
        , _minitargs = []
        }

checkArrayBounds :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkArrayBounds (Act _ contracts)  solver' smttimeout debug =
  forM_ contracts (\(Contract constr behvs) -> do
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    solver <- spawnSolver config
    let constrQs = mkConstrArrayBoundsQuery constr
    let behvQs = mkBehvArrayBoundsQuery <$> behvs

    r <- (\(name, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, res)) constrQs
    checkRes "Constructor" r
    r' <- forM behvQs (\(name, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, SMT.SMTResult) -> IO ()
    checkRes transition (name, res) =
      case res of
        Sat model -> failMsg ("Array indices are not within bounds for " <> transition <> " " <> name <> ".") (prettyAnsi model)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."

    failMsg str model = render (red (pretty str) <> line <> model <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure



--- ** No rewrite aliasing ** ---

mkEqualityAssertion :: StorageLocation -> StorageLocation -> Exp ABoolean
mkEqualityAssertion l1 l2 = allEqual
  where
    ix1 = ixsFromLocation l1
    ix2 = ixsFromLocation l2

    eqs = zipWith merger ix1 ix2
    merger :: TypedExp -> TypedExp -> Exp ABoolean
    merger (TExp SInteger e1) (TExp SInteger e2) = Eq nowhere SInteger e1 e2
    merger _ _ = error "Internal error: Expected Integer index expressions"

    allEqual = foldr mkAnd (LitBool nowhere True) eqs
    mkAnd r c = And nowhere c r

mkAliasingAssertion :: [StorageLocation] -> Exp ABoolean
mkAliasingAssertion ls = mkOr $ map (uncurry mkEqualityAssertion) $ combine ls
  where
    mkOr = foldr (Or nowhere) (LitBool nowhere False)


mkAliasingQuery :: Behaviour -> (Id, SMTExp, SolverInstance -> IO Model)
mkAliasingQuery behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds _ stateUpdates _) = (ifaceName, mkSMT, getModel)
  where
    locs = locFromUpdate <$> stateUpdates
    locsArgs = (\l -> Arg (idsFromLocation l) l) <$> locs
    groupedLocs = fmap (\(Arg _ b) -> b) <$> group (sort locsArgs)

    activeLocs = concatMap (\(Loc _ item) -> locsFromItem SStorage item) locs
    activeCallds = concatMap (\(Loc _ item) -> calldataFromItem SStorage item) locs

    storage = concatMap declareStorageLocation activeLocs
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCallds
    args = nub ifaceArgs <> activeArgs
    env = ethEnvFromBehaviour behv
    constLocs = (nub activeLocs) \\ (locFromUpdate <$> stateUpdates)

    -- constraints
    pres = mkAssert ifaceName <$> preconds <> caseconds
    constants = encodeConstant <$> constLocs

    assertions = mkAliasingAssertion <$> groupedLocs
    assertion = traceShowId $ mkOr assertions
      where
        mkOr = foldr (Or nowhere) (LitBool nowhere False)

    mkSMT = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = declareEthEnv <$> env
      , _assertions = [mkAssert ifaceName assertion]  <> pres <> constants
      }
    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) activeLocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _menvironment = environment
        , _minitargs = []
        }

checkRewriteAliasing :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkRewriteAliasing (Act _ contracts)  solver' smttimeout debug =
  forM_ contracts (\(Contract _ behvs) -> do
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    solver <- spawnSolver config
    let behvQs = mkAliasingQuery <$> behvs
    r' <- forM behvQs (\(name, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, SMT.SMTResult) -> IO ()
    checkRes transition (name, res) =
      case res of
        Sat model -> failMsg ("Rewrites are aliased for " <> transition <> " " <> name <> ".") (prettyAnsi model)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that rewrites are not aliased for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nSolver timeour. Cannot prove that rewrites are not aliased for"  <> transition <> " " <> name <> "."

    failMsg str model = render (red (pretty str) <> line <> model <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure