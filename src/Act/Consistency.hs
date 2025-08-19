{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}

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
import Data.Type.Equality ((:~:)(..), TestEquality (testEquality))
import Data.Singletons (sing, SingI)
import Data.Semigroup (Arg (..))

import Control.Monad.Reader
import Control.Monad (forM, forM_, zipWithM)

import Act.Lex (AlexPosn(..))
import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.SMT as SMT
import Act.Print

import qualified EVM.Solvers as Solvers

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
    slocs = nub $ concatMap slocsFromExp (preconds <> caseconds)
    clocs = nub $ concatMap clocsFromExp (preconds <> caseconds)
    env = concatMap ethEnvFromBehaviour behvs
    preconds = concatMap _preconditions behvs
    pres = mkAssert ifaceName <$> preconds
    caseconds = concatMap _caseconditions behvs

    mkSMT = SMTExp
      { _storage = concatMap (declareStorage [Pre]) slocs
      , _calldata = (declareArg ifaceName <$> decls) <> (declareCalldataLocation ifaceName <$> clocs)
      , _environment = declareEthEnv <$> env
      , _assertions = (mkAssert ifaceName $ props caseconds) : pres
      }

    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) slocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      calllocs <- mapM (getCalldataLocValue solver ifaceName) clocs
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _mcalllocs = calllocs
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

type ModelCtx = Reader Model

mkBounds :: TypedExp -> Int -> [Exp ABoolean]
mkBounds (TExp SInteger e) b = [LEQ nowhere (LitInt nowhere 0) e, LT nowhere e (LitInt nowhere $ toInteger b)]
mkBounds _ _ = error "Internal Error: Expected Integral Index"

mkRefBounds :: Ref a -> [Exp ABoolean]
mkRefBounds (SArray _ ref _ tes) = concatMap (uncurry mkBounds) tes <> mkRefBounds ref
mkRefBounds (SMapping _ ref _ _) = mkRefBounds ref
mkRefBounds (SField _ ref _ _) = mkRefBounds ref
mkRefBounds _ = []

mkStorageBounds :: StorageLocation -> [Exp ABoolean]
mkStorageBounds (SLoc _ (Item _ _ ref)) = mkRefBounds ref

mkCalldataBounds :: CalldataLocation -> [Exp ABoolean]
mkCalldataBounds (CLoc _ (Item _ _ ref)) = mkRefBounds ref

-- TODO: There are locs that don't need to be checked, e.g. assignment locs cannot be out of bounds
mkConstrArrayBoundsQuery :: Constructor -> (Id, [StorageLocation], [CalldataLocation], SMTExp, SolverInstance -> IO Model)
mkConstrArrayBoundsQuery constructor@(Constructor _ (Interface ifaceName decls) _ preconds _ _ initialStorage) =
  (ifaceName, arraySLocs, arrayCLocs, mkSMT, getModel)
  where
    -- declare vars
    activeSLocs = slocsFromConstructor constructor
    arraySLocs = filter isArray activeSLocs
    activeCLocs = clocsFromConstructor constructor
    arrayCLocs = filter isCalldataArray activeCLocs
    boundsExps = concatMap mkStorageBounds arraySLocs
              <> concatMap mkCalldataBounds arrayCLocs

    localLocs = filter ((==) ifaceName . ctorFromLocation) activeSLocs

    storage = concatMap declareInitialStorage activeSLocs
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCLocs
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
      prestate <- mapM (getStorageValue solver ifaceName Pre) (activeSLocs \\ localLocs)
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      calllocs <- mapM (getCalldataLocValue solver ifaceName) activeCLocs
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }

mkBehvArrayBoundsQuery :: Behaviour -> (Id, [StorageLocation], [CalldataLocation], SMTExp, SolverInstance -> IO Model)
mkBehvArrayBoundsQuery behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds _ stateUpdates _) =
  (ifaceName, arraySLocs, arrayCLocs, mkSMT, getModel)
  where
    -- Declare vars
    activeSLocs = slocsFromBehaviour behv
    arraySLocs = filter isArray activeSLocs
    activeCLocs = clocsFromBehaviour behv
    arrayCLocs = filter isCalldataArray activeCLocs
    boundsExps = concatMap mkStorageBounds arraySLocs
              <> concatMap mkCalldataBounds arrayCLocs

    storage = concatMap declareStorageLocation activeSLocs
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCLocs
    args = nub ifaceArgs <> activeArgs
    env = ethEnvFromBehaviour behv
    constLocs = (nub activeSLocs) \\ (locFromUpdate <$> stateUpdates)

    -- Constraints
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
      prestate <- mapM (getStorageValue solver ifaceName Pre) activeSLocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      calllocs <- mapM (getCalldataLocValue solver ifaceName) activeCLocs
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _mcalllocs = calllocs
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

    r <- (\(name, slocs, clocs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, slocs, clocs, res)) constrQs
    checkRes "Constructor" r
    r' <- forM behvQs (\(name, slocs, clocs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, slocs, clocs, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, [StorageLocation], [CalldataLocation], SMT.SMTResult) -> IO ()
    checkRes transition (name, slocs, clocs, res) =
      case res of
        Sat model -> failMsg ("Array indices are not within bounds for " <> transition <> " " <> name <> ".")
          (prettyAnsi model) (printOutOfBounds model slocs clocs)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."

    printOutOfBounds :: Model -> [StorageLocation] -> [CalldataLocation] -> DocAnsi
    printOutOfBounds model slocs clocs =
      indent 2 ( underline (string "Out of bounds:"))
      <> line <> vsep (printedSLocs <> printedCLocs)
      where
        printedSLocs = runReader (mapM checkStorageBounds slocs) model
        printedCLocs = runReader (mapM checkCalldataBounds clocs) model

    failMsg str model oobs = render (red (pretty str) <> line <> model <> line <> oobs <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure

checkBound :: TypedExp -> Int -> ModelCtx Bool
checkBound (TExp SInteger e) b =
  [ (0 <= toInteger idx) && (toInteger idx < toInteger b) | idx <- modelEval e ]
checkBound _ _ = error "Internal Error: Expected Integer indices"

checkRefBounds :: Ref a -> ModelCtx Bool
checkRefBounds (SArray _ ref _ idcs) = liftA2 (&&) (and <$> mapM (uncurry checkBound) idcs) (checkRefBounds ref)
checkRefBounds (SMapping _ ref _ _) = checkRefBounds ref
checkRefBounds (SField _ ref _ _) = checkRefBounds ref
checkRefBounds _ = pure True

checkStorageBounds :: StorageLocation -> ModelCtx DocAnsi
checkStorageBounds (SLoc _ item@(Item _ _ ref)) = do
  cond <- checkRefBounds ref
  if cond then pure $ string ""
  else do
    i <- printOutOfBoundsItem item
    pure $ indent 4 $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> i
  where
    (AlexPn _ l c) = posnFromRef ref

checkCalldataBounds :: CalldataLocation -> ModelCtx DocAnsi
checkCalldataBounds (CLoc _ item@(Item _ _ ref)) = do
  cond <- checkRefBounds ref
  if cond
    then pure $ string ""
    else do
      i <- printOutOfBoundsItem item
      pure $ indent 4 $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> i
    where
      (AlexPn _ l c ) = posnFromRef ref

printIdx :: TypedExp -> Int -> ModelCtx DocAnsi
printIdx te@(TExp SInteger e) b = do
  idx <- modelEval e
  if (toInteger idx < toInteger b) && (0 <= toInteger idx)
    then pure $ string "[" <> string (prettyTypedExp te) <> string "]"
    else
      case e of
        LitInt _ _ -> pure $
          string "[" <> red (string (show idx))
          <> string " | " <>  green (string (show b)) <> string "]"
        _ -> pure $
          string "[(" <> string (prettyTypedExp te) <> string ") = " <> red (string ( show idx))
          <> string " | " <>  green (string (show b)) <> string "]"
printIdx _ _ = error "Internal Error: Expected Integer indices"

printOutOfBoundsRef :: Ref a -> ModelCtx DocAnsi
printOutOfBoundsRef (SArray _ ref _ idcs) =
  liftA2 (<>) (printOutOfBoundsRef ref) (concatWith (<>) <$> mapM (uncurry printIdx) idcs)
printOutOfBoundsRef (SMapping _ ref _ idcs) =
  liftA2 (<>) (printOutOfBoundsRef ref) (concatWith (<>)
    <$> mapM (\te -> pure $ string "[" <> string (prettyTypedExp te) <> string "]") idcs)
printOutOfBoundsRef (SField _ ref _ id') =
  liftA2 (<>) (printOutOfBoundsRef ref) (pure $ string $ "." ++ id')
printOutOfBoundsRef (SVar _ _ id') = pure $ string id'
printOutOfBoundsRef (CVar _ _ id') = pure $ string id'

printOutOfBoundsItem :: TItem a k-> ModelCtx DocAnsi
printOutOfBoundsItem (Item _ _ ref) = printOutOfBoundsRef ref


--- ** No rewrite aliasing ** ---

mkEqualityAssertion :: StorageLocation -> StorageLocation -> Exp ABoolean
mkEqualityAssertion l1 l2 = allEqual
  where
    ix1 = ixsFromLocation l1
    ix2 = ixsFromLocation l2

    eqs = zipWith eqIdx ix1 ix2
    eqIdx :: TypedExp -> TypedExp -> Exp ABoolean
    eqIdx (TExp SInteger e1) (TExp SInteger e2) = Eq nowhere SInteger e1 e2
    eqIdx _ _ = error "Internal error: Expected Integer index expressions"

    allEqual = foldr mkAnd (LitBool nowhere True) eqs
    mkAnd r c = And nowhere c r

mkAliasingAssertion :: [StorageLocation] -> Exp ABoolean
mkAliasingAssertion ls = mkOr $ map (uncurry mkEqualityAssertion) $ combine ls
  where
    mkOr = foldr (Or nowhere) (LitBool nowhere False)

mkAliasingQuery :: Behaviour -> (Id, [[StorageLocation]], SMTExp, SolverInstance -> IO Model)
mkAliasingQuery behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds _ stateUpdates _) =
  (ifaceName, groupedLocs, mkSMT, getModel)
  where
    updatedLocs = locFromUpdate <$> stateUpdates
    updatedLocsIds = (\l -> Arg (idsFromLocation l) l) <$> updatedLocs
    groupedLocs = fmap (\(Arg _ b) -> b) <$> group (sort updatedLocsIds)

    activeSLocs = nub $ concatMap (\(SLoc _ item) -> slocsFromItem SStorage item) updatedLocs
               <> concatMap slocsFromExp preconds
               <> concatMap slocsFromExp caseconds
    activeCLocs = nub $ concatMap (\(SLoc _ item) -> clocsFromItem SStorage item) updatedLocs
               <> concatMap clocsFromExp preconds
               <> concatMap clocsFromExp caseconds

    storage = concatMap declareStorageLocation activeSLocs
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCLocs
    args = nub ifaceArgs <> activeArgs
    env = ethEnvFromBehaviour behv
    constLocs = (nub activeSLocs) \\ (locFromUpdate <$> stateUpdates)

    -- constraints
    pres = mkAssert ifaceName <$> preconds <> caseconds
    constants = encodeConstant <$> constLocs

    assertLocGroupAliasings = mkAliasingAssertion <$> groupedLocs
    assertion = mkOr assertLocGroupAliasings
      where
        mkOr = foldr (Or nowhere) (LitBool nowhere False)

    mkSMT = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = declareEthEnv <$> env
      , _assertions = [mkAssert ifaceName assertion]  <> pres <> constants
      }
    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) activeSLocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      calllocs <- mapM (getCalldataLocValue solver ifaceName) activeCLocs
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }

checkRewriteAliasing :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkRewriteAliasing (Act _ contracts)  solver' smttimeout debug =
  forM_ contracts (\(Contract _ behvs) -> do
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    solver <- spawnSolver config
    let behvQs = mkAliasingQuery <$> behvs
    r' <- forM behvQs (\(name, groupedLocs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, groupedLocs, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, [[StorageLocation]], SMT.SMTResult) -> IO ()
    checkRes transition (name, locs, res) =
      case res of
        Sat model -> failMsg ("Rewrites are aliased for " <> transition <> " " <> name <> ".") (prettyAnsi model) (printLocs model locs)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that rewrites are not aliased for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nSolver timeour. Cannot prove that rewrites are not aliased for"  <> transition <> " " <> name <> "."

    printLocs :: Model -> [[StorageLocation]] -> DocAnsi
    printLocs model locs =
      indent 2 $ underline (string "Rewrites:") <> line <> line <>
      vsep (runReader (mapM findAliased locs) model)

    failMsg str model rewrites = render (red (pretty str) <> line <> model <> line <> rewrites <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure


findAliased :: [StorageLocation] -> ModelCtx DocAnsi
findAliased locs =
  vsep <$> mapM checkAliasing pairs
  where
    pairs = combine locs

checkAliasing :: (StorageLocation, StorageLocation) -> ModelCtx DocAnsi
checkAliasing (l1, l2) = do
  isRewrite <- and <$> Control.Monad.zipWithM compareIdx ixs1 ixs2
  if isRewrite then
    liftA2 (<>) (indent 2 . vsep <$> sequence [printAliasedLoc l1, printAliasedLoc l2]) $ pure line
  else pure $ string ""
  where
    ixs1 = ixsFromLocation l1
    ixs2 = ixsFromLocation l2

compareIdx :: TypedExp -> TypedExp -> ModelCtx Bool
compareIdx (TExp SInteger e1) (TExp SInteger e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx (TExp SBoolean e1) (TExp SBoolean e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx (TExp SByteStr e1) (TExp SByteStr e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx _ _ = pure $ False

printAliased :: TypedExp -> ModelCtx DocAnsi
printAliased te@(TExp SInteger e) = do
  e' <- modelEval e
  pure $ string "[(" <> string (prettyTypedExp te) <> string ") = " <> string (show e') <> string "]"
printAliased _ = error "Internal Error: Expected Integer indices"

printAliasedRef :: Ref a -> ModelCtx DocAnsi
printAliasedRef (SArray _ ref _ idcs) =
  liftA2 (<>) (printAliasedRef ref) (concatWith (<>) <$> mapM (printAliased . fst) idcs)
printAliasedRef (SMapping _ ref _ idcs) =
  liftA2 (<>) (printAliasedRef ref) (concatWith (<>) <$> mapM (\te -> pure $ string "[" <> string (prettyTypedExp te) <> string "]") idcs)
printAliasedRef (SField _ ref _ id') =
  liftA2 (<>) (printAliasedRef ref) (pure $ string id')
printAliasedRef (SVar _ _ id') = pure $ string id'
printAliasedRef (CVar _ _ id') = pure $ string id'

printAliasedLoc :: StorageLocation -> ModelCtx DocAnsi
printAliasedLoc (SLoc _ (Item _ _ ref)) = do
  r <- printAliasedRef ref
  pure $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> r
  where
    (AlexPn _ l c ) = posnFromRef ref


modelEval :: forall (a :: ActType). SingI a => Exp a -> ModelCtx (TypeOf a)
modelEval e = case e of
  And  _ a b    -> [ a' && b' | a' <- modelEval a, b' <- modelEval b]
  Or   _ a b    -> [ a' || b' | a' <- modelEval a, b' <- modelEval b]
  Impl _ a b    -> [ a' <= b' | a' <- modelEval a, b' <- modelEval b]
  Neg  _ a      -> not <$> modelEval a
  LT   _ a b    -> [ a' <  b' | a' <- modelEval a, b' <- modelEval b]
  LEQ  _ a b    -> [ a' <= b' | a' <- modelEval a, b' <- modelEval b]
  GT   _ a b    -> [ a' >  b' | a' <- modelEval a, b' <- modelEval b]
  GEQ  _ a b    -> [ a' >= b' | a' <- modelEval a, b' <- modelEval b]
  LitBool _ a   -> pure a

  Add _ a b     -> [ a' + b'     | a' <- modelEval a, b' <- modelEval b]
  Sub _ a b     -> [ a' - b'     | a' <- modelEval a, b' <- modelEval b]
  Mul _ a b     -> [ a' * b'     | a' <- modelEval a, b' <- modelEval b]
  Div _ a b     -> [ a' `div` b' | a' <- modelEval a, b' <- modelEval b]
  Mod _ a b     -> [ a' `mod` b' | a' <- modelEval a, b' <- modelEval b]
  Exp _ a b     -> [ a' ^ b'     | a' <- modelEval a, b' <- modelEval b]
  LitInt  _ a   -> pure a
  IntMin  _ a   -> pure $ intmin  a
  IntMax  _ a   -> pure $ intmax  a
  UIntMin _ a   -> pure $ uintmin a
  UIntMax _ a   -> pure $ uintmax a

  Eq _ SInteger x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ SBoolean x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ SByteStr x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]

  NEq _ SInteger x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ SBoolean x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ SByteStr x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]

  ITE _ a b c   ->  modelEval a >>= \cond -> if cond then modelEval b else modelEval c

  Create _ _ _ -> error "modelEval of contracts not supported"
  VarRef _ whn SStorage item -> do
    model <- ask
    case lookup (_SLoc item) $ if whn == Pre then _mprestate model else _mpoststate model of
      Just (TExp sType e') -> case testEquality (sing @a) sType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          (LitBool _ b) -> pure b
          (ByLit _ s) -> pure s
          _ -> error "modelEval: Model did not return a literal"
        _ -> error "modelEval: Location given does not match type"
      _ -> error "modelEval: Location not found in model"
  VarRef _ _ SCalldata item -> do
    model <- ask
    case lookup (_CLoc item) $ _mcalllocs model of
      Just (TExp sType e') -> case testEquality (sing @a) sType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          (LitBool _ b) -> pure b
          (ByLit _ s) -> pure s
          _ -> error "modelEval: Model did not return a literal"
        _ -> error "modelEval: Location given does not match type"
      _ -> error "modelEval: Location not found in model"

  IntEnv _ env     -> do
    model <- ask
    case lookup env $ _menvironment model of
      Just (TExp sType e') -> case testEquality (sing @a) sType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          _ -> error "modelEval: Model did not return an Integer literal"
        _ -> error "modelEval: Location given does not match type"
      _ -> error "modelEval: Location not found in model"
  _ -> error "modelEval: TODO"