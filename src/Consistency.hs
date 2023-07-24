{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}

module Consistency (
  checkCases
) where


import Prelude hiding (GT, LT)

import Data.List
import Control.Concurrent.Async
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import System.Exit (exitFailure)
import System.IO (stdout)

import Syntax
import Syntax.Annotated
import SMT
import Syntax.Untyped (makeIface)

import Debug.Trace

-- TODO this is duplicated in hevm Keccak.hs but not exported
combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

-- | Checks non-overlapping cases
mkNonoverlapAssertion :: [Exp ABoolean] -> Exp ABoolean
mkNonoverlapAssertion caseconds =
  mkOr $ (\(x, y) -> And nowhere x y) <$> combine caseconds
  where 
    mkOr [] = LitBool nowhere False
    mkOr (c:cs) = Or nowhere c (mkOr cs)

-- | Checks exhaustiveness of cases
mkExhaustiveAssertion :: [Exp ABoolean] -> Exp ABoolean
mkExhaustiveAssertion caseconds =
  foldl mkAnd (LitBool nowhere True) caseconds
  where
    mkAnd r c = And nowhere (Neg nowhere c) r

-- | Create query for cases 
mkCaseQuery :: ([Exp ABoolean] -> Exp ABoolean) -> [Behaviour] -> (Id, SMTExp, (SolverInstance -> IO Model))
mkCaseQuery props behvs@((Behaviour _ _ (Interface ifaceName decls) preconds _ _ _ _):_) =
  (ifaceName, mkSMT, getModel)
  where
    locs = nub $ concatMap locsFromExp (preconds <> caseconds)
    env = concatMap ethEnvFromBehaviour behvs
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

-- | Checks exhaustiveness of cases

checkCases :: Act -> IO ()
checkCases (Act _ contracts) = do
  let groups = concatMap (\(Contract _ behvs) -> groupBy sameIface behvs) contracts
  let config = SMT.SMTConfig CVC5 50000 True -- TODO make this parametrizable
  solver <- spawnSolver config
  let qs = mkCaseQuery mkNonoverlapAssertion <$> groups
  r <- flip mapConcurrently qs (\(name, q, getModel) -> do
                                   res <- checkSat solver getModel q
                                   pure (name, res))
  mapM_ (checkRes "nonoverlapping") r
  let qs' = mkCaseQuery mkExhaustiveAssertion <$> groups
  r' <- flip mapConcurrently qs' (\(name, q, getModel) -> do
                                    traceShowM q
                                    res <- checkSat solver getModel q
                                    pure (name, res))
  mapM_ (checkRes "exhaustive") r'

    where
    
      sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
        makeIface iface == makeIface iface'

      checkRes :: String -> (Id, SMT.SMTResult) -> IO ()
      checkRes check (name, res) =
        case res of
          Sat model -> failMsg ("Cases are not " <> check <> " for behavior " <> name <> ".") (pretty model)
          Unsat -> passMsg $ "Cases are " <> check <> " for behavior " <> name <> "."
          Unknown -> errorMsg $ "Solver timeour. Cannot prove that cases are " <> check <> " for behavior " <> name <> "."
          SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that cases are " <>  check <> " for behavior " <> name <> "."

      passMsg str = render (green $ text str <> line)
      failMsg str model = render (red (text str) <> line <> model <> line) >> exitFailure
      errorMsg str = render (text str <> line) >> exitFailure


-- XXX Duplicate
-- | prints a Doc, with wider output than the built in `putDoc`
render :: Doc -> IO ()
render doc = displayIO stdout (renderPretty 0.9 120 doc)
