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

import Syntax
import Syntax.Annotated
import SMT
import Syntax.Untyped (makeIface)

-- TODO this is duplicated in hevm Keccak.hs but not exported
combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

-- | Checks non-overlapping cases
mkNonoverapQuery :: [Behaviour] -> (Id, SMTExp, (SolverInstance -> IO Model))
mkNonoverapQuery behvs@((Behaviour _ _ (Interface ifaceName decls) preconds _ _ _ _):_) =
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
      , _assertions = pres <> [allPairs]
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

    allPairs = mkAssert ifaceName <$> mkOr $ (\(x, y) -> And nowhere x y) <$> combine caseconds

    mkOr [] = LitBool nowhere False
    mkOr (c:cs) = Or nowhere c (mkOr cs)
mkNonoverapQuery [] = error "Internal error: behaviours cannot be empty"

checkCases :: Act -> IO [(Id, SMTResult)]
checkCases (Act _ contracts) = do
  let groups = concatMap (\(Contract _ behvs) -> groupBy sameIface behvs) contracts
  let config = SMT.SMTConfig CVC5 50000 True -- TODO make this parametrizable
  solver <- spawnSolver config
  let qs = mkNonoverapQuery <$> groups
  flip mapConcurrently qs (\(name, q, getModel) -> do
                              res <- checkSat solver getModel q
                              pure (name, res))
  where 
   sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
     makeIface iface == makeIface iface'
