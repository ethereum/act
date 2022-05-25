{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- {-|
-- Module      : Consistent
-- Description : SMT-based checks of case consistency
-- -}
module Consistent where

import Syntax.Annotated
import Syntax
import Error
import Type.Reflection
import Data.Map (Map)
import Type
import Data.Typeable
import qualified Data.Map as Map
import Control.Monad.State
import Prelude hiding (LT, GT)
import Data.Set as Set
import Data.List (tails, nub, sort)
import Data.Containers.ListUtils (nubOrd)
import SMT
import Debug.Trace
import Data.Validation (fromEither)

checkConsistency :: [Claim] -> Err [Claim]
checkConsistency = undefined

-- Contract -> Interface -> Cases
mygrouping :: [Claim] -> Map Id (Map Id [Exp Bool])
mygrouping = undefined

type Ctx = Int
-- doSmth :: Ctx -> Int -> Int
-- doSmth x = do
--   ctx <- get
--   put 10

-- checkcases -> normalize -> abstractcases

checkcases :: [Exp Bool] -> Error String ()
checkcases = undefined

-- To be run like: "checkNoOverlap abstractCases [Exp Bool]". It will then:
--   Abstract away, while checking that abstractions don't have overlapping variables
--   Then checks the cases don't overlap.
checkNoOverlap :: [Err (Exp Bool)] -> IO (Err ())
checkNoOverlap x = do
  let config = SMT.SMTConfig {_solver=SMT.Z3, _timeout=100, _debug=False}
  solverInstance <- spawnSolver config
  let mypairs = pairs (successes x) :: [Exp Bool] -- TODO filtering here!!!
  traceM (show mypairs)
  let queries = expToQuery <$> (mypairs) :: [SMT2]
  traceM (show queries)
  results <- mapM (checkSat solverInstance throwaway) (queries) :: IO [SMTResult]
  traceM (show results)
  return $ resultsAgg results
  where
    throwaway :: SMT.SolverInstance -> IO Model
    throwaway  _ = pure $ Model
      { _mprestate  = []
      , _mpoststate = []
      , _mcalldata = ("", [])
      , _menvironment = []
      , _minitargs = []
      }
    expToQuery :: Exp Bool -> SMT2
    expToQuery e = (unlines init) ++ assert
      where
        assert = mkAssert "" e
        names = namesFromExp e :: Set (TypedExp)
        init =  toList $ Set.map (flip SMT.constant Boolean . withInterface "" . typedExpToSMT2) names :: [SMT2]

    pairs :: [Exp Bool] -> [Exp Bool]
    pairs xs = [And nowhere x y | (x:ys) <- tails (xs), y <- ys]
    resultsAgg :: [SMTResult] -> Err ()
    resultsAgg [] = Success ()
    resultsAgg (a:ax) = if (not $ isFail a) then (resultsAgg ax) else (throw (nowhere, "a"))


-- We look up Exp Bool in `expression`, and if it's not there
--    then we check if it matches any in setOfVars. If it does
--    we cannot guarantee uniqueness
data AbstFunc = AbstFunc
  { setOfVars  :: Set (TypedExp)
  , expression :: Map (Exp Bool) Int
  } deriving Show
start :: (Int, AbstFunc)
start = (0, AbstFunc {setOfVars = Set.empty, expression = Map.empty})

successes :: [Validation e a] -> [a]
successes v = [a | Success a <- v]

failures :: [Validation e a] -> [e]
failures v = [e | Failure e <- v]

-- Checks also DISTINCT cases. Currently, they can overlap
-- For example: (a<b) can be overlapping with a=c
-- we can accomplish this via namesFromExp
abstractCases :: [Exp Bool] -> [Err (Exp Bool)]
-- another way: abstractCases :: [Exp Bool] -> [Err (Exp Bool)]
--              abstractCases a = Success (successes y) where -- which forgets all errors :(
abstractCases a = (y) where
  (x, y, z) = abstractCasesHelper (a, [], start)
type MyPair = ([Exp Bool], [Err (Exp Bool)], (Int, AbstFunc))
abstractCasesHelper :: MyPair -> MyPair
abstractCasesHelper ([], b, c) = ([], b, c)
abstractCasesHelper (a:ax, b, c)  = abstractCasesHelper (ax, z, y) where
  (x, y) = runState (abstractCase a) c
  z = x:(b)

-- Use this to actually bind & run the Monad

testX1 = (GT nowhere (Var nowhere SInteger "a") (Var nowhere SInteger "b")) :: Exp Bool
testX2 = (LEQ nowhere (Var nowhere SInteger "b") (Var nowhere SInteger "a")) :: Exp Bool
testX3 = (Eq nowhere (Var nowhere SInteger "b") (Var nowhere SInteger "a")) :: Exp Bool
testXbool1 = (LitBool nowhere True) :: Exp Bool
testXbool2 = (LitBool nowhere False) :: Exp Bool
testXV1 = Var nowhere SInteger "a"
testXV2 = Var nowhere SInteger "b"
testXV3 = TEntry nowhere Post (Item SInteger "contr" "y" [])
testXV4 = TEntry nowhere Post (Item SInteger "contr" "z" [])
testXVstr1 = Var nowhere SByteStr "x"
testXVstr2 = Var nowhere SByteStr "y"
testXVb = Var nowhere SBoolean "a"
varBool = Var nowhere SInteger "myBoolvar"

abstractCase :: Exp Bool -> State (Int, AbstFunc) (Err (Exp Bool))
-- Only LT is allowed
-- 1) a>b is represented as b<a
-- 2) a>=b is represented as b<=a
-- 3) a>=b becomes NOT a<b
-- NOTE: this requires well-behaved integers -- reflexivity + transitivity
-- DIV/MUL/SUB/etc are represented as a full-on function, with its own variable
abstractCase (LitBool pn exp1) = do
    return $ Success (LitBool pn exp1)
abstractCase (Or pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ do
      l' <- l
      r' <- r
      pure $ Or pn l' r'
abstractCase (And pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ do
      l' <- l
      r' <- r
      pure $ And pn l' r'
abstractCase (GT pn a b) = do
    x <- abstractCase (LT pn b a)
    return $ do
      x' <- x
      pure $ Neg nowhere x'
abstractCase (GEQ pn a b) = do
    let x = LEQ pn b a
    return $ do
      pure $ Neg nowhere x
abstractCase (LEQ pn a b) = do
    abstractCase (Neg pn (GT nowhere b a))
abstractCase (ITE pn a b c) = do
    e1 <- abstractCase a
    e2 <- abstractCase b
    e3 <- abstractCase c
    return $ do
      e1' <- e1
      e2' <- e2
      e3' <- e3
      pure $ And pn (Or nowhere (Neg nowhere e1') e2') (Or nowhere e1' e3')
abstractCase (Neg pn e) = do
    x <- abstractCase e
    return $ do
      x' <- x
      return $ Neg pn x'
abstractCase (Impl pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ do
      l' <- l
      r' <- r
      pure $ Or pn (Neg pn l') r'
abstractCase (NEq pn exp1 exp2) = do
    x <- abstractCase (Eq pn exp1 exp2)
    return $ do
      x' <- x
      pure $ Neg pn x'
abstractCase (LT pn exp1 exp2) = do
    (lastVar, ctx) <- get
    var1 <- case Map.lookup (LT nowhere exp1 exp2) (expression ctx) of
       Just v -> return v
       Nothing -> do
         let exp1Names = (Syntax.namesFromExp exp1)
         let exp2Names = (Syntax.namesFromExp exp2)
         let check =(exp1Names `union` exp2Names) `intersection` (setOfVars ctx)
         if check == Set.empty then do
           let x = exp1Names `union` exp2Names `union` setOfVars ctx
           let y = Map.insert (LT nowhere exp1 exp2) lastVar (expression ctx)
           put (lastVar+1, AbstFunc {setOfVars = x, expression=y})
           return lastVar
         else
           return 999
    if var1 == 999 then return $ throw (nowhere, "Abtracted expression uses same set of inputs twice")
    else return $ do
      pure $ Var pn SBoolean (show var1)
abstractCase (Eq pn (exp1 :: Exp tp) (exp2 :: Exp tp)) = case eqT @tp @Bool of
  Just Refl -> do
    u1 <- abstractCase exp1
    u2 <- abstractCase exp2
    return $ do
      u1' <- u1
      u2' <- u2
      pure $ Eq pn u1' u2'
  Nothing -> do
    (lastVar, ctx) <- get
    var1 <- case Map.lookup (Eq nowhere exp1 exp2) (expression ctx) of
       Just v -> return v
       Nothing -> do
         let exp1Names = (Syntax.namesFromExp exp1)
         let exp2Names = (Syntax.namesFromExp exp2)
         let check =(exp1Names `union` exp2Names) `intersection` (setOfVars ctx)
         if check == Set.empty then do
           let x = exp1Names `union` exp2Names `union` setOfVars ctx
           let y = Map.insert (Eq nowhere exp1 exp2) lastVar (expression ctx)
           put (lastVar+1, AbstFunc {setOfVars = x, expression=y})
           return lastVar
         else
           return 999
    if var1 == 999 then return $ throw (nowhere, "Abtracted expression uses same set of inputs twice")
    else return $ do
      pure $ Var pn SBoolean (show var1)
abstractCase _ = undefined


