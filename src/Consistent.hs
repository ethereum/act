{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

-- {-|
-- Module      : Consistent
-- Description : SMT-based checks of case consistency
-- -}
module Consistent (checkConsistency, abstractCase, testX, testX2, testXV1, testXV2, testXVstr, runExpr) where

import Syntax.Annotated
import Error
import Data.Map (Map)
import Type
import qualified Data.Map as Map
import Control.Monad.State

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

normalize :: Exp Bool -> Exp Bool
normalize (GE pn exp1 exp2) = Neg pn $ LEQ pn exp1 exp2
normalize (GEQ pn exp1 exp2) = Neg pn $ LE pn exp1 exp2
normalize x = x

abstractCases :: [Exp Bool] -> ([Exp Bool], Map TypedExp Id)
abstractCases = undefined


testX = (LE nowhere (Var nowhere SInteger "a") (Var nowhere SInteger "b")) :: Exp Bool
testX2 = (LitBool nowhere True) :: Exp Bool
testXV1 = Var nowhere SInteger "b"
testXV2 = Var nowhere SInteger "a"
testXVstr = Var nowhere SByteStr "abc"

-- NOTE: you HAVE to import Control.Monad.State to have any visibility
-- Here, State is a type constructor:
-- :k Sate
--
abstractCase :: Exp Bool -> State (Int, Map TypedExp Int) (Exp Bool)
-- Only LE is allowed
-- 1) a>b is represented as b<a
-- 2) a>=b is represented as b<=a 
-- 3) a>=b becomes NOT a<b
-- NOTE: this requires well-behaved integers -- reflexivity + transitivity
-- DIV/MUL/SUB/etc are represented as a full-on function, with its own variable
-- TODO: Eq does not work
--       Deal with bytestrings
abstractCase (LitBool pn exp1) = do
    return $ LitBool pn exp1
abstractCase (Or pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ Or pn l r
abstractCase (And pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ And pn l r
abstractCase (GE pn a b) = do
    abstractCase (LE pn b a)
abstractCase (GEQ pn a b) = do
    abstractCase (LEQ pn b a)
abstractCase (LEQ pn a b) = do
    abstractCase (Neg pn (GE nowhere b a))
abstractCase (Neg pn e) = do
    e' <- abstractCase e
    return $ Neg pn e'
abstractCase (Impl pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ Or pn (Neg pn l) r

abstractCase (LE pn exp1 exp2) = do
    (lastVar, ctx) <- get
    var1 <- case Map.lookup (TExp SInteger exp1) ctx of
                  Just v -> return v
                  Nothing -> do
                      put (lastVar+1, Map.insert (TExp SInteger exp1) lastVar ctx)
                      return lastVar
    (lastVar2, ctx2) <- get
    var2 <- case Map.lookup (TExp SInteger exp2) ctx of
                  Just v -> return v
                  Nothing -> do
                      put (lastVar2+1, Map.insert (TExp SInteger exp2) lastVar2 ctx2)
                      return lastVar2
    return $ LE pn (Var pn SInteger $show var1) (Var pn SInteger $show var2)

abstractCase (Eq pn exp1 exp2) = do
    (lastVar, ctx) <- get
    var1 <- case Map.lookup (exp1) ctx of
                  Just v -> return v
                  Nothing -> do
                      put (lastVar+1, Map.insert (exp1) lastVar ctx)
                      return lastVar
    (lastVar2, ctx2) <- get
    var2 <- case Map.lookup (exp2) ctx of
                  Just v -> return v
                  Nothing -> do
                      put (lastVar2+1, Map.insert (exp2) lastVar2 ctx2)
                      return lastVar2
    return $ Eq pn (Var pn SInteger $show var1) (Var pn SInteger $show var2)
abstractCase _ = undefined


-- abstractCase (LE pn exp1 exp2) = do
--     abstractAway LE pn exp1 exp2
-- abstractCase (Eq pn exp1 exp2) = do
--     abstractAway Eq pn exp1 exp2
-- 
-- abstractAway constr pn exp1 exp2 = do
--     (lastVar, ctx) <- get
--     var1 <- case Map.lookup (TExp SInteger exp1) ctx of
--                   Just v -> return v
--                   Nothing -> do
--                       put (lastVar+1, Map.insert (TExp SInteger exp1) lastVar ctx)
--                       return lastVar
--     (lastVar2, ctx2) <- get
--     var2 <- case Map.lookup (TExp SInteger exp2) ctx of
--                   Just v -> return v
--                   Nothing -> do
--                       put (lastVar2+1, Map.insert (TExp SInteger exp2) lastVar2 ctx2)
--                       return lastVar2
--     return $ constr pn (Var pn SInteger $show var1) (Var pn SInteger $show var2)


-- Use this to actually bind & run the Monad
start = (0, Map.empty) :: (Int, Map TypedExp Int)
runExpr expr = runState (abstractCase expr) start

