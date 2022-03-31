{-# LANGUAGE GADTs #-}

-- {-|
-- Module      : Consistent
-- Description : SMT-based checks of case consistency
-- -}
module Consistent (checkConsistency, abstractCase, testX, testXB, testX3, testXOrTrue) where

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
testXB = (LitBool nowhere True) :: Exp Bool
testX3 = Or nowhere testX testXB :: Exp Bool
testXOrTrue = Or nowhere testX testX :: Exp Bool
abstractCase :: Exp Bool -> State (Int, Map TypedExp Int) (Exp Bool)
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
abstractCase _ = undefined

