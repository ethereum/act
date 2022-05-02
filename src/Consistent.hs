{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
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
module Consistent (checkConsistency, abstractCase, testX, testX2, testXV1, testXV2, testXVstr1, testXVstr2, testXbool1, testXbool2, runExpr, abstractCases) where

import Syntax.Annotated
import Error
import Type.Reflection
import Data.Map (Map)
import Type
import Data.Typeable
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

start :: (Int, Map (Exp Bool) Int)
start = (0, Map.empty)
runExpr :: Exp Bool -> (MyExp Bool, (Int, Map (Exp Bool) Int))
runExpr expr = runState (abstractCase expr) start

abstractCases :: [Exp Bool] -> [MyExp Bool]
abstractCases a = y where
  (x, y, z) = abstractCasesHelper (a, [], start)
type MyPair = ([Exp Bool], [MyExp Bool], (Int, Map(Exp Bool) Int))
abstractCasesHelper :: MyPair -> MyPair
abstractCasesHelper ([], b, c) = ([], b, c)
abstractCasesHelper (a:ax, b, c)  = abstractCasesHelper (ax, x:b, y) where
  (x, y) = runState (abstractCase a) c

-- Use this to actually bind & run the Monad

testX = (GE nowhere (Var nowhere SInteger "a") (Var nowhere SInteger "b")) :: Exp Bool
testX2 = (LEQ nowhere (Var nowhere SInteger "b") (Var nowhere SInteger "a")) :: Exp Bool
testXbool1 = (LitBool nowhere True) :: Exp Bool
testXbool2 = (LitBool nowhere False) :: Exp Bool
testXV1 = Var nowhere SInteger "b"
testXV2 = Var nowhere SInteger "a"
testXVstr1 = Var nowhere SByteStr "abc"
testXVstr2 = Var nowhere SByteStr "fgh"

-- NOTE: you HAVE to import Control.Monad.State to have any visibility
-- Here, State is a type constructor:
-- :k Sate
--

data MyExp (a :: *) where
  -- boolean variables
  MInt  :: Pn -> Int -> MyExp Bool
  MAnd  :: Pn -> MyExp Bool -> MyExp Bool -> MyExp Bool
  MBool :: Pn -> Bool -> MyExp Bool
  MOr   :: Pn -> MyExp Bool -> MyExp Bool -> MyExp Bool
  MNeg  :: Pn -> MyExp Bool -> MyExp Bool
  MEq   :: Pn -> MyExp Bool -> MyExp Bool -> MyExp Bool
deriving instance Show (MyExp a)

abstractCase :: Exp Bool -> State (Int, Map (Exp Bool) Int) (MyExp Bool)
-- Only LE is allowed
-- 1) a>b is represented as b<a
-- 2) a>=b is represented as b<=a 
-- 3) a>=b becomes NOT a<b
-- NOTE: this requires well-behaved integers -- reflexivity + transitivity
-- DIV/MUL/SUB/etc are represented as a full-on function, with its own variable
abstractCase (LitBool pn exp1) = do
    return $ MBool pn exp1
abstractCase (Or pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ MOr pn l r
abstractCase (And pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ MAnd pn l r
abstractCase (GE pn a b) = do
    x <- abstractCase (LE pn b a)
    return $ MNeg nowhere x
abstractCase (GEQ pn a b) = do
    x <- abstractCase (LEQ pn b a)
    return $ MNeg nowhere x
abstractCase (LEQ pn a b) = do
    abstractCase (Neg pn (GE nowhere b a))
abstractCase (ITE pn a b c) = do
    e1 <- abstractCase a
    e2 <- abstractCase b
    e3 <- abstractCase c
    return $ MAnd pn (MOr nowhere (MNeg nowhere e1) e2) (MOr nowhere e1 e3)
abstractCase (Neg pn e) = do
    e' <- abstractCase e
    return $ MNeg pn e'
abstractCase (Impl pn exp1 exp2) = do
    l <- abstractCase exp1
    r <- abstractCase exp2
    return $ MOr pn (MNeg pn l) r
abstractCase (NEq pn exp1 exp2) = do
     e1 <- abstractCase (Eq pn exp1 exp2)
     return $ MNeg pn e1
abstractCase (LE pn exp1 exp2) = do
    (lastVar, ctx) <- get
    var1 <- case Map.lookup (LE nowhere exp1 exp2) ctx of
                  Just v -> return v
                  Nothing -> do
                      put (lastVar+1, Map.insert (LE nowhere exp1 exp2) lastVar ctx)
                      return lastVar
    return $ MInt pn var1
abstractCase (Eq pn (l1 :: Exp tp) (l2 :: Exp tp)) = case eqT @tp @Bool of
  Just Refl -> do
    u1 <- abstractCase l1
    u2 <- abstractCase l2
    return $ MEq pn u1 u2
  Nothing -> do
    (lastVar, ctx) <- get
    var1 <- case Map.lookup (Eq nowhere l1 l2) ctx of
                  Just v -> return v
                  Nothing -> do
                      put (lastVar+1, Map.insert (Eq nowhere l1 l2) lastVar ctx)
                      return lastVar
    return $ MInt pn var1
abstractCase _ = undefined


