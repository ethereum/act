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



-- We look up Exp Bool in `expression`, and if it's not there
--    then we check if it matches any in setOfVars. If it does
--    we cannot guarantee uniqueness
data AbstFunc = AbstFunc
  { setOfVars  :: Set (TypedExp)
  , expression :: Map (Exp Bool) Int
  } deriving Show
start :: (Int, AbstFunc)
start = (0, AbstFunc {setOfVars = Set.empty, expression = Map.empty})

runExpr :: Exp Bool -> (MyExp, (Int, AbstFunc))
runExpr expr = runState (abstractCase expr) start

-- TODO: we need to DISTINCT cases. Currently, they can overlap
-- For example: (a<b) can be overlapping with a=c
-- we can accomplish this via namesFromExp
abstractCases :: [Exp Bool] -> [MyExp]
abstractCases a = y where
  (x, y, z) = abstractCasesHelper (a, [], start)
type MyPair = ([Exp Bool], [MyExp], (Int, AbstFunc))
abstractCasesHelper :: MyPair -> MyPair
abstractCasesHelper ([], b, c) = ([], b, c)
abstractCasesHelper (a:ax, b, c)  = abstractCasesHelper (ax, x:b, y) where
  (x, y) = runState (abstractCase a) c

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

-- NOTE: you HAVE to import Control.Monad.State to have any visibility
-- Here, State is a type constructor:
-- :k Sate
--

data MyExp where
  -- boolean variables
  MInt  :: Pn -> Int -> MyExp
  MAnd  :: Pn -> MyExp -> MyExp -> MyExp
  MBool :: Pn -> Bool -> MyExp
  MOr   :: Pn -> MyExp -> MyExp -> MyExp
  MNeg  :: Pn -> MyExp -> MyExp
  MEq   :: Pn -> MyExp -> MyExp -> MyExp
deriving instance Show MyExp

abstractCase :: Exp Bool -> State (Int, AbstFunc) (MyExp)
-- Only LT is allowed
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
abstractCase (GT pn a b) = do
    x <- abstractCase (LT pn b a)
    return $ MNeg nowhere x
abstractCase (GEQ pn a b) = do
    x <- abstractCase (LEQ pn b a)
    return $ MNeg nowhere x
abstractCase (LEQ pn a b) = do
    abstractCase (Neg pn (GT nowhere b a))
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
    return $ MInt pn var1
abstractCase (Eq pn (exp1 :: Exp tp) (exp2 :: Exp tp)) = case eqT @tp @Bool of
  Just Refl -> do
    u1 <- abstractCase exp1
    u2 <- abstractCase exp2
    return $ MEq pn u1 u2
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
    return $ MInt pn var1
abstractCase _ = undefined


