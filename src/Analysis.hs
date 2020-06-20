{-# LANGUAGE GADTs     #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Analysis where


import Prelude hiding (lookup, EQ, GT, LT)
import Data.Functor.Foldable
import Data.Functor.Product
import Data.Functor.Const
import Data.Map.Strict (Map, lookup)

import Syntax
import RefinedSyntax
import Lex (AlexPosn (..))

pattern For t p = Pair t (Const p)

-- error message formatter
message (AlexPn _ line column) s =
  show line <> ":" <> show column <> " : " <> s

-- integer relations
binrel
  :: Either String MType    -- t1
  -> Either String MType    -- t2
  -> AlexPosn
  -> String                 -- symbol
  -> Either String MType
binrel t1 t2 p symbol = do
  t1' <- t1 ; t2' <- t2
  case (t1', t2') of
    (MInt, MInt) -> Right MBool
    _            -> Left $
      message p ("operator `" <> symbol <> "` expects integers")

-- integer or boolean relations
binrel'
  :: Either String MType    -- t1
  -> Either String MType    -- t2
  -> AlexPosn
  -> String                 -- symbol
  -> Either String MType
binrel' t1 t2 p symbol = do
  t1' <- t1 ; t2' <- t2
  case (t1', t2') of
    (MBool, MBool) -> Right MBool
    (MInt , MInt ) -> Right MBool
    _              -> Left $
      message p ("operator `" <> symbol <> "` type mismatch")

-- binary operation helper
binop
  :: MType
  -> Either String MType
  -> Either String MType
  -> AlexPosn
  -> String
  -> Either String MType
binop expected t1 t2 p symbol = do
  t1' <- t2 ; t2' <- t2
  if t1' == expected && t2' == expected then
    Right t1'
  else
    Left $ message p $ concat [
        "operator `"
      , symbol
      , "` expects ("
      , show expected
      , ", "
      , show expected
      , ")"
    ]
           

typecheck :: Gamma -> AnnExpr -> Either String MType
typecheck gamma = cata alg where

  -- boolean operations
  alg (For (EBoolLit b) p) = Right MBool
  alg (For (ENot t) p) = do
    t' <- t
    if t' == MBool then
      Right MBool
    else
      Left $ message p "operator `not` expects Bool"
  alg (For (EAnd t1 t2) p) = binop MBool t1 t2 p "and"
  alg (For (EOr t1 t2) p) = binop MBool t1 t2 p "or"
  alg (For (EImpl t1 t2) p) = binop MBool t1 t2 p "=>"

  -- binary relations
  -- `==` and `=/=` are polymorphic (excluding mappings)
  -- the rest are not
  alg (For (EEq  t1 t2) p) = binrel' t1 t2 p "=="
  alg (For (ENEq t1 t2) p) = binrel' t1 t2 p "=/="
  alg (For (ELE  t1 t2) p) = binrel t1 t2 p "<="
  alg (For (ELT  t1 t2) p) = binrel t1 t2 p "<"
  alg (For (EGE  t1 t2) p) = binrel t1 t2 p ">="
  alg (For (EGT  t1 t2) p) = binrel t1 t2 p ">"

  -- numeric operations
  alg (For (EIntLit i) p) = Right MInt
  alg (For (EAdd t1 t2) p) = binop MInt t1 t2 p "+"
  alg (For (ESub t1 t2) p) = binop MInt t1 t2 p "-"
  alg (For (EMul t1 t2) p) = binop MInt t1 t2 p "*"
  alg (For (EDiv t1 t2) p) = binop MInt t1 t2 p "/"
  alg (For (EMod t1 t2) p) = binop MInt t1 t2 p "%"
  alg (For (EExp t1 t2) p) = binop MInt t1 t2 p "^"

  -- other

  alg (For (ERead id) p) =
    case lookup id gamma of
      Just t -> Right t
      Nothing -> Left $ message p ("identifier " <> id <> " unknown")

  alg (For (EZoom t1 t2) p) = do
    t1' <- t1 ; t2' <- t2
    case t1' of
      MMap k v ->
        if t2' == k then
          Right v
        else
          Left $ message p ("mapping expected key of type " <> show k)

  alg (For (EEnv env) p) = error "TODO: typecheck EEnv"

  alg (For (EITE t1 t2 t3) p) = do
    t1' <- t1 ; t2' <- t2 ; t3' <- t3
    case (t1' == MBool, t2' == t3') of
      (True, True) -> Right t2'
      (False, _)   ->
        Left $ message p "if/then/else expects boolean condition"
      (_, False)   ->
        Left $ message p "if/then/else expects matching types"

  alg (For EScore p) = error "TODO: typecheck underscores"


emboss :: Expr -> Typed
emboss = cata alg where

  -- booleans
  alg (EBoolLit b) = T (BoolLit b) WBool
  alg (ENot (T e WBool)) = T (Not e) WBool
  alg (EAnd (T e1 WBool) (T e2 WBool)) = T (And e1 e2) WBool
  alg (EOr (T e1 WBool) (T e2 WBool)) = T (Or e1 e2) WBool
  alg (EImpl (T e1 WBool) (T e2 WBool)) = T (Impl e1 e2) WBool
  
  -- binary relations
  alg (EEq (T e1 WBool) (T e2 WBool)) = T (Eq e1 e2) WBool
  alg (EEq (T e1 WInt) (T e2 WInt)) = T (Eq e1 e2) WBool
  alg (ENEq (T e1 WBool) (T e2 WBool)) = T (NEq e1 e2) WBool
  alg (ENEq (T e1 WInt) (T e2 WInt)) = T (NEq e1 e2) WBool
  alg (ELE (T e1 WInt) (T e2 WInt)) = T (LE e1 e2) WBool
  alg (ELT (T e1 WInt) (T e2 WInt)) = T (LT e1 e2) WBool
  alg (EGE (T e1 WInt) (T e2 WInt)) = T (GE e1 e2) WBool
  alg (EGT (T e1 WInt) (T e2 WInt)) = T (GT e1 e2) WBool

  -- TODO: emboss remaining expressions

  alg _ = error "malformed expression"

refineBehaviour :: RawBehaviour -> [AnnExpr]
refineBehaviour (RawBehaviour name contract interface preconditions cases) =
  map f cases where
  f ((Case condition claim), _) = condition



tt = Fix $ EBoolLit True
one = Fix $ EIntLit 1
nottrue = Fix $ ENot tt
notone = Fix $ ENot one
trueandtrue = Fix $ EAnd tt tt
trueandone = Fix $ EAnd one one
e1 = Fix $ Pair (EBoolLit True) (Const (AlexPn 0 1 2))
