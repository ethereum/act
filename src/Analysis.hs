{-
 - ensures:
 - declared identifiers are unique
 - definition types match
 - LHS of storage is a reference
 - preconditions are boolean
 - case conditions are boolean
 - mapping and array types are valid
 - cases are nonempty
 -
 -}

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
import Data.Map.Strict (Map, lookup, empty, intersection, fromList)
import Control.Monad.Writer
import Data.List (intercalate)
import qualified Data.Set

import qualified Syntax as S
import Syntax (ExpF (..))
import RefinedSyntax
import Lex (AlexPosn (..))

pattern For t p = Pair (Const p) t

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

-- binary operations
binop
  :: MType
  -> Either String MType
  -> Either String MType
  -> AlexPosn
  -> String
  -> Either String MType
binop expected t1 t2 p symbol = do
  t1' <- t1 ; t2' <- t2
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
           

check :: Gamma -> S.AnnExpr -> Either String MType
check gamma = cata alg where

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

  -- TODO: check references
  -- alg (For (ERead id) p) =
  --   case lookup id gamma of
  --     Just t -> Right t
  --     Nothing -> Left $ message p ("identifier " <> id <> " unknown")

  alg (For (EEnv env) p) = error "TODO: check EEnv"

  alg (For (EITE t1 t2 t3) p) = do
    t1' <- t1 ; t2' <- t2 ; t3' <- t3
    case (t1' == MBool, t2' == t3') of
      (True, True) -> Right t2'
      (False, _)   ->
        Left $ message p "if/then/else expects boolean condition"
      (_, False)   ->
        Left $ message p "if/then/else expects matching types"

  alg (For EScore p) = error "TODO: typecheck underscores"

  alg _ = error "TODO: check remaining expressions"

check' :: Gamma -> S.AnnExpr -> Writer [String] (Maybe MType)
check' gamma e =
  case check gamma e of
    Left message -> writer (Nothing, [message])
    Right t -> writer (Just t, [])

emboss :: Gamma -> S.Expr -> Typed
emboss gamma = cata alg where

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

  -- integers
  alg (EIntLit i) = T (IntLit i) WInt
  alg (EAdd (T e1 WInt) (T e2 WInt)) = T (Add e1 e2) WInt
  alg (ESub (T e1 WInt) (T e2 WInt)) = T (Sub e1 e2) WInt
  alg (EMul (T e1 WInt) (T e2 WInt)) = T (Mul e1 e2) WInt
  alg (EDiv (T e1 WInt) (T e2 WInt)) = T (Div e1 e2) WInt
  alg (EMod (T e1 WInt) (T e2 WInt)) = T (Mod e1 e2) WInt
  alg (EExp (T e1 WInt) (T e2 WInt)) = T (Exp e1 e2) WInt

  -- TODO: fix reads
  -- alg (ERead id) =
  --   case lookup id gamma of
  --     Just MBool -> T (Read id) WBool
  --     Nothing -> error "malformed expression"

  -- TODO: emboss remaining expressions

  alg _ = error "malformed expression"


-- refine :: Gamma -> S.AnnExpr -> Either String Typed
-- refine gamma e = do
--   t <- check gamma e
--   return $ emboss gamma $ projection e where
--     projection = cata alg
--     alg (Pair _ e) = Fix e

-- transform :: Act S.AnnExpr -> Act (Either String Typed)
-- transform = fmap (refine empty)

-- tester :: Act (Either String Typed) -> Either String ()
-- tester act = foldl folder (Right ()) act

-- TODO: rename
-- rproject = cata alg where
--   alg (Pair _ a) = Fix a

-- mtype :: S.Type -> MType
-- mtype = cata alg where
--   alg S.TBool = MBool
--   alg _ = error "..."

-- interfaceContext :: Annotated Interface -> Either String Gamma
-- interfaceContext (pos, (Interface name decls)) =
--   case length ids == length ids' of
--     True  -> Right $ fromList types
--     False -> Left $ message pos "interface contains duplicate identifiers"
--   where
--     tuple (Decl t id) = (id, t)
--     ids = fmap (projection . snd) decls
--     ids' = Data.Set.fromList ids
--     projection (Decl t id) = id
--     types = fmap ((fmap mtype) . tuple . snd) decls

checkBehaviour
  :: Gamma
  -> S.Behaviour S.AnnExpr
  -> Writer [String] (S.Behaviour MType)
checkBehaviour gamma (S.Behaviour n c i conditions cases) =
  error ""


--   case mergeGamma gamma empty of
--     Nothing -> Left $ message ipos "duplicate identifier"
--     Just gamma' ->
--       case foldr (<>) [] (fmap projection types) of
--         [] -> Right $ fmap unsafeRight types
--         messages -> Left $ intercalate "\n" messages
-- 
--   let types = S.Behaviour n c interface conditions' cases'
--       conditions' = fmap (fmap (check gamma')) conditions
--       cases' = fmap (fmap (fmap (check gamma'))) cases
-- 
--       unsafeRight (Right x) = x
--       unsafeRight (Left _) = error "unreachable"
-- 
--       projection (Left m) = [m]
--       projection (Right _) = []
-- 


mergeGamma :: Gamma -> Gamma -> Maybe Gamma
mergeGamma g1 g2 =
  case length (intersection g1 g2) of
    0 -> Just $ g1 <> g2
    _ -> Nothing

tt = Fix $ EBoolLit True
one = Fix $ EIntLit 1
nottrue = Fix $ ENot tt
notone = Fix $ ENot one
trueandtrue = Fix $ EAnd tt tt
trueandone = Fix $ EAnd one one
e1 = Fix $ Pair (EBoolLit True) (Const (AlexPn 0 1 2))
