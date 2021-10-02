{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Syntax
Description : Functions for manipulating and collapsing all our different ASTs.
-}
module Syntax where

import Data.List
import Data.Map (Map,empty,insertWith,unionsWith)
import Data.Singletons

import Syntax.TimeAgnostic as Agnostic
import qualified Syntax.Annotated as Annotated
import           Syntax.Untyped hiding (Constant,Rewrite)
import qualified Syntax.Untyped as Untyped

-----------------------------------------
-- * Extract from fully refined ASTs * --
-----------------------------------------

-- | Invariant predicates can always be expressed as a single expression.
invExp :: Annotated.InvariantPred -> Annotated.Exp Bool
invExp = uncurry (<>)

locsFromBehaviour :: Annotated.Behaviour -> [Annotated.StorageLocation]
locsFromBehaviour (Behaviour _ _ _ _ preconds postconds rewrites returns) = nub $
  concatMap locsFromExp preconds
  <> concatMap locsFromExp postconds
  <> concatMap locsFromRewrite rewrites
  <> maybe [] locsFromTypedExp returns

locsFromConstructor :: Annotated.Constructor -> [Annotated.StorageLocation]
locsFromConstructor (Constructor _ _ _ pre post initialStorage rewrites) = nub $
  concatMap locsFromExp pre
  <> concatMap locsFromExp post
  <> concatMap locsFromRewrite rewrites
  <> concatMap locsFromRewrite (Rewrite <$> initialStorage)

------------------------------------
-- * Extract from any typed AST * --
------------------------------------

behvsFromClaims :: [Claim t] -> [Behaviour t]
behvsFromClaims claims = [b | B b <- claims]

locsFromRewrite :: Rewrite t -> [StorageLocation t]
locsFromRewrite update = nub $ case update of
  Constant loc -> [loc]
  Rewrite (Update _ item e) -> locsFromItem item <> locsFromExp e

locFromRewrite :: Rewrite t -> StorageLocation t
locFromRewrite = onRewrite id locFromUpdate

locFromUpdate :: StorageUpdate t -> StorageLocation t
locFromUpdate (Update _ item _) = _Loc item

locsFromItem :: TStorageItem a t -> [StorageLocation t]
locsFromItem item = _Loc item : concatMap locsFromTypedExp (ixsFromItem item)

locsFromTypedExp :: TypedExp t -> [StorageLocation t]
locsFromTypedExp (TExp _ e) = locsFromExp e

locsFromExp :: Exp a t -> [StorageLocation t]
locsFromExp = nub . go
  where
    go :: Exp a t -> [StorageLocation t]
    go e = case e of
      And a b   -> go a <> go b
      Or a b    -> go a <> go b
      Impl a b  -> go a <> go b
      Eq a b    -> go a <> go b
      LE a b    -> go a <> go b
      LEQ a b   -> go a <> go b
      GE a b    -> go a <> go b
      GEQ a b   -> go a <> go b
      NEq a b   -> go a <> go b
      Neg a     -> go a
      Add a b   -> go a <> go b
      Sub a b   -> go a <> go b
      Mul a b   -> go a <> go b
      Div a b   -> go a <> go b
      Mod a b   -> go a <> go b
      Exp a b   -> go a <> go b
      Cat a b   -> go a <> go b
      Slice a b c -> go a <> go b <> go c
      ByStr _ -> []
      ByLit _ -> []
      LitInt _  -> []
      IntMin _  -> []
      IntMax _  -> []
      UIntMin _ -> []
      UIntMax _ -> []
      LitBool _ -> []
      NewAddr a b -> go a <> go b
      IntEnv _ -> []
      ByEnv _ -> []
      ITE x y z -> go x <> go y <> go z
      TEntry _ a -> locsFromItem a
      Var _ _ -> []

ethEnvFromBehaviour :: Behaviour t -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds postconds rewrites returns) = nub $
  concatMap ethEnvFromExp preconds
  <> concatMap ethEnvFromExp postconds
  <> concatMap ethEnvFromRewrite rewrites
  <> maybe [] ethEnvFromTypedExp returns

ethEnvFromConstructor :: Constructor t -> [EthEnv]
ethEnvFromConstructor (Constructor _ _ _ pre post initialStorage rewrites) = nub $
  concatMap ethEnvFromExp pre
  <> concatMap ethEnvFromExp post
  <> concatMap ethEnvFromRewrite rewrites
  <> concatMap ethEnvFromRewrite (Rewrite <$> initialStorage)

ethEnvFromRewrite :: Rewrite t -> [EthEnv]
ethEnvFromRewrite rewrite = case rewrite of
  Constant (Loc _ item) -> ethEnvFromItem item
  Rewrite (Update _ item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TStorageItem a t -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromItem

ethEnvFromTypedExp :: TypedExp t -> [EthEnv]
ethEnvFromTypedExp (TExp _ e) = ethEnvFromExp e

ethEnvFromExp :: Exp a t -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp a t -> [EthEnv]
    go e = case e of
      And a b   -> go a <> go b
      Or a b    -> go a <> go b
      Impl a b  -> go a <> go b
      Eq a b    -> go a <> go b
      LE a b    -> go a <> go b
      LEQ a b   -> go a <> go b
      GE a b    -> go a <> go b
      GEQ a b   -> go a <> go b
      NEq a b   -> go a <> go b
      Neg a     -> go a
      Add a b   -> go a <> go b
      Sub a b   -> go a <> go b
      Mul a b   -> go a <> go b
      Div a b   -> go a <> go b
      Mod a b   -> go a <> go b
      Exp a b   -> go a <> go b
      Cat a b   -> go a <> go b
      Slice a b c -> go a <> go b <> go c
      ITE a b c -> go a <> go b <> go c
      ByStr _ -> []
      ByLit _ -> []
      LitInt _  -> []
      LitBool _ -> []
      IntMin _ -> []
      IntMax _ -> []
      UIntMin _ -> []
      UIntMax _ -> []
      NewAddr a b -> go a <> go b
      IntEnv a -> [a]
      ByEnv a -> [a]
      TEntry _ a -> ethEnvFromItem a
      Var _ _ -> []

idFromRewrite :: Rewrite t -> Id
idFromRewrite = onRewrite idFromLocation idFromUpdate

idFromItem :: TStorageItem a t -> Id
idFromItem (Item _ _ name _) = name

idFromUpdate :: StorageUpdate t -> Id
idFromUpdate (Update _ item _) = idFromItem item

idFromLocation :: StorageLocation t -> Id
idFromLocation (Loc _ item) = idFromItem item

contractFromRewrite :: Rewrite t -> Id
contractFromRewrite = onRewrite contractFromLoc contractFromUpdate

contractFromItem :: TStorageItem a t -> Id
contractFromItem (Item _ c _ _) = c

ixsFromItem :: TStorageItem a t -> [TypedExp t]
ixsFromItem (Item _ _ _ ixs) = ixs

contractsInvolved :: Behaviour t -> [Id]
contractsInvolved = fmap contractFromRewrite . _stateUpdates

contractFromLoc :: StorageLocation t -> Id
contractFromLoc (Loc _ item) = contractFromItem item

contractFromUpdate :: StorageUpdate t -> Id
contractFromUpdate (Update _ item _) = contractFromItem item

ixsFromLocation :: StorageLocation t -> [TypedExp t]
ixsFromLocation (Loc _ item) = ixsFromItem item

ixsFromUpdate :: StorageUpdate t -> [TypedExp t]
ixsFromUpdate (Update _ item _) = ixsFromItem item

ixsFromRewrite :: Rewrite t -> [TypedExp t]
ixsFromRewrite = onRewrite ixsFromLocation ixsFromUpdate

itemType :: TStorageItem a t -> MType
itemType (Item t _ _ _) = fromSing t

isMapping :: StorageLocation t -> Bool
isMapping = not . null . ixsFromLocation

onRewrite :: (StorageLocation t -> a) -> (StorageUpdate t -> a) -> Rewrite t -> a
onRewrite f _ (Constant  a) = f a
onRewrite _ g (Rewrite a) = g a

updatesFromRewrites :: [Rewrite t] -> [StorageUpdate t]
updatesFromRewrites rs = [u | Rewrite u <- rs]

locsFromRewrites :: [Rewrite t] -> [StorageLocation t]
locsFromRewrites rs = [l | Constant l <- rs]

--------------------------------------
-- * Extraction from untyped ASTs * --
--------------------------------------

nameFromStorage :: Untyped.Storage -> Id
nameFromStorage (Untyped.Rewrite (PEntry _ x _) _) = x
nameFromStorage (Untyped.Constant (PEntry _ x _)) = x
nameFromStorage store = error $ "Internal error: cannot extract name from " ++ show store

getPosn :: Expr -> Pn
getPosn expr = case expr of
    EAnd pn  _ _ -> pn
    EOr pn _ _ -> pn
    ENot pn _ -> pn
    EImpl pn _ _ -> pn
    EEq pn _ _ -> pn
    ENeq pn _ _ -> pn
    ELEQ pn _ _ -> pn
    ELT pn _ _ -> pn
    EGEQ pn _ _ -> pn
    EGT pn _ _ -> pn
    EAdd pn _ _ -> pn
    ESub pn _ _ -> pn
    EITE pn _ _ _ -> pn
    EMul pn _ _ -> pn
    EDiv pn _ _ -> pn
    EMod pn _ _ -> pn
    EExp pn _ _ -> pn
    Zoom pn _ _ -> pn
    EUTEntry pn _ _ -> pn
    EPreEntry pn _ _ -> pn
    EPostEntry pn _ _ -> pn
    Func pn _ _ -> pn
    ListConst e -> getPosn e
    ECat pn _ _ -> pn
    ESlice pn _ _ _ -> pn
    ENewaddr pn _ _ -> pn
    ENewaddr2 pn _ _ _ -> pn
    BYHash pn _ -> pn
    BYAbiE pn _ -> pn
    StringLit pn _ -> pn
    WildExp pn -> pn
    EnvExp pn _ -> pn
    IntLit pn _ -> pn
    BoolLit pn _ -> pn

posFromDef :: Defn -> Pn
posFromDef (Defn e _) = getPosn e

-- | Returns all the identifiers used in an expression,
-- as well all of the positions they're used in.
idFromRewrites :: Expr -> Map Id [Pn]
idFromRewrites e = case e of
  EAnd _ a b        -> idFromRewrites' [a,b]
  EOr _ a b         -> idFromRewrites' [a,b]
  ENot _ a          -> idFromRewrites a
  EImpl _ a b       -> idFromRewrites' [a,b]
  EEq _ a b         -> idFromRewrites' [a,b]
  ENeq _ a b        -> idFromRewrites' [a,b]
  ELEQ _ a b        -> idFromRewrites' [a,b]
  ELT _ a b         -> idFromRewrites' [a,b]
  EGEQ _ a b        -> idFromRewrites' [a,b]
  EGT _ a b         -> idFromRewrites' [a,b]
  EAdd _ a b        -> idFromRewrites' [a,b]
  ESub _ a b        -> idFromRewrites' [a,b]
  EITE _ a b c      -> idFromRewrites' [a,b,c]
  EMul _ a b        -> idFromRewrites' [a,b]
  EDiv _ a b        -> idFromRewrites' [a,b]
  EMod _ a b        -> idFromRewrites' [a,b]
  EExp _ a b        -> idFromRewrites' [a,b]
  Zoom _ a b        -> idFromRewrites' [a,b]
  EUTEntry p x es   -> insertWith (<>) x [p] $ idFromRewrites' es
  EPreEntry p x es  -> insertWith (<>) x [p] $ idFromRewrites' es
  EPostEntry p x es -> insertWith (<>) x [p] $ idFromRewrites' es
  Func _ _ es       -> idFromRewrites' es
  ListConst a       -> idFromRewrites a
  ECat _ a b        -> idFromRewrites' [a,b]
  ESlice _ a b c    -> idFromRewrites' [a,b,c]
  ENewaddr _ a b    -> idFromRewrites' [a,b]
  ENewaddr2 _ a b c -> idFromRewrites' [a,b,c]
  BYHash _ a        -> idFromRewrites a
  BYAbiE _ a        -> idFromRewrites a
  StringLit {}      -> empty
  WildExp {}        -> empty
  EnvExp {}         -> empty
  IntLit {}         -> empty
  BoolLit {}        -> empty
  where
    idFromRewrites' = unionsWith (<>) . fmap idFromRewrites

-- | True iff the case is a wildcard.
isWild :: Case -> Bool
isWild (Case _ (WildExp _) _) = True
isWild _                      = False
