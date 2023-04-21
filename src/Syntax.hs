{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

{-|
Module      : Syntax
Description : Functions for manipulating and collapsing all our different ASTs.
-}
module Syntax where

import Prelude hiding (LT, GT)

import Data.List
import Data.Map (Map,empty,insertWith,unionsWith,unionWith,singleton)

import Syntax.TimeAgnostic as Agnostic
import qualified Syntax.Annotated as Annotated
import           Syntax.Untyped hiding (Constant,Rewrite)
import qualified Syntax.Untyped as Untyped

-----------------------------------------
-- * Extract from fully refined ASTs * --
-----------------------------------------

-- | Invariant predicates can always be expressed as a single expression.
invExp :: Annotated.InvariantPred -> Annotated.Exp ABoolean
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
      And _ a b   -> go a <> go b
      Or _ a b    -> go a <> go b
      Impl _ a b  -> go a <> go b
      Eq _ _ a b    -> go a <> go b
      LT _ a b    -> go a <> go b
      LEQ _ a b   -> go a <> go b
      GT _ a b    -> go a <> go b
      GEQ _ a b   -> go a <> go b
      NEq _ _ a b   -> go a <> go b
      Neg _ a     -> go a
      Add _ a b   -> go a <> go b
      Sub _ a b   -> go a <> go b
      Mul _ a b   -> go a <> go b
      Div _ a b   -> go a <> go b
      Mod _ a b   -> go a <> go b
      Exp _ a b   -> go a <> go b
      Cat _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      IntMin {}  -> []
      IntMax {}  -> []
      UIntMin {} -> []
      UIntMax {} -> []
      LitBool {} -> []
      IntEnv {} -> []
      ByEnv {} -> []
      Create _ _ _ es -> concatMap locsFromTypedExp es
      ITE _ x y z -> go x <> go y <> go z
      TEntry _ _ a -> locsFromItem a
      Var {} -> []

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
      And   _ a b   -> go a <> go b
      Or    _ a b   -> go a <> go b
      Impl  _ a b   -> go a <> go b
      Eq    _ _ a b   -> go a <> go b
      LT    _ a b   -> go a <> go b
      LEQ   _ a b   -> go a <> go b
      GT    _ a b   -> go a <> go b
      GEQ   _ a b   -> go a <> go b
      NEq   _ _ a b   -> go a <> go b
      Neg   _ a     -> go a
      Add   _ a b   -> go a <> go b
      Sub   _ a b   -> go a <> go b
      Mul   _ a b   -> go a <> go b
      Div   _ a b   -> go a <> go b
      Mod   _ a b   -> go a <> go b
      Exp   _ a b   -> go a <> go b
      Cat   _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ITE   _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      LitBool {} -> []
      IntMin {} -> []
      IntMax {} -> []
      UIntMin {} -> []
      UIntMax {} -> []
      IntEnv _ a -> [a]
      ByEnv _ a -> [a]
      Create _ _ _ ixs -> concatMap ethEnvFromTypedExp ixs
      TEntry _ _ a -> ethEnvFromItem a
      Var {} -> []

idFromRewrite :: Rewrite t -> Id
idFromRewrite = onRewrite idFromLocation idFromUpdate

idFromItem :: TStorageItem a t -> Id
idFromItem (Item _ _ ref) = idFromStorageRef ref

idFromStorageRef :: StorageRef t -> Id
idFromStorageRef (SVar _ _ x) = x
idFromStorageRef (SMapping _ e _) = idFromStorageRef e
idFromStorageRef (SField _ e _) = idFromStorageRef e

idFromUpdate :: StorageUpdate t -> Id
idFromUpdate (Update _ item _) = idFromItem item

idFromLocation :: StorageLocation t -> Id
idFromLocation (Loc _ item) = idFromItem item

contractFromRewrite :: Rewrite t -> Id
contractFromRewrite = onRewrite contractFromLoc contractFromUpdate

contractFromItem :: TStorageItem a t -> Id
contractFromItem (Item _ _ ref) = contractFromStorageRef ref

contractFromStorageRef :: StorageRef t -> Id
contractFromStorageRef (SVar _ c _) = c
contractFromStorageRef (SMapping _ e _) = contractFromStorageRef e
contractFromStorageRef (SField _ e _) = contractFromStorageRef e

ixsFromItem :: TStorageItem a t -> [TypedExp t]
ixsFromItem (Item _ _ (SMapping _ _ ixs)) = ixs
ixsFromItem _ = []

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

itemType :: TStorageItem a t -> ActType
itemType (Item t _ _) = actType t

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
nameFromStorage (Untyped.Rewrite e _) = nameFromEntry e
nameFromStorage (Untyped.Constant e) = nameFromEntry e

nameFromEntry :: Entry -> Id
nameFromEntry (EVar _ x) = x
nameFromEntry (EMapping _ e _) = nameFromEntry e
nameFromEntry (EField _ e _) = nameFromEntry e

getPosEntry :: Entry -> Pn
getPosEntry (EVar pn _) = pn
getPosEntry (EMapping pn _ _) = pn
getPosEntry (EField pn _ _) = pn

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
    ECreate pn _ _ -> pn
    EUTEntry e -> getPosEntry e
    EPreEntry e -> getPosEntry e
    EPostEntry e -> getPosEntry e
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
  EUTEntry en       -> idFromEntry en
  EPreEntry en      -> idFromEntry en
  EPostEntry en     -> idFromEntry en
  ECreate p x es      -> insertWith (<>) x [p] $ idFromRewrites' es
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

    idFromEntry :: Entry -> Map Id [Pn]
    idFromEntry (EVar p x) = singleton x [p]
    idFromEntry (EMapping _ en xs) = unionWith (<>) (idFromEntry en) (idFromRewrites' xs)
    idFromEntry (EField _ en _) = idFromEntry en
    
-- | True iff the case is a wildcard.
isWild :: Case -> Bool
isWild (Case _ (WildExp _) _) = True
isWild _                      = False
