{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

{-|
Module      : Syntax
Description : Functions for manipulating and collapsing all our different ASTs.
-}
module Syntax where

import Data.List
import Data.Map (Map,empty,insertWith,unionsWith)

import EVM.ABI (AbiType(..))

import Syntax.TimeAgnostic as Agnostic
import qualified Syntax.Annotated as Annotated
import           Syntax.Untyped hiding (Constant,Rewrite)
import qualified Syntax.Untyped as Untyped

-----------------------------------------
-- * Extract from fully refined ASTs * --
-----------------------------------------

stripTimeTyped :: Annotated.TypedExp -> Agnostic.TypedExp Untimed
stripTimeTyped (ExpInt e) = ExpInt (stripTime e)
stripTimeTyped (ExpBool e) = ExpBool (stripTime e)
stripTimeTyped (ExpBytes e) = ExpBytes (stripTime e)

-- | Strip timing from an annotated expression, sometimes useful for display in the ui
stripTime :: Annotated.Exp a -> Agnostic.Exp a Untimed
stripTime e = case e of
  And a b   -> And (stripTime a) (stripTime b)
  Or a b    -> Or (stripTime a) (stripTime b)
  Impl a b    -> Impl (stripTime a) (stripTime b)
  Eq a b    -> Eq (stripTime a) (stripTime b)
  LE a b    -> LE (stripTime a) (stripTime b)
  LEQ a b    -> LEQ (stripTime a) (stripTime b)
  GE a b    -> GE (stripTime a) (stripTime b)
  GEQ a b    -> GEQ (stripTime a) (stripTime b)
  NEq a b    -> NEq (stripTime a) (stripTime b)
  Neg a  -> Neg (stripTime a)
  Add a b    -> Add (stripTime a) (stripTime b)
  Sub a b    -> Sub (stripTime a) (stripTime b)
  Mul a b    -> Mul (stripTime a) (stripTime b)
  Div a b    -> Div (stripTime a) (stripTime b)
  Mod a b    -> Mod (stripTime a) (stripTime b)
  Exp a b    -> Exp (stripTime a) (stripTime b)
  Cat a b    -> Cat (stripTime a) (stripTime b)
  Slice a b c    -> Slice (stripTime a) (stripTime b) (stripTime c)
  ByVar a -> ByVar a
  ByStr a -> ByStr a
  ByLit a -> ByLit a
  LitInt a -> LitInt a
  IntMin a -> IntMin a
  IntMax a -> IntMax a
  UIntMin a -> UIntMin a
  UIntMax a -> UIntMax a
  IntVar a -> IntVar a
  LitBool a -> LitBool a
  BoolVar a -> BoolVar a
  IntEnv a -> IntEnv a
  ByEnv a -> ByEnv a
  NewAddr a b -> NewAddr (stripTime a) (stripTime b)
  ITE x y z -> ITE (stripTime x) (stripTime y) (stripTime z)
  TEntry (IntItem a b c) _ -> TEntry (IntItem a b (fmap stripTimeTyped c)) Neither
  TEntry (BoolItem a b c) _ -> TEntry (BoolItem a b (fmap stripTimeTyped c)) Neither
  TEntry (BytesItem a b c) _ -> TEntry (BytesItem a b (fmap stripTimeTyped c)) Neither

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

locsFromRewrite :: Rewrite t -> [StorageLocation t]
locsFromRewrite update = nub $ case update of
  Constant loc -> [loc]
  Rewrite (IntUpdate   item e) -> locsFromItem item <> locsFromExp e
  Rewrite (BoolUpdate  item e) -> locsFromItem item <> locsFromExp e
  Rewrite (BytesUpdate item e) -> locsFromItem item <> locsFromExp e

locFromRewrite :: Rewrite t -> StorageLocation t
locFromRewrite = onRewrite id locFromUpdate

locFromUpdate :: StorageUpdate t -> StorageLocation t
locFromUpdate (IntUpdate   item _) = IntLoc item
locFromUpdate (BoolUpdate  item _) = BoolLoc item
locFromUpdate (BytesUpdate item _) = BytesLoc item

locsFromItem :: TStorageItem a t -> [StorageLocation t]
locsFromItem t = case t of
  IntItem   contract name ixs -> IntLoc   (IntItem   contract name ixs) : ixLocs ixs
  BoolItem  contract name ixs -> BoolLoc  (BoolItem  contract name ixs) : ixLocs ixs
  BytesItem contract name ixs -> BytesLoc (BytesItem contract name ixs) : ixLocs ixs
  where
    ixLocs :: [TypedExp t] -> [StorageLocation t]
    ixLocs = concatMap locsFromTypedExp

locsFromTypedExp :: TypedExp t -> [StorageLocation t]
locsFromTypedExp (ExpInt e) = locsFromExp e
locsFromTypedExp (ExpBool e) = locsFromExp e
locsFromTypedExp (ExpBytes e) = locsFromExp e

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
      ByVar _ -> []
      ByStr _ -> []
      ByLit _ -> []
      LitInt _  -> []
      IntMin _  -> []
      IntMax _  -> []
      UIntMin _ -> []
      UIntMax _ -> []
      IntVar _  -> []
      LitBool _ -> []
      BoolVar _ -> []
      NewAddr a b -> go a <> go b
      IntEnv _ -> []
      ByEnv _ -> []
      ITE x y z -> go x <> go y <> go z
      TEntry a _ -> locsFromItem a

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
  Constant (IntLoc item) -> ethEnvFromItem item
  Constant (BoolLoc item) -> ethEnvFromItem item
  Constant (BytesLoc item) -> ethEnvFromItem item
  Rewrite (IntUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
  Rewrite (BoolUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
  Rewrite (BytesUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TStorageItem a t -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromItem

ethEnvFromTypedExp :: TypedExp t -> [EthEnv]
ethEnvFromTypedExp (ExpInt e) = ethEnvFromExp e
ethEnvFromTypedExp (ExpBool e) = ethEnvFromExp e
ethEnvFromTypedExp (ExpBytes e) = ethEnvFromExp e

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
      ByVar _ -> []
      ByStr _ -> []
      ByLit _ -> []
      LitInt _  -> []
      IntVar _  -> []
      LitBool _ -> []
      BoolVar _ -> []
      IntMin _ -> []
      IntMax _ -> []
      UIntMin _ -> []
      UIntMax _ -> []
      NewAddr a b -> go a <> go b
      IntEnv a -> [a]
      ByEnv a -> [a]
      TEntry a _ -> ethEnvFromItem a

metaType :: AbiType -> MType
metaType (AbiUIntType _)     = Integer
metaType (AbiIntType  _)     = Integer
metaType AbiAddressType      = Integer
metaType AbiBoolType         = Boolean
metaType (AbiBytesType n)    = if n <= 32 then Integer else ByteStr
metaType AbiBytesDynamicType = ByteStr
metaType AbiStringType       = ByteStr
--metaType (AbiArrayDynamicType a) =
--metaType (AbiArrayType        Int AbiType
--metaType (AbiTupleType        (Vector AbiType)
metaType _ = error "Extract.metaType: TODO"

idFromRewrite :: Rewrite t -> Id
idFromRewrite = onRewrite idFromLocation idFromUpdate

idFromItem :: TStorageItem a t -> Id
idFromItem (IntItem _ name _) = name
idFromItem (BoolItem _ name _) = name
idFromItem (BytesItem _ name _) = name

idFromUpdate :: StorageUpdate t -> Id
idFromUpdate (IntUpdate   item _) = idFromItem item
idFromUpdate (BoolUpdate  item _) = idFromItem item
idFromUpdate (BytesUpdate item _) = idFromItem item

idFromLocation :: StorageLocation t -> Id
idFromLocation (IntLoc   item) = idFromItem item
idFromLocation (BoolLoc  item) = idFromItem item
idFromLocation (BytesLoc item) = idFromItem item

contractFromRewrite :: Rewrite t -> Id
contractFromRewrite = onRewrite contractFromLoc contractFromUpdate

contractFromItem :: TStorageItem a t -> Id
contractFromItem (IntItem   c _ _) = c
contractFromItem (BoolItem  c _ _) = c
contractFromItem (BytesItem c _ _) = c

ixsFromItem :: TStorageItem a t -> [TypedExp t]
ixsFromItem (IntItem   _ _ ixs) = ixs
ixsFromItem (BoolItem  _ _ ixs) = ixs
ixsFromItem (BytesItem _ _ ixs) = ixs

contractsInvolved :: Behaviour t -> [Id]
contractsInvolved = fmap contractFromRewrite . _stateUpdates

contractFromLoc :: StorageLocation t -> Id
contractFromLoc (IntLoc   item) = contractFromItem item
contractFromLoc (BoolLoc  item) = contractFromItem item
contractFromLoc (BytesLoc item) = contractFromItem item

contractFromUpdate :: StorageUpdate t -> Id
contractFromUpdate (IntUpdate   item _) = contractFromItem item
contractFromUpdate (BoolUpdate  item _) = contractFromItem item
contractFromUpdate (BytesUpdate item _) = contractFromItem item

ixsFromLocation :: StorageLocation t -> [TypedExp t]
ixsFromLocation (IntLoc item) = ixsFromItem item
ixsFromLocation (BoolLoc item) = ixsFromItem item
ixsFromLocation (BytesLoc item) = ixsFromItem item

ixsFromUpdate :: StorageUpdate t -> [TypedExp t]
ixsFromUpdate (IntUpdate   item _) = ixsFromItem item
ixsFromUpdate (BoolUpdate  item _) = ixsFromItem item
ixsFromUpdate (BytesUpdate item _) = ixsFromItem item

ixsFromRewrite :: Rewrite t -> [TypedExp t]
ixsFromRewrite = onRewrite ixsFromLocation ixsFromUpdate

itemType :: TStorageItem a t -> MType
itemType IntItem{}   = Integer
itemType BoolItem{}  = Boolean
itemType BytesItem{} = ByteStr

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
