{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Extract where

import Data.List

import RefinedAst
import Syntax
import EVM.ABI (AbiType(..))

locsFromBehaviour :: Behaviour -> [StorageLocation]
locsFromBehaviour (Behaviour _ _ _ _ preconds postconds stateUpdates returns) = nub $
  concatMap locsFromExp preconds
  <> concatMap locsFromExp postconds
  <> concatMap locsFromStateUpdate stateUpdates
  <> maybe [] locsFromReturnExp returns

locsFromConstructor :: Constructor -> [StorageLocation]
locsFromConstructor (Constructor _ _ _ pre post initialStorage stateUpdates) = nub $
  concatMap locsFromExp pre
  <> concatMap locsFromExp post
  <> concatMap locsFromStateUpdate stateUpdates
  <> concatMap locsFromStateUpdate (Right <$> initialStorage)

locsFromStateUpdate :: Either StorageLocation StorageUpdate -> [StorageLocation]
locsFromStateUpdate update = nub $ case update of
  Left loc -> [loc]
  Right (IntUpdate item e) -> IntLoc item : locsFromExp e
  Right (BoolUpdate item e) -> BoolLoc item : locsFromExp e
  Right (BytesUpdate item e) -> BytesLoc item : locsFromExp e

locsFromReturnExp :: TypedExp t -> [StorageLocation]
locsFromReturnExp (ExpInt e) = locsFromExp e
locsFromReturnExp (ExpBool e) = locsFromExp e
locsFromReturnExp (ExpBytes e) = locsFromExp e

locsFromExp :: Exp t a -> [StorageLocation]
locsFromExp = nub . go
  where
    go :: Exp t a -> [StorageLocation]
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
      TEntry a _ -> locsFromStorageItem a

    locsFromStorageItem :: TStorageItem t a -> [StorageLocation]
    locsFromStorageItem t = case t of
      IntItem contract name ixs -> [IntLoc $ IntItem contract name $ untimeTyped <$> ixs] <> ixLocs ixs
      BoolItem contract name ixs -> [BoolLoc $ BoolItem contract name $ untimeTyped <$> ixs] <> ixLocs ixs
      BytesItem contract name ixs -> [BytesLoc $ BytesItem contract name $ untimeTyped <$> ixs] <> ixLocs ixs
      where
        ixLocs :: [TypedExp t] -> [StorageLocation]
        ixLocs = concatMap (locsFromReturnExp . untimeTyped)

        untimeTyped :: TypedExp t -> TypedExp Untimed
        untimeTyped (ExpInt   e) = ExpInt   $ forceTime Neither e
        untimeTyped (ExpBool  e) = ExpBool  $ forceTime Neither e
        untimeTyped (ExpBytes e) = ExpBytes $ forceTime Neither e

ethEnvFromBehaviour :: Behaviour -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds postconds stateUpdates returns) = nub $
  concatMap ethEnvFromExp preconds
  <> concatMap ethEnvFromExp postconds
  <> concatMap ethEnvFromStateUpdate stateUpdates
  <> maybe [] ethEnvFromReturnExp returns

ethEnvFromConstructor :: Constructor -> [EthEnv]
ethEnvFromConstructor (Constructor _ _ _ pre post initialStorage stateUpdates) = nub $
  concatMap ethEnvFromExp pre
  <> concatMap ethEnvFromExp post
  <> concatMap ethEnvFromStateUpdate stateUpdates
  <> concatMap ethEnvFromStateUpdate (Right <$> initialStorage)

ethEnvFromStateUpdate :: Either StorageLocation StorageUpdate -> [EthEnv]
ethEnvFromStateUpdate update = case update of
  Left (IntLoc item) -> ethEnvFromItem item
  Left (BoolLoc item) -> ethEnvFromItem item
  Left (BytesLoc item) -> ethEnvFromItem item
  Right (IntUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
  Right (BoolUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
  Right (BytesUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TStorageItem t a -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromReturnExp . getItemIxs

ethEnvFromReturnExp :: TypedExp t -> [EthEnv]
ethEnvFromReturnExp (ExpInt e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBool e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBytes e) = ethEnvFromExp e

ethEnvFromExp :: Exp t a -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp t a -> [EthEnv]
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

getLoc :: Either StorageLocation StorageUpdate -> StorageLocation
getLoc = either id mkLoc

mkLoc :: StorageUpdate -> StorageLocation
mkLoc (IntUpdate item _) = IntLoc item
mkLoc (BoolUpdate item _) = BoolLoc item
mkLoc (BytesUpdate item _) = BytesLoc item

metaType :: AbiType -> MType
metaType (AbiUIntType _)     = Integer
metaType (AbiIntType  _)     = Integer
metaType AbiAddressType      = Integer
metaType AbiBoolType         = Boolean
metaType (AbiBytesType _)    = ByteStr
metaType AbiBytesDynamicType = ByteStr
metaType AbiStringType       = ByteStr
--metaType (AbiArrayDynamicType a) =
--metaType (AbiArrayType        Int AbiType
--metaType (AbiTupleType        (Vector AbiType)
metaType _ = error "Extract.metaType: TODO"

nameFromStorage :: Syntax.Storage -> Id
nameFromStorage (Rewrite (PEntry _ x _) _) = x
nameFromStorage (Constant (PEntry _ x _)) = x
nameFromStorage store = error $ "Internal error: cannot extract name from " ++ show store


getId :: Either StorageLocation StorageUpdate -> Id
getId = either getLocationId getUpdateId

getId' :: TStorageItem t a -> Id
getId' (IntItem _ name _) = name
getId' (BoolItem _ name _) = name
getId' (BytesItem _ name _) = name

getUpdateId :: StorageUpdate -> Id
getUpdateId (IntUpdate   item _) = getId' item
getUpdateId (BoolUpdate  item _) = getId' item
getUpdateId (BytesUpdate item _) = getId' item

getLocationId :: StorageLocation -> Id
getLocationId (IntLoc   item) = getId' item
getLocationId (BoolLoc  item) = getId' item
getLocationId (BytesLoc item) = getId' item

getContract :: Either StorageLocation StorageUpdate -> Id
getContract = either getLocationContract getUpdateContract

getContract' :: TStorageItem t a -> Id
getContract' (IntItem c _ _) = c
getContract' (BoolItem c _ _) = c
getContract' (BytesItem c _ _) = c

getItemIxs :: TStorageItem t a -> [TypedExp t]
getItemIxs (IntItem   _ _ ixs) = ixs
getItemIxs (BoolItem  _ _ ixs) = ixs
getItemIxs (BytesItem _ _ ixs) = ixs

contractsInvolved :: Behaviour -> [Id]
contractsInvolved = fmap getContract . _stateUpdates

getLocationContract :: StorageLocation -> Id
getLocationContract (IntLoc item) = getContract' item
getLocationContract (BoolLoc item) = getContract' item
getLocationContract (BytesLoc item) = getContract' item

getUpdateContract :: StorageUpdate -> Id
getUpdateContract (IntUpdate item _) = getContract' item
getUpdateContract (BoolUpdate item _) = getContract' item
getUpdateContract (BytesUpdate item _) = getContract' item

getContainerId :: StorageLocation -> Id
getContainerId (IntLoc item) = getId' item
getContainerId (BoolLoc item) = getId' item
getContainerId (BytesLoc item) = getId' item

getContainerIxs :: StorageLocation -> [TypedExp Untimed]
getContainerIxs (IntLoc item) = getItemIxs item
getContainerIxs (BoolLoc item) = getItemIxs item
getContainerIxs (BytesLoc item) = getItemIxs item

getUpdateIxs :: StorageUpdate -> [TypedExp Untimed]
getUpdateIxs (IntUpdate item _) = getItemIxs item
getUpdateIxs (BoolUpdate item _) = getItemIxs item
getUpdateIxs (BytesUpdate item _) = getItemIxs item

getIxs :: Either StorageLocation StorageUpdate -> [TypedExp Untimed]
getIxs = either getContainerIxs getUpdateIxs

getItemType :: TStorageItem t a -> MType
getItemType IntItem{}   = Integer
getItemType BoolItem{}  = Boolean
getItemType BytesItem{} = ByteStr

isMapping :: StorageLocation -> Bool
isMapping = not . null . getContainerIxs
