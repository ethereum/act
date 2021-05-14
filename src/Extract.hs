{-# LANGUAGE GADTs #-}

module Extract where

import qualified Data.List.NonEmpty as NonEmpty
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

locsFromReturnExp :: ReturnExp -> [StorageLocation]
locsFromReturnExp (ExpInt e) = locsFromExp e
locsFromReturnExp (ExpBool e) = locsFromExp e
locsFromReturnExp (ExpBytes e) = locsFromExp e

locsFromExp :: Exp a -> [StorageLocation]
locsFromExp = nub . go
  where
    go :: Exp a -> [StorageLocation]
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
      TEntry a -> case a of
        DirectInt contract name -> [IntLoc $ DirectInt contract name]
        DirectBool contract slot -> [BoolLoc $ DirectBool contract slot]
        DirectBytes contract slot -> [BytesLoc $ DirectBytes contract slot]
        MappedInt contract name ixs -> [IntLoc $ MappedInt contract name ixs] <> ixLocs ixs
        MappedBool contract name ixs -> [BoolLoc $ MappedBool contract name ixs] <> ixLocs ixs
        MappedBytes contract name ixs -> [BytesLoc $ MappedBytes contract name ixs] <> ixLocs ixs
        where
          ixLocs :: NonEmpty.NonEmpty ReturnExp -> [StorageLocation]
          ixLocs = concatMap locsFromReturnExp

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

ethEnvFromItem :: TStorageItem a -> [EthEnv]
ethEnvFromItem item = nub $ case item of
  MappedInt _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  MappedBool _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  MappedBytes _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  _ -> []

ethEnvFromReturnExp :: ReturnExp -> [EthEnv]
ethEnvFromReturnExp (ExpInt e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBool e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBytes e) = ethEnvFromExp e

ethEnvFromExp :: Exp a -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp a -> [EthEnv]
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
      TEntry a  -> ethEnvFromItem a

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
getId (Right (IntUpdate a _)) = getId' a
getId (Right (BoolUpdate a _)) = getId' a
getId (Right (BytesUpdate a _)) = getId' a
getId (Left (IntLoc a)) = getId' a
getId (Left (BoolLoc a)) = getId' a
getId (Left (BytesLoc a)) = getId' a

getId' :: TStorageItem a -> Id
getId' (DirectInt _ name) = name
getId' (DirectBool _ name) = name
getId' (DirectBytes _ name) = name
getId' (MappedInt _ name _) = name
getId' (MappedBool _ name _) = name
getId' (MappedBytes _ name _) = name

getContract :: Either StorageLocation StorageUpdate -> Id
getContract (Left (IntLoc item)) = getContract' item
getContract (Left (BoolLoc item)) = getContract' item
getContract (Left (BytesLoc item)) = getContract' item
getContract (Right (IntUpdate item _)) = getContract' item
getContract (Right (BoolUpdate item _)) = getContract' item
getContract (Right (BytesUpdate item _)) = getContract' item

getContract' :: TStorageItem a -> Id
getContract' (DirectInt c _) = c
getContract' (DirectBool c _) = c
getContract' (DirectBytes c _) = c
getContract' (MappedInt c _ _) = c
getContract' (MappedBool c _ _) = c
getContract' (MappedBytes c _ _) = c

contractsInvolved :: Behaviour -> [Id]
contractsInvolved beh =
  getContractId . getLoc <$> _stateUpdates beh

getContractId :: StorageLocation -> Id
getContractId (IntLoc (DirectInt a _)) = a
getContractId (BoolLoc (DirectBool a _)) = a
getContractId (BytesLoc (DirectBytes a _)) = a
getContractId (IntLoc (MappedInt a _ _)) = a
getContractId (BoolLoc (MappedBool a _ _)) = a
getContractId (BytesLoc (MappedBytes a _ _)) = a

getContainerId :: StorageLocation -> Id
getContainerId (IntLoc (DirectInt _ a)) = a
getContainerId (BoolLoc (DirectBool _ a)) = a
getContainerId (BytesLoc (DirectBytes _ a)) = a
getContainerId (IntLoc (MappedInt _ a _)) = a
getContainerId (BoolLoc (MappedBool _ a _)) = a
getContainerId (BytesLoc (MappedBytes _ a _)) = a

getContainerIxs :: StorageLocation -> [ReturnExp]
getContainerIxs (IntLoc (DirectInt _ _)) = []
getContainerIxs (BoolLoc (DirectBool _ _)) = []
getContainerIxs (BytesLoc (DirectBytes _ _)) = []
getContainerIxs (IntLoc (MappedInt _ _ ixs)) = NonEmpty.toList ixs
getContainerIxs (BoolLoc (MappedBool _ _ ixs)) = NonEmpty.toList ixs
getContainerIxs (BytesLoc (MappedBytes _ _ ixs)) = NonEmpty.toList ixs

isMapping :: StorageLocation -> Bool
isMapping loc = case loc of
  (IntLoc (MappedInt {})) -> True
  (BoolLoc (MappedBool {})) -> True
  (BytesLoc (MappedBytes {})) -> True
  _ -> False
