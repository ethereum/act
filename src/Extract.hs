{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE BlockArguments #-}

{-# LANGUAGE TypeOperators, RankNTypes #-}

module Extract where

import qualified Data.List.NonEmpty as NonEmpty

import RefinedAst
import Syntax

import Data.Comp.Multi.Algebra (cata)
import Data.Comp.Multi.HFunctor (K(..))
import Data.Comp.Multi.HFoldable (hfold)
import Data.Comp.Multi.Ops (injectA, projectA, (:&:)(..))
import qualified Data.Comp.Ops as O
import Data.Comp.Multi.Term (Term, unTerm)
import Utils

storageLocations :: TStorageItem a -> [StorageLocation]
storageLocations a = case a of
  DirectInt {} -> [IntLoc a]
  DirectBool {} -> [BoolLoc a]
  DirectBytes {} -> [BytesLoc a]
  MappedInt _ _ ixs -> IntLoc a : ixLocs ixs
  MappedBool _ _ ixs -> BoolLoc a : ixLocs ixs
  MappedBytes _ _ ixs -> BytesLoc a : ixLocs ixs
  where
    ixLocs :: NonEmpty.NonEmpty ReturnExp -> [StorageLocation]
    ixLocs = concatMap locsFromReturnExp

locsFromReturnExp :: ReturnExp -> [StorageLocation]
locsFromReturnExp (ExpInt e) = locsFromExp e
locsFromReturnExp (ExpBool e) = locsFromExp e
locsFromReturnExp (ExpBytes e) = locsFromExp e

locsFromExp :: Exp a -> [StorageLocation]
locsFromExp = cataK \case
  BoolStore t -> storageLocations t
  IntStore t  -> storageLocations t
  ByStore t   -> storageLocations t
  e           -> hfold e

locsFromExp' :: Exp a -> [StorageLocation]
locsFromExp' = unK . cata f
  where
    f :: ExpF (K [StorageLocation]) i -> K [StorageLocation] i
    f = K . \case
      BoolStore t -> storageLocations t
      IntStore t  -> storageLocations t
      ByStore t   -> storageLocations t
      e           -> hfold e

ethEnvFromBehaviour :: Behaviour -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds postconds stateUpdates returns) =
  (concatMap ethEnvFromExp preconds)
  <> (concatMap ethEnvFromExp postconds)
  <> (concatMap ethEnvFromStateUpdate stateUpdates)
  <> (maybe [] ethEnvFromReturnExp returns)

ethEnvFromConstructor :: Constructor -> [EthEnv]
ethEnvFromConstructor (Constructor _ _ _ pre post initialStorage stateUpdates) =
  (concatMap ethEnvFromExp pre)
  <> (concatMap ethEnvFromExp post)
  <> (concatMap ethEnvFromStateUpdate stateUpdates)
  <> (concatMap ethEnvFromStateUpdate (Right <$> initialStorage))

ethEnvFromStateUpdate :: Either StorageLocation StorageUpdate -> [EthEnv]
ethEnvFromStateUpdate update = case update of
  Left (IntLoc item) -> ethEnvFromItem item
  Left (BoolLoc item) -> ethEnvFromItem item
  Left (BytesLoc item) -> ethEnvFromItem item
  Right (IntUpdate item e) -> ethEnvFromItem item <> ethEnvFromExp e
  Right (BoolUpdate item e) -> ethEnvFromItem item <> ethEnvFromExp e
  Right (BytesUpdate item e) -> ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TStorageItem a -> [EthEnv]
ethEnvFromItem item = case item of
  MappedInt _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  MappedBool _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  MappedBytes _ _ ixs -> concatMap ethEnvFromReturnExp ixs
  _ -> []

ethEnvFromReturnExp :: ReturnExp -> [EthEnv]
ethEnvFromReturnExp (ExpInt e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBool e) = ethEnvFromExp e
ethEnvFromReturnExp (ExpBytes e) = ethEnvFromExp e

ethEnvFromExp :: Exp a -> [EthEnv]
ethEnvFromExp = cataK \case
  IntEnv a    -> [a]
  ByEnv a     -> [a]
  BoolStore a -> ethEnvFromItem a
  IntStore a  -> ethEnvFromItem a
  ByStore a   -> ethEnvFromItem a
  e           -> hfold e

getLoc :: Either StorageLocation StorageUpdate -> StorageLocation
getLoc = either id mkLoc

mkLoc :: StorageUpdate -> StorageLocation
mkLoc (IntUpdate item _) = IntLoc item
mkLoc (BoolUpdate item _) = BoolLoc item
mkLoc (BytesUpdate item _) = BytesLoc item

nameFromStorage :: Syntax.Storage -> Id
nameFromStorage (Rewrite (Entry _ name _) _) = name
nameFromStorage (Constant (Entry _ name _)) = name
nameFromStorage store = error $ "Internal error: cannot extract name from " ++ (show store)

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
