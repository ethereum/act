{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase   #-}

module Extract where

import Data.Functor.Const
import qualified Data.List.NonEmpty as NonEmpty

import RefinedAst
import Syntax
import Utils


-- Non-recursive Expression type and necessary instances

data ExpF r t where
  AndF :: r Bool -> r Bool -> ExpF r Bool
  LitBoolF :: Bool -> ExpF r Bool
  EqF :: r a -> r a -> ExpF r Bool
  TEntryF :: TStorageItem t -> ExpF r t

instance HFunctor ExpF where
  hfmap eta = \case
    AndF p q -> AndF (eta p) (eta q)
    LitBoolF p -> LitBoolF p
    EqF x y -> EqF (eta x) (eta y)
    TEntryF t -> TEntryF t

instance HRecursive Exp where
  type HBase Exp = ExpF
  hproject = \case
    And p q -> AndF p q
    LitBool p -> LitBoolF p
    Eq x y -> EqF x y
    TEntry t -> TEntryF t

instance HFoldable ExpF where
  hfoldMap f = \case
    AndF p q -> f p <> f q
    LitBoolF _ -> mempty
    EqF x y -> f x <> f y
    TEntryF _ -> mempty

locsFromExp' :: Exp a -> [StorageLocation]
locsFromExp' = mcata $ \case
  TEntryF t -> storageLocations t
  e         -> recurse e

e0 = And (LitBool False) (And (LitBool True) (LitBool False))
e1 = TEntry (DirectInt "C" "x")
e2 = And (TEntry (DirectBool "C" "x")) (And (LitBool True) (LitBool False))
e3 = And (LitBool False) (And (TEntry (DirectBool "C" "x")) (LitBool False))
e4 = And (LitBool False) (And (TEntry (DirectBool "C" "x")) (TEntry (DirectBool "C" "y")))

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
locsFromExp e = case e of
  And a b   -> (locsFromExp a) <> (locsFromExp b)
  Or a b    -> (locsFromExp a) <> (locsFromExp b)
  Impl a b  -> (locsFromExp a) <> (locsFromExp b)
  Eq a b    -> (locsFromExp a) <> (locsFromExp b)
  LE a b    -> (locsFromExp a) <> (locsFromExp b)
  LEQ a b   -> (locsFromExp a) <> (locsFromExp b)
  GE a b    -> (locsFromExp a) <> (locsFromExp b)
  GEQ a b   -> (locsFromExp a) <> (locsFromExp b)
  NEq a b   -> (locsFromExp a) <> (locsFromExp b)
  Neg a     -> (locsFromExp a)
  Add a b   -> (locsFromExp a) <> (locsFromExp b)
  Sub a b   -> (locsFromExp a) <> (locsFromExp b)
  Mul a b   -> (locsFromExp a) <> (locsFromExp b)
  Div a b   -> (locsFromExp a) <> (locsFromExp b)
  Mod a b   -> (locsFromExp a) <> (locsFromExp b)
  Exp a b   -> (locsFromExp a) <> (locsFromExp b)
  Cat a b   -> (locsFromExp a) <> (locsFromExp b)
  Slice a b c -> (locsFromExp a) <> (locsFromExp b) <> (locsFromExp c)
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
  NewAddr _ _ -> error "TODO: handle new addr in SMT expressions"
  IntEnv _ -> []
  ByEnv _ -> []
  ITE x y z -> (locsFromExp x) <> (locsFromExp y) <> (locsFromExp z)
  TEntry a -> storageLocations a

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
ethEnvFromExp e = case e of
  And a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Or a b    -> ethEnvFromExp a <> ethEnvFromExp b
  Impl a b  -> ethEnvFromExp a <> ethEnvFromExp b
  Eq a b    -> ethEnvFromExp a <> ethEnvFromExp b
  LE a b    -> ethEnvFromExp a <> ethEnvFromExp b
  LEQ a b   -> ethEnvFromExp a <> ethEnvFromExp b
  GE a b    -> ethEnvFromExp a <> ethEnvFromExp b
  GEQ a b   -> ethEnvFromExp a <> ethEnvFromExp b
  NEq a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Neg a     -> ethEnvFromExp a
  Add a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Sub a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Mul a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Div a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Mod a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Exp a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Cat a b   -> ethEnvFromExp a <> ethEnvFromExp b
  Slice a b c -> ethEnvFromExp a <> ethEnvFromExp b <> ethEnvFromExp c
  ITE a b c -> ethEnvFromExp a <> ethEnvFromExp b <> ethEnvFromExp c
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
  NewAddr a b -> ethEnvFromExp a <> ethEnvFromExp b
  IntEnv a -> [a]
  ByEnv a -> [a]
  TEntry a  -> ethEnvFromItem a

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
