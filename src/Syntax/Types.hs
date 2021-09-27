{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms, StandaloneDeriving, TypeFamilies, FlexibleInstances #-}

module Syntax.Types where

import Data.Singletons
import Data.Typeable

import Data.ByteString as Syntax.Types (ByteString)
import EVM.ABI as Syntax.Types (AbiType(..))

--types understood by proving tools
data MType
  = Integer
  | Boolean
  | ByteStr
  deriving (Eq, Ord, Show, Read)

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
metaType _ = error "Syntax.Types.metaType: TODO"

pattern FromAbi :: () => Typeable a => SType a -> AbiType
pattern FromAbi t <- (metaType -> FromSing (STypeable t))
{-# COMPLETE FromAbi #-} -- We promise that the pattern covers all cases of AbiType.

pattern FromMeta :: () => Typeable a => SType a -> MType
pattern FromMeta t <- FromSing (STypeable t)
{-# COMPLETE FromMeta #-} -- We promise that the pattern covers all cases of MType.

data SType a where
  SInteger :: SType Integer
  SBoolean :: SType Bool
  SByteStr :: SType ByteString
deriving instance Show (SType a)
deriving instance Eq (SType a)

data STypeable a where
  STypeable :: Typeable a => SType a -> STypeable a
deriving instance Show (STypeable a)
deriving instance Eq (STypeable a)

type instance Sing = STypeable

instance SingI Integer    where sing = STypeable SInteger
instance SingI Bool       where sing = STypeable SBoolean
instance SingI ByteString where sing = STypeable SByteStr

instance SingKind * where
  type Demote * = MType

  fromSing (STypeable SInteger) = Integer
  fromSing (STypeable SBoolean) = Boolean
  fromSing (STypeable SByteStr) = ByteStr

  toSing Integer = SomeSing (STypeable SInteger)
  toSing Boolean = SomeSing (STypeable SBoolean)
  toSing ByteStr = SomeSing (STypeable SByteStr)
