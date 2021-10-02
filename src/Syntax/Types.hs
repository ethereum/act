{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase, ScopedTypeVariables, MultiParamTypeClasses, FlexibleContexts #-}

-- These extensions should be removed once we remove the defs at the end of this file.
{-# LANGUAGE RankNTypes, TypeApplications, StandaloneKindSignatures, PolyKinds #-}

{-|
Module      : Syntax.Types
Description : Types that represent Act types, and functions and patterns to go between them and Haskell's own types.
-}

module Syntax.Types (module Syntax.Types) where

import Data.Singletons
import Data.Type.Equality (TestEquality(..))
import Data.Typeable hiding (TypeRep,typeRep)
import Type.Reflection

import Data.ByteString    as Syntax.Types (ByteString)
import EVM.ABI            as Syntax.Types (AbiType(..))

-- | Types understood by proving tools.
data MType
  = Integer
  | Boolean
  | ByteStr
  deriving (Eq, Ord, Show, Read)

-- | Singleton types of the types understood by proving tools.
data SType a where
  SInteger :: SType Integer
  SBoolean :: SType Bool
  SByteStr :: SType ByteString
--deriving instance Show (SType a)
deriving instance Eq (SType a)

instance Show (SType a) where
  show = \case
    SInteger -> "int"
    SBoolean -> "bool"
    SByteStr -> "bytestring"

instance TestEquality SType where
  testEquality t1@STypeable t2@STypeable = eqT

eqS :: forall (a :: *) (b :: *) f t. (SingI a, SingI b, Eq (f a t)) => f a t -> f b t -> Bool
eqS fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

class HasType a t where
  getType :: a -> SType t

  tag :: a -> (SType t, a)
  tag a = (getType a, a)

withSingI2 :: Sing a -> Sing b -> ((SingI a, SingI b) => r) -> r
withSingI2 sa sb r = withSingI sa $ withSingI sb $ r

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

-- | For our purposes, the singleton of a type @a@ is always @'SType' a@.
-- Note that even though there only exist three different 'SType', this does
-- not mean that the type family is partial. It simply means that the resulting
-- type is uninhabited if the argument is neither 'Integer', 'Bool' nor
-- 'ByteString'.
type instance Sing = SType

-- Defines which singleton to retreive when we only have the type, not the
-- actual singleton.
instance SingI Integer    where sing = SInteger
instance SingI Bool       where sing = SBoolean
instance SingI ByteString where sing = SByteStr

-- | This instance allows us to go between 'MType', @'SType' a@ and @a@,
-- with @a :: '*'@.
instance SingKind * where
  -- | We can demote a type variable @a@ to a value of type 'MType'
  type Demote * = MType

  -- | We can go from any singleton type to the corresponding demoted type.
  fromSing SInteger = Integer
  fromSing SBoolean = Boolean
  fromSing SByteStr = ByteStr

  -- | We can go from any demoted type to the corresponding singleton type,
  -- but need to hide its type variable when doing so.
  toSing Integer = SomeSing SInteger
  toSing Boolean = SomeSing SBoolean
  toSing ByteStr = SomeSing SByteStr

-- | Pattern match on an 'EVM.ABI.AbiType' is if it were an 'SType' with a 'Typeable'
-- instance.
pattern FromAbi :: () => Typeable a => SType a -> AbiType
pattern FromAbi t <- (metaType -> FromSing t@STypeable)
{-# COMPLETE FromAbi #-} -- We promise that the pattern covers all cases of AbiType.

-- | Pattern match on an 'MType' is if it were an 'SType' with a 'Typeable' instance.
pattern FromMeta :: () => Typeable a => SType a -> MType
pattern FromMeta t <- FromSing t@STypeable
{-# COMPLETE FromMeta #-} -- We promise that the pattern covers all cases of MType.

-- | Helper pattern to retrieve the 'Typeable' instance of an 'SType'.
pattern STypeable :: () => Typeable a => SType a
pattern STypeable <- (stypeRep -> TypeRep)

-- | Allows us to retrieve the 'TypeRep' of any 'SType', which in turn can be used
-- to retrieve the 'Typeable' instance.
stypeRep :: SType a -> TypeRep a
stypeRep = \case
  SInteger -> typeRep
  SBoolean -> typeRep
  SByteStr -> typeRep

-- Everything below will be added to base 4.17 but for now we need it here.
-- See https://gitlab.haskell.org/ghc/ghc/-/blob/master/libraries/base/Data/Typeable/Internal.hs#L264

-- | A 'TypeableInstance' wraps up a 'Typeable' instance for explicit
-- handling. For internal use: for defining 'TypeRep' pattern.
type TypeableInstance :: forall k. k -> *
data TypeableInstance a where
 TypeableInstance :: Typeable a => TypeableInstance a

-- | Get a reified 'Typeable' instance from an explicit 'TypeRep'.
--
-- For internal use: for defining 'TypeRep' pattern.
typeableInstance :: forall (k :: *) (a :: k). TypeRep a -> TypeableInstance a
typeableInstance rep = withTypeable rep TypeableInstance

-- | A explicitly bidirectional pattern synonym to construct a
-- concrete representation of a type.
--
-- As an __expression__: Constructs a singleton @TypeRep a@ given a
-- implicit 'Typeable a' constraint:
--
-- @
-- TypeRep @a :: Typeable a => TypeRep a
-- @
--
-- As a __pattern__: Matches on an explicit @TypeRep a@ witness bringing
-- an implicit @Typeable a@ constraint into scope.
--
-- @
-- f :: TypeRep a -> ..
-- f TypeRep = {- Typeable a in scope -}
-- @
--
-- @since 4.17.0.0
pattern TypeRep :: forall (k :: *) (a :: k). () => Typeable @k a => TypeRep @k a
pattern TypeRep <- (typeableInstance -> TypeableInstance)
  where TypeRep = typeRep
