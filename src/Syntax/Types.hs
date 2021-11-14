{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- These extensions should be removed once we remove the defs at the end of this file.
{-# LANGUAGE RankNTypes, TypeApplications, StandaloneKindSignatures, PolyKinds #-}

{-|
Module      : Syntax.Types
Description : Types that represent Act types, and functions and patterns to go between them and Haskell's own types.
-}

module Syntax.Types (module Syntax.Types) where

import Data.Singletons
import Data.Tuple.Extra (dupe)
import Data.Type.Equality (TestEquality(..))
import Data.Typeable hiding (TypeRep,typeRep)
import Type.Reflection

import Data.ByteString    as Syntax.Types (ByteString)
import EVM.ABI            as Syntax.Types (AbiType(..))

-- | Singleton types of the types understood by proving tools.
data SType a where
  SInteger :: SType Integer
  SBoolean :: SType Bool
  SByteStr :: SType ByteString
deriving instance Eq (SType a)

instance Show (SType a) where
  show = \case
    SInteger -> "int"
    SBoolean -> "bool"
    SByteStr -> "bytestring"

instance TestEquality SType where
  testEquality SType SType = eqT

-- | Compare equality of two things parametrized by types which have singletons.
eqS :: forall (a :: *) (b :: *) f t. (SingI a, SingI b, Eq (f a t)) => f a t -> f b t -> Bool
eqS fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | For our purposes, the singleton of a type @a@ is always @'SType' a@.
-- We need this to be able to use 'SomeSing' when implementing 'ActType'.

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

-- | A non-indexed type whose inhabitants represent the types understood
-- by proving tools. Implemented by an existentially quantified 'SType'.
type ActType = SomeSing *

pattern Integer :: ActType
pattern Integer = SomeSing SInteger

pattern Boolean :: ActType
pattern Boolean = SomeSing SBoolean

pattern ByteStr :: ActType
pattern ByteStr = SomeSing SByteStr

{-# COMPLETE Integer, Boolean, ByteStr #-}

class HasType a t where
  getType :: a -> SType t

actType :: AbiType -> ActType
actType (AbiUIntType _)     = Integer
actType (AbiIntType  _)     = Integer
actType AbiAddressType      = Integer
actType AbiBoolType         = Boolean
actType (AbiBytesType n)    = if n <= 32 then Integer else ByteStr
actType AbiBytesDynamicType = ByteStr
actType AbiStringType       = ByteStr
--actType (AbiArrayDynamicType a) =
--actType (AbiArrayType        Int AbiType
--actType (AbiTupleType        (Vector AbiType)
actType _ = error "Syntax.Types.actType: TODO"

-- | Pattern match on an 'EVM.ABI.AbiType' is if it were an 'SType'.
pattern FromAbi :: () => (SingI a, Typeable a) => SType a -> AbiType
pattern FromAbi t <- (actType -> FromAct t)
{-# COMPLETE FromAbi #-} -- We promise that the pattern covers all cases of AbiType.

-- | Pattern match on an 'ActType' is if it were an 'SType'.
pattern FromAct :: () => (SingI a, Typeable a) => SType a -> ActType
pattern FromAct t <- SomeSing t@SType
{-# COMPLETE FromAct #-}

-- | Helper pattern to retrieve the 'Typeable' and 'SingI' instances of the type
-- represented by an 'SType'.
pattern SType :: () => (SingI a, Typeable a) => SType a
pattern SType <- (dupe -> (Sing, stypeRep -> TypeRep))
{-# COMPLETE SType #-}

-- | Allows us to retrieve the 'TypeRep' of any 'SType', which in turn can be used
-- to retrieve the 'Typeable' instance.
stypeRep :: SType a -> TypeRep a
stypeRep = \case
  SInteger -> typeRep
  SBoolean -> typeRep
  SByteStr -> typeRep

-- Everything below will be added to base 4.17 but for now we need it here.
-- See https://gitlab.haskell.org/ghc/ghc/-/commit/d3ef2dc2bdfec457d5e0973f3e8f3e92767c16af#786588e27bcbc2a8360d2d0d3b2ce1d075797ffb_232_263

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
