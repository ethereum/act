{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes, TypeApplications, PolyKinds #-}

{-|
Module      : Syntax.Types
Description : Types that represent Act types, and functions and patterns to go between them and Haskell's own types.
-}

module Act.Syntax.Types (module Act.Syntax.Types) where

import Data.Singletons
import Data.ByteString
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import EVM.ABI            as Act.Syntax.Types (AbiType(..))

import Act.Syntax.Untyped (ValueType(..))

-- | Types of Act expressions
data ActType
  = AInteger
  | ABoolean
  --  | AArray Nat ActType
  | AByteStr

-- | Singleton runtime witness for Act types. Sometimes we need to examine type
-- tags at runtime. Tagging structures with this type will let us do that.
data SType (a :: ActType) where
  SInteger  :: SType AInteger
  SBoolean  :: SType ABoolean
 -- SArray    :: SNat n -> SType b -> SType (AArray n b)
  SByteStr  :: SType AByteStr
deriving instance Eq (SType a)

instance Show (SType a) where
  show = \case
    SInteger -> "int"
    SBoolean -> "bool"
--    SArray n v -> "array " <> show n <> show v
    SByteStr -> "bytestring"

type instance Sing = SType

instance TestEquality SType where
  testEquality SInteger SInteger = Just Refl
  testEquality SBoolean SBoolean = Just Refl
  testEquality SByteStr SByteStr = Just Refl
  -- testEquality (SArray n1 v1) (SArray n2 v2) = 
  --   case testEquality n1 n2 of
  --     Just Refl ->
  --       case testEquality v1 v2 of
  --         Just Refl -> Just Refl
  --         Nothing -> Nothing
  --     Nothing -> Nothing
  testEquality _ _ = Nothing


-- | Compare equality of two things parametrized by types which have singletons.
eqS :: forall (a :: ActType) (b :: ActType) f t. (SingI a, SingI b, Eq (f a t)) => f a t -> f b t -> Bool
eqS fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | The same but when the higher-kinded type has two type arguments
eqS' :: forall (a :: ActType) (b :: ActType) f t t'. (SingI a, SingI b, Eq (f a t t')) => f a t t' -> f b t t' -> Bool
eqS' fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- Defines which singleton to retrieve when we only have the type, not the
-- actual singleton.
instance SingI 'AInteger where sing = SInteger
instance SingI 'ABoolean where sing = SBoolean
instance SingI 'AByteStr where sing = SByteStr
--instance SingI ('AArray n v) where sing = SArray (natSing :: SNat 0) (sing :: Sing v)

-- | Reflection of an Act type into a haskell type. Used to define the result
-- type of the evaluation function.
type family TypeOf a where
  TypeOf 'AInteger = Integer
  TypeOf 'ABoolean = Bool
--  TypeOf (AArray n v) = Array Int (TypeOf v)
  TypeOf 'AByteStr = ByteString


fromAbiType :: AbiType -> ActType
fromAbiType (AbiUIntType _)     = AInteger
fromAbiType (AbiIntType  _)     = AInteger
fromAbiType AbiAddressType      = AInteger
fromAbiType AbiBoolType         = ABoolean
fromAbiType (AbiBytesType n)    = if n <= 32 then AInteger else AByteStr
fromAbiType AbiBytesDynamicType = AByteStr
fromAbiType AbiStringType       = AByteStr
--fromAbiType (AbiArrayType n v)  = AArray (fromIntegral n) $ fromAbiType v
fromAbiType _ = error "Syntax.Types.actType: TODO"


someType :: ActType -> SomeType
someType AInteger = SomeType SInteger
someType ABoolean = SomeType SBoolean
someType AByteStr = SomeType SByteStr
-- someType (AArray n v) = 
--   case someType v of
--     FromSome sv ->
--       withSomeSNat n $ \sn -> SomeType $ SArray sn sv

actType :: SType s -> ActType
actType SInteger = AInteger
actType SBoolean = ABoolean
actType SByteStr = AByteStr
--actType (SArray n v) = AArray (fromSNat n) (actType v)

fromValueType :: ValueType -> ActType
fromValueType (PrimitiveType t) = fromAbiType t
fromValueType (ContractType _) = AInteger

data SomeType where
  SomeType :: SingI a => SType a -> SomeType

-- | Pattern match on an 'SomeType' is if it were an 'SType'.
pattern FromSome :: () => (SingI a) => SType a -> SomeType
pattern FromSome t <- SomeType t
{-# COMPLETE FromSome #-}

-- | Pattern match on an 'AbiType' is if it were an 'SType'.
pattern FromAbi :: () => (SingI a) => SType a -> AbiType
pattern FromAbi t <- (someType . fromAbiType -> FromSome t)
{-# COMPLETE FromAbi #-}

-- | Pattern match on an 'ActType' is if it were an 'SType'.
pattern FromAct ::() => (SingI a) => SType a -> ActType
pattern FromAct t <- (someType -> FromSome t)
{-# COMPLETE FromAct #-}

-- | Pattern match on an 'ValueType' is if it were an 'SType'.
pattern FromVType :: () => (SingI a) => SType a -> ValueType
pattern FromVType t <- (someType . fromValueType -> FromSome t)
{-# COMPLETE FromVType #-}

-- | Helper pattern to retrieve the 'SingI' instances of the type
-- represented by an 'SType'.
pattern SType :: () => (SingI a) => SType a
pattern SType <- Sing
{-# COMPLETE SType #-}
