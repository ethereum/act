{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Util where

import Data.Kind (Type, Constraint)

import Data.Parameterized.List (List(..))

-- | Applies the constraint `c` to each type in the list `ts`
type family All (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
  All c '[] = ()
  All c (t ': ts) = (c t, All c ts)

-- | Converts a paramterized list type into a nested tuple type
type family Tuple (f :: Type -> Type) (l :: [ts]) :: Type where
  Tuple _ '[] = ()
  Tuple f (hd ': tl) = (f hd, Tuple f tl)

-- | Converts a parameterized list into a nested tuple
tuple :: List f ts -> Tuple f ts
tuple Nil = ()
tuple (hd :< tl) = (hd, tuple tl)

-- | Applies the given function to each element in the parameterized list and
-- concats the results into a normal haskell list
concatMapFC :: forall (f :: Type -> Type) (ts :: [Type]) (b :: Type)
            . (forall (a :: Type) . f a -> [b]) -> List f ts -> [b]
concatMapFC _ Nil = []
concatMapFC f (hd :< tl) = (f hd) <> (concatMapFC f tl)
