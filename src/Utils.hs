{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils where

import Control.Natural
import Data.Functor.Const
import Data.Monoid (Endo(..))

class HFunctor (h :: (* -> *) -> * -> *) where
  hfmap :: (f ~> g) -> h f ~> h g

class HFoldable (h :: (* -> *) -> * -> *) where
  hfoldMap :: Monoid m => (forall b. f b -> m) -> h f a -> m

  hfoldr :: (forall a. f a -> b -> b) -> b -> h f a -> b
  hfoldr f z h = appEndo (hfoldMap (Endo . f) h) z

  recurse :: Monoid m => h (Const m) a -> m
  recurse = hfoldMap getConst

class HFunctor (HBase t) => HRecursive (t :: * -> *) where
  type HBase t :: (* -> *) -> * -> *

  hproject :: t ~> HBase t t

  hcata :: forall f. (HBase t f ~> f) -> t ~> f
  hcata eta = mu
    where
      mu :: t ~> f
      mu = eta . hfmap mu . hproject

  ccata :: (forall a. HBase t (Const b) a -> b) -> t a -> b
  ccata collapse = getConst . hcata (Const . collapse)