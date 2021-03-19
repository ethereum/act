{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE FlexibleContexts   #-}

module Utils where

import Control.Natural

class HFunctor (h :: (* -> *) -> * -> *) where
  hfmap :: (f ~> g) -> h f ~> h g

class HFoldable (h :: (* -> *) -> * -> *) where
  hfoldMap :: Monoid m => (forall b. f b -> m) -> h f a -> m

class HFunctor (HBase r) => HRecursive (r :: * -> *) where
  type HBase r :: (* -> *) -> * -> *

  hproject :: r ~> HBase r r

  hcata :: (HBase r f ~> f) -> r ~> f
  hcata alg = alg . hfmap (hcata alg) . hproject