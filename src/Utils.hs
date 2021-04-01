{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms      #-}

module Utils where

import Control.Comonad
import Control.Natural
import Data.Function (on)
import Data.Functor.Const (Const(..))
import Data.Monoid (Endo(..))
import GHC.Generics ((:*:)(..))

(<$$>) :: (a -> b) -> Const a x -> Const b x
f <$$> (Const a) = Const (f a)

(<**>) :: Const (a -> b) x -> Const a y -> Const b z
(Const f) <**> (Const a) = Const $ f a

(&&&&) :: (f ~> g) -> (f ~> h) -> f ~> (g :*: h)
(&&&&) u v x = u x :*: v x
infixr 3 &&&&

class HFunctor (h :: (* -> *) -> * -> *) where
  hfmap :: (f ~> g) -> h f ~> h g

class HFunctor h => HFoldable (h :: (* -> *) -> * -> *) where
  hfoldMap :: Monoid m => (forall b. f b -> m) -> h f a -> m

  hfoldr :: (forall a. f a -> b -> b) -> b -> h f c -> b
  hfoldr f z h = appEndo (hfoldMap (Endo . f) h) z

  recurse :: Monoid m => h (Const m) a -> m
  recurse = hfoldMap getConst

class HFunctor w => HComonad w where
  hextract    :: w f ~> f
  hduplicate  :: w f ~> w (w f)

instance HFunctor ((:*:) a) where
  hfmap eta (a:*:b) = a :*: eta b

instance HComonad ((:*:) a) where
  hextract     (_:*:b) = b
  hduplicate p@(a:*:_) = a:*:p

type family HBase (t :: * -> *) :: (* -> *) -> * -> *

class HFunctor (HBase t) => HRecursive (t :: * -> *) where
  hproject :: t ~> HBase t t

  hcata :: forall f. HBase t f ~> f -> t ~> f
  hcata eta = mu
    where
      mu :: t ~> f
      mu = eta . hfmap mu . hproject

  ccata :: (forall a. HBase t (Const c) a -> c) -> t b -> c
  ccata collapse = getConst . hcata (Const . collapse)

  hpara :: forall f. HBase t (t :*: f) ~> f -> t ~> f
  hpara eta = mu
    where
      mu :: t ~> f
      mu = eta . hfmap (id &&&& mu) . hproject

  hgfold
    :: forall w f. HComonad w
    => (forall g x. HBase t (w g) ~> w (HBase t g))
    -> HBase t (w f) ~> f
    -> t ~> f
  hgfold k g = g . hextract . c
    where
      c :: t ~> w (HBase t (w f))
      c = k . hfmap (hduplicate . hfmap g . c) . hproject

  hzygo :: HBase t g ~> g -> HBase t (g :*: f) ~> f -> t ~> f
  hzygo eta = hgfold (hdistZygo eta)

  czygo
    :: (forall x. HBase t (Const b)     x -> b)
    -> (forall x. HBase t (Const (b,a)) x -> a)
    -> t x
    -> a
  czygo alg collapse = getConst . hzygo
                                    (Const . alg)
                                    (Const . collapse . hfmap lowerTuple)
    where
      lowerTuple :: Const x :*: Const y ~> Const (x,y)
      lowerTuple (x:*:y) = Const (getConst x, getConst y)

hdistZygo :: HFunctor h => h g ~> g -> h (g :*: f) ~> g :*: h f
hdistZygo eta m = eta (hfmap ffst m) :*: hfmap fsnd m
  where
    ffst (f :*: _) = f
    fsnd (_ :*: f) = f

pattern Fst  a   <- Const (_,a)
pattern Snd  a   <- Const (a,_)
pattern Pair a b <- Const (a,b)

class HFunctor (HBase t) => HCorecursive (t :: * -> *) where
  hembed :: HBase t t ~> t

  hana :: forall f. (f ~> HBase t f) -> f ~> t
  hana eta = mu
    where
      mu :: f ~> t
      mu = hembed . hfmap mu . eta

newtype HFix h a = HFix { unHFix :: h (HFix h) a }

deriving instance Show (h (HFix h) a) => Show (HFix h a)

class HEq (f :: * -> *) where
  heq :: f a -> f a -> Bool

instance HEq (f (HFix f)) => HEq (HFix f) where
  heq = heq `on` unHFix