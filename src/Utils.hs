{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE PatternSynonyms      #-}

module Utils where

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Projection
import Data.Comp.Multi.Term
import Data.Comp.Ops

(<$$>) :: (a -> b) -> K a x -> K b x
f <$$> (K a) = K (f a)

(<**>) :: K (a -> b) x -> K a y -> K b z
(K f) <**> (K a) = K $ f a

cataK :: HFunctor f => (forall a. f (K k) a -> k) -> Term f a -> k
cataK f = unK . (cata $ K . f)

recurse :: (HFoldable h, Monoid m) => h (K m) a -> m
recurse = hfoldMap unK

zygo :: forall f a b. HFunctor f => Alg f b -> f (b :*: a) :-> a -> Term f :-> a
zygo f g = fsnd . cata h
  where
    h :: f (b :*: a) :-> b :*: a
    h term = f (hfmap ffst term) :*: g term

zygoK
  :: HFunctor f
  => (forall x. f (K b) x -> b)
  -> (forall x. f (K (b,a)) x -> a)
  -> Term f x
  -> a
zygoK f g = unK . zygo (K . f) (K . g . hfmap lowerTuple)

lowerTuple :: K x :*: K y :-> K (x,y)
lowerTuple (x:*:y) = K (unK x, unK y)

pattern Fst  a   <- K (a,_)
pattern Snd  b   <- K (_,b)
pattern Pair a b <- K (a,b)