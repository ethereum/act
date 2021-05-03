{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE KindSignatures       #-}

module Utils where

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Projection
import Data.Comp.Multi.Term

(<$$>) :: (a -> b) -> K a x -> K b x
f <$$> (K a) = K (f a)

(<**>) :: K (a -> b) x -> K a y -> K b z
(K f) <**> (K a) = K $ f a

(<$*>) :: (a -> b) -> K a x -> b
f <$*> (K a) = f a

type GRAlg f b a = f (b :*: a) :-> a

zygo :: forall f a b. HFunctor f => Alg f b -> GRAlg f b a -> Term f :-> a
zygo f g = fsnd . cata h
  where
    h :: f (b :*: a) :-> b :*: a
    h term = f (hfmap ffst term) :*: g term

hylo :: forall f a b. HFunctor f => Alg f b -> Coalg f a -> a :-> b
hylo f g = f . hfmap (hylo f g) . g

cataK :: HFunctor f => (f (K k) :=> k) -> Term f :=> k
cataK f = unK . (cata $ K . f)

paraK :: HFunctor f => f (Term f :*: K a) :=> a -> Term f :=> a
paraK f = unK . (para $ K . f)

zygoK
  :: HFunctor f
  => (f (K b) :=> b)
  -> (f (K (b,a)) :=> a)
  -> Term f :=> a
zygoK f g = unK . zygo (K . f) (K . g . hfmap lowerTuple)

lowerTuple :: K x :*: K y :-> K (x,y)
lowerTuple (x:*:y) = K (unK x, unK y)

pattern Fst :: a -> K (a, b) i
pattern Fst  a   <- K (a,_)

pattern Snd :: b -> K (a, b) i
pattern Snd  b   <- K (_,b)

pattern Both :: a -> b -> K (a, b) i
pattern Both a b <- K (a,b)