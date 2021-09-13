{-# LANGUAGE OverloadedLists,TypeOperators, LambdaCase, AllowAmbiguousTypes, TypeApplications, TypeFamilies, DeriveFunctor, ConstraintKinds, UndecidableInstances, FlexibleContexts, FlexibleInstances, RankNTypes, KindSignatures, ApplicativeDo, MultiParamTypeClasses, ScopedTypeVariables, InstanceSigs #-}

module ErrorLogger (module ErrorLogger) where

import Control.Lens as ErrorLogger ((#))
import Control.Monad.Writer hiding (Alt)
import Data.Functor
import Data.Functor.Alt
import Data.List.NonEmpty as NE
import Data.Validation as ErrorLogger
import Data.Proxy
import Data.Reflection
import GHC.Generics

import Syntax.Untyped (Pn)

type Error e = Validation (NonEmpty (Pn,e))

throw :: (Pn,e) -> Error e a
throw msg = _Failure # [msg]

notAtPosn :: Pn -> (forall s. Reifies s (AltDict (Error e)) => A s (Error e) a) -> Error e a
notAtPosn p = withAlt $ \case
  Failure err -> if any ((p ==) . fst) err then id else const $ Failure err
  res         -> const res

-- notAtPosn' :: forall e a. Pn -> (forall s. Reifies s (Def Alt (Error e)) => Lift Alt (Error e) s a) -> Error e a
-- notAtPosn' p = flip (with @Alt @(Error e)) undefined $ \case
--   Failure err -> if any ((p ==) . fst) err then id else const $ Failure err
--   res         -> const res


-- newtype Lift (p :: (* -> *) -> Constraint) (f :: * -> *) (s :: * -> *) a = Lift { lower :: f a } deriving (Functor)

-- class ReifiableConstraint p where
--   data Def (p :: (* -> *) -> Constraint) (f :: * -> *) :: *
--   reifiedIns :: Reifies s (Def p f) :- p (Lift p f s)


-- instance Functor f => ReifiableConstraint Alt where
--   data Def Alt f = Alt { alt_ :: forall a. f a -> f a -> f a }
--   reifiedIns = Sub Dict


-- instance (Functor (Lift Alt f s), Reifies s (Def Alt f)) => Alt (Lift Alt f s) where
--   Lift a <!> Lift b = let alt' = alt_ $ reflect (Proxy @s)
--                        in Lift $ a `alt'` b

-- with :: forall p f a. Def p f -> (forall (s :: * -> *). Reifies s (Def p f) => Lift p f s a) -> f a
-- with d comp = reify @(Def p f) d $ ((\(Proxy :: Proxy (s :: * -> *)) -> lower (comp @s)) :: forall (s :: * -> *). Reifies s (Def p f) => Proxy s -> f a)


newtype A s f a = A { runA :: f a } deriving (Show, Functor)

newtype AltDict f = AltDict { alt :: forall a. f a -> f a -> f a }

instance (Functor (A s f), Reifies s (AltDict f)) => Alt (A s f) where
 A l <!> A r = let alt_ = alt $ reflect (Proxy @s)
                in A $ l `alt_` r

withAlt :: (forall a. f a -> f a -> f a) -> (forall s. Reifies s (AltDict f) => A s f b) -> f b
withAlt alt_ comp = reify (AltDict alt_) $ \(_ :: Proxy s) -> runA (comp @s)
