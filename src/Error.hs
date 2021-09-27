{-# LANGUAGE OverloadedLists,TypeOperators, LambdaCase, AllowAmbiguousTypes, TypeApplications, TypeFamilies, DeriveFunctor, ConstraintKinds, UndecidableInstances, FlexibleContexts, FlexibleInstances, RankNTypes, KindSignatures, ApplicativeDo, MultiParamTypeClasses, ScopedTypeVariables, InstanceSigs #-}

module Error (module Error) where

import Control.Monad.Writer hiding (Alt)
import Data.Functor
import Data.Functor.Alt
import Data.List.NonEmpty as NE
import Data.Validation as Error
import Data.Proxy
import Data.Reflection
import GHC.Generics

import Syntax.Untyped (Pn)

-- Reexport NonEmpty so that we can use `-XOverloadedLists` without thinking.
import Data.List.NonEmpty as Error (NonEmpty)

type Error e = Validation (NonEmpty (Pn,e))

throw :: (Pn,e) -> Error e a
throw msg = Failure [msg]

infixr 1 <==<, >==>

-- These allow us to chain error-prone computations without a @Monad@ instance.
(<==<) :: (b -> Error e c) -> (a -> Error e b) -> a -> Error e c
(<==<) = flip (>==>)

(>==>) :: (a -> Error e b) -> (b -> Error e c) -> a -> Error e c
f >==> g = \x -> f x `bindValidation` g

-- | If there is no error at the supplied position, we accept this result and
-- do not attempt to run any later branches, even if there were other errors.
-- (The second argument looks intimidating but it simply demands that each
-- @'Error' e a@ branch is wrapped in 'A' before being passed to '(<!>)'.)
notAtPosn :: Pn -> (forall s. Reifies s (Alt_ (Error e)) => A s (Error e) a) -> Error e a
notAtPosn p = withAlt $ \case
  Failure err -> if any ((p ==) . fst) err then id else const $ Failure err
  res         -> const res

-- | Wraps any functor in a type that can be supplied a custom 'Alt' instance. 
newtype A s f a = A { runA :: f a }
  deriving Functor

-- | The type of custom 'Alt' instances.
newtype Alt_ f = Alt_ { alt :: forall a. f a -> f a -> f a }

-- | Given a proof that we can reify a custom 'Alt' instance on the wrapped
-- functor, we can give it an actual 'Alt' instance (allows using '(<!>)').
instance (Functor f, Reifies s (Alt_ f)) => Alt (A s f) where
  A l <!> A r = A $ alt (reflect @s Proxy) l r

-- | The first argument is used as a custom 'Alt' instance when evaluating
-- a functor wrapped in 'A'.
withAlt :: (forall a. f a -> f a -> f a) -> (forall s. Reifies s (Alt_ f) => A s f b) -> f b
withAlt alt_ comp = reify (Alt_ alt_) $ \(_ :: Proxy s) -> runA @s comp
