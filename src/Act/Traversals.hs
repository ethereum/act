{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Act.Traversals (TraversableTerm(..)) where

import Data.Functor.Identity
import Act.Syntax.TimeAgnostic
import Prelude hiding (LT, GT)

-- | Generic operations over AST terms
class TraversableTerm a where
  mapTermM  :: Monad m => (forall b t . Exp b t -> m (Exp b t)) -> a -> m a

  mapTerm :: (forall b t . Exp b t -> Exp b t) -> a -> a
  mapTerm f e = runIdentity (mapTermM (Identity . f) e)

instance TraversableTerm (Exp a t) where
  mapTermM = mapExpM

instance TraversableTerm (TypedExp t) where
  mapTermM = mapTypedExpM

instance TraversableTerm (TStorageItem a t) where
  mapTermM = mapTStorageItemM

instance TraversableTerm (StorageRef t) where
  mapTermM = mapStorageRefM

mapExpM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> Exp b t -> m (Exp b t)
mapExpM f = \case
  --booleans
  And p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (And p a' b')
  Or p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Or p a' b')
  Impl p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Impl p a' b')
  Neg p a -> do
    a' <- mapExpM f a
    f (Neg p a')
  LT p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (LT p a' b')
  LEQ p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (LEQ p a' b')
  GEQ p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (GEQ p a' b')
  GT p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (GT p a' b')
  LitBool p a -> f (LitBool p a)

  --integers

  Add p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Add p a' b')
  Sub p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Sub p a' b')
  Mul p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Mul p a' b')
  Div p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Div p a' b')
  Mod p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Mod p a' b')
  Exp p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Exp p a' b')
  LitInt p a -> f (LitInt p a)
  IntEnv p a -> f (IntEnv p a)

  --bounds
  IntMin p a -> f (IntMin p a)
  IntMax p a -> f (IntMax p a)
  UIntMin p a -> f (UIntMin p a)
  UIntMax p a -> f (UIntMax p a)
  InRange p a b -> do
    b' <- mapExpM f b
    f (InRange p a b')

  --bytestrings

  Cat p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Cat p a' b')
  Slice p a b c -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    c' <- mapExpM f c
    f (Slice p a' b' c')
  ByStr p a -> f (ByStr p a)
  ByLit p a -> f (ByLit p a)
  ByEnv p a -> f (ByEnv p a)

  --contracts

  Create p n as -> do
    as' <- mapM (mapTypedExpM f) as
    f (Create p n as')

  --polymorphic

  Eq p s a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Eq p s a' b')
  NEq p s a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (NEq p s a' b')

  ITE p a b c -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    c' <- mapExpM f c
    f (ITE p a' b' c')
  Var p s a i -> f (Var p s a i)
  TEntry p t i -> do
    i' <- mapTStorageItemM f i
    f (TEntry p t i')

mapTypedExpM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> TypedExp t -> m (TypedExp t)
mapTypedExpM f (TExp s e) = do
  e' <- f e
  pure $ TExp s e'

mapTStorageItemM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> TStorageItem b t -> m (TStorageItem b t)
mapTStorageItemM f (Item s v r) = do
  r' <- mapStorageRefM f r
  pure $ Item s v r'

mapStorageRefM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> StorageRef t -> m (StorageRef t)
mapStorageRefM f = \case
  SVar p a b -> pure (SVar p a b)
  SMapping p a b -> do
    a' <- mapStorageRefM f a
    b' <- mapM (mapTypedExpM f) b
    pure $ SMapping p a' b'
  SField p r a b -> do
    r' <- mapStorageRefM f r
    pure $ SField p r' a b
