{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Syntax.Refined
Description : AST data types where all implicit timings have been made explicit.
-}
module Syntax.Refined (module Syntax.Refined) where

import qualified Syntax.TimeAgnostic as Agnostic
import Syntax.TimeAgnostic (Timing(..),setPre,setPost)

-- Reexports
import Syntax.TimeAgnostic as Syntax.Refined hiding (Timing(..),Timable,setTime,setPre,setPost,Time,Neither,Claim,Transition,Invariant,InvariantPred,Constructor,Behaviour,Rewrite,StorageUpdate,StorageLocation,TStorageItem,Exp,TypedExp)
import Syntax.TimeAgnostic as Syntax.Refined (pattern Invariant, pattern Constructor, pattern Behaviour, pattern Rewrite, pattern Exp)


-- We shadow all timing-agnostic AST types with explicitly timed versions.
type Claim           = Agnostic.Claim           Timed
type Transition      = Agnostic.Transition      Timed
type Invariant       = Agnostic.Invariant       Timed
type InvariantPred   = Agnostic.InvariantPred   Timed
type Constructor     = Agnostic.Constructor     Timed
type Behaviour       = Agnostic.Behaviour       Timed
type Rewrite         = Agnostic.Rewrite         Timed
type StorageUpdate   = Agnostic.StorageUpdate   Timed
type StorageLocation = Agnostic.StorageLocation Timed
type TStorageItem a  = Agnostic.TStorageItem  a Timed
type Exp          a  = Agnostic.Exp           a Timed
type TypedExp        = Agnostic.TypedExp        Timed

------------------------------------------
-- * How to make all timings explicit * --
------------------------------------------

instance Refinable Agnostic.Claim where
  refine claim = case claim of
    C ctor -> C $ refine ctor
    B behv -> B $ refine behv
    I invr -> I $ refine invr
    S stor -> S stor

instance Refinable Agnostic.Transition where
  refine trans = case trans of
    Ctor ctor -> Ctor $ refine ctor
    Behv behv -> Behv $ refine behv

instance Refinable Agnostic.Invariant where
  refine inv@Invariant{..} = inv
    { _ipreconditions = setPre <$> _ipreconditions
    , _istoragebounds = setPre <$> _istoragebounds
    , _predicate      = (setPre _predicate, setPost _predicate)
    }

instance Refinable Agnostic.Constructor where
  refine ctor@Constructor{..} = ctor
    { _cpreconditions = setPre <$> _cpreconditions
    , _initialStorage = refine <$> _initialStorage
    , _cstateUpdates  = refine <$> _cstateUpdates
    }

instance Refinable Agnostic.Behaviour where
  refine behv@Behaviour{..} = behv
    { _preconditions = setPre <$> _preconditions
    , _stateUpdates  = refine <$> _stateUpdates
    }

instance Refinable Agnostic.Rewrite where
  refine (Constant location) = Constant $ setPre location -- not 100% on this `setPre`?
  refine (Rewrite  update)   = Rewrite  $ refine update

instance Refinable Agnostic.StorageUpdate where
  refine update = case update of
    IntUpdate item expr -> IntUpdate (setPost item) (setPre expr)
    BoolUpdate item expr -> BoolUpdate (setPost item) (setPre expr)
    BytesUpdate item expr -> BytesUpdate (setPost item) (setPre expr)
