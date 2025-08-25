{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Syntax.TypedExplicit
Description : AST data types where all implicit timings have been made explicit.
-}
module Act.Syntax.TypedExplicit (module Act.Syntax.TypedExplicit) where

import qualified Act.Syntax.Typed as Typed
import Act.Syntax.Typed (Timing(..),setPre,setPost)

-- Reexports
import Act.Syntax.Typed as Act.Syntax.TypedExplicit hiding (Timing(..),Timable(..),Time,Neither,Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,StorageUpdate,StorageLocation,CalldataLocation,TItem,Exp,TypedExp,TypedArgument,Ref)
import Act.Syntax.Typed as Act.Syntax.TypedExplicit (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour, pattern Exp)


-- We shadow all timing-agnostic AST types with explicitly timed versions.
type Act              = Typed.Act              Timed
type Contract         = Typed.Contract         Timed
type Invariant        = Typed.Invariant        Timed
type InvariantPred    = Typed.InvariantPred    Timed
type Constructor      = Typed.Constructor      Timed
type Behaviour        = Typed.Behaviour        Timed
type StorageUpdate    = Typed.StorageUpdate    Timed
type StorageLocation  = Typed.StorageLocation  Timed
type CalldataLocation = Typed.CalldataLocation Timed
type Ref            k = Typed.Ref            k Timed
type TItem        k a = Typed.TItem        k a Timed
type Exp            a = Typed.Exp            a Timed
type TypedExp         = Typed.TypedExp         Timed
type TypedArgument    = Typed.TypedArgument    Timed

------------------------------------------
-- * How to make all timings explicit * --
------------------------------------------

instance Annotatable Typed.Act where
  annotate (Typed.Act store act) = Typed.Act store $ fmap annotate act

instance Annotatable Typed.Contract where
  annotate (Typed.Contract ctor behv) = Typed.Contract (annotate ctor) (fmap annotate behv)

instance Annotatable Typed.Invariant where
  annotate inv@Invariant{..} = inv
    { _ipreconditions = setPre <$> _ipreconditions
    , _istoragebounds = setPre <$> _istoragebounds
    , _predicate = annotate _predicate
    }

instance Annotatable Typed.InvariantPred where
  annotate (PredUntimed p) = PredTimed (setPre p) (setPost p)

instance Annotatable Typed.Constructor where
  annotate ctor@Constructor{..} = ctor
    { _cpreconditions = setPre <$> _cpreconditions
    , _initialStorage = annotate <$> _initialStorage
    , _invariants  = annotate <$> _invariants
    }

instance Annotatable Typed.Behaviour where
  annotate behv@Behaviour{..} = behv
    { _preconditions = setPre <$> _preconditions
    , _caseconditions = setPre <$> _caseconditions
    , _stateUpdates  = annotate <$> _stateUpdates
    }

instance Annotatable Typed.StorageUpdate where
  -- The timing in items only refers to the timing of mapping indices of a
  -- storage update. Hence, it should be Pre
  annotate (Update typ item expr) = Update typ (setPre item) (setPre expr)
