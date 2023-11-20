{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Syntax.Typed
Description : AST data types which have passed type checking but still contain implicit timings.
-}
module Act.Syntax.Typed (module Act.Syntax.Typed) where

import qualified Act.Syntax.TimeAgnostic as Agnostic

-- Reexports
import Act.Syntax.TimeAgnostic as Act.Syntax.Typed hiding (Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,StorageUpdate,StorageLocation)
import Act.Syntax.TimeAgnostic as Act.Syntax.Typed (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour)

-- We shadow all timing-agnostic AST types with versions
-- that need to have implicit timings where possible.
type Act             = Agnostic.Act             Untimed
type Contract        = Agnostic.Contract        Untimed
type Invariant       = Agnostic.Invariant       Untimed
type Constructor     = Agnostic.Constructor     Untimed
type Behaviour       = Agnostic.Behaviour       Untimed
type StorageUpdate   = Agnostic.StorageUpdate   Untimed
type StorageLocation = Agnostic.StorageLocation Untimed
