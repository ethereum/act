{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Syntax.Typed
Description : AST data types which have passed type checking but still contain implicit timings.
-}
module Syntax.Typed (module Syntax.Typed) where

import qualified Syntax.TimeAgnostic as Agnostic

-- Reexports
import Syntax.TimeAgnostic as Syntax.Typed hiding (Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,StorageUpdate,StorageLocation) 
import Syntax.TimeAgnostic as Syntax.Typed (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour)

-- We shadow all timing-agnostic AST types with versions
-- that need to have implicit timings where possible.
type Act             = Agnostic.Act             Untimed
type Contract        = Agnostic.Contract        Untimed
type Invariant       = Agnostic.Invariant       Untimed
type Constructor     = Agnostic.Constructor     Untimed
type Behaviour       = Agnostic.Behaviour       Untimed
type StorageUpdate   = Agnostic.StorageUpdate   Untimed
type StorageLocation = Agnostic.StorageLocation Untimed
