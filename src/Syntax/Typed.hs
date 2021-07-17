{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Syntax.Typed
Description : AST data types which have passed type checking but still contain implicit timings.
-}
module Syntax.Typed (module Syntax.Typed) where

import qualified Syntax.TimeAgnostic as Agnostic

-- Reexports
import Syntax.TimeAgnostic as Syntax.Typed hiding (Claim,Transition,Invariant,InvariantPred,Constructor,Behaviour,Rewrite,StorageUpdate,StorageLocation) 
import Syntax.TimeAgnostic as Syntax.Typed (pattern Invariant, pattern Constructor, pattern Behaviour, pattern Rewrite)

-- We shadow all timing-agnostic AST types with versions
-- that need to have implicit timings where possible.
type Claim           = Agnostic.Claim           Untimed
type Transition      = Agnostic.Transition      Untimed
type Invariant       = Agnostic.Invariant       Untimed
type Constructor     = Agnostic.Constructor     Untimed
type Behaviour       = Agnostic.Behaviour       Untimed
type Rewrite         = Agnostic.Rewrite         Untimed
type StorageUpdate   = Agnostic.StorageUpdate   Untimed
type StorageLocation = Agnostic.StorageLocation Untimed
