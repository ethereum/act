{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Syntax.TypedImplicit
Description : AST data types which have passed type checking but still contain implicit timings.
-}
module Act.Syntax.TypedImplicit (module Act.Syntax.TypedImplicit) where

import qualified Act.Syntax.Typed as Typed

-- Reexports
import Act.Syntax.Typed as Act.Syntax.TypedImplicit hiding (Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,StorageUpdate,StorageLocation)
import Act.Syntax.Typed as Act.Syntax.TypedImplicit (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour)

-- We shadow all AST types with versions that need to have implicit timings
type Act             = Typed.Act             Untimed
type Contract        = Typed.Contract        Untimed
type Invariant       = Typed.Invariant       Untimed
type Constructor     = Typed.Constructor     Untimed
type Behaviour       = Typed.Behaviour       Untimed
type StorageUpdate   = Typed.StorageUpdate   Untimed
type StorageLocation = Typed.StorageLocation Untimed