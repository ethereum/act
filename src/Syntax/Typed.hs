-- {-# LANGUAGE ExistentialQuantification #-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE DataKinds #-}
-- {-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE OverloadedStrings #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE RecordWildCards #-}
-- {-# Language MultiParamTypeClasses #-}
-- {-# Language FlexibleContexts #-}
-- {-# Language ScopedTypeVariables #-}
-- {-# Language TypeFamilies #-}
-- {-# Language TypeApplications #-}
-- {-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
-- {-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax.Typed (module Syntax.Typed) where

-- import Control.Applicative (empty)

-- import Data.Char (toLower)
-- import Data.List (genericDrop,genericTake)
-- import Data.Text (pack)
-- import Data.Type.Equality
-- import Data.Typeable
-- import Data.Map.Strict (Map)
-- import Data.List.NonEmpty hiding (fromList)
-- import Data.ByteString (ByteString)
-- import qualified Data.ByteString as BS
-- import Data.String (fromString)

-- import EVM.Solidity (SlotType(..))

-- import Data.Aeson
-- import Data.Aeson.Types
-- import Data.Vector (fromList)

-- import Syntax.TimingAgnostic hiding (Claim,Transition,Invariant,Constructor,Behaviour,Rewrite,StorageUpdate,StorageLocation)
import Syntax.TimeAgnostic as Syntax.Typed hiding (Claim,Transition,Invariant,InvariantExp,Constructor,Behaviour,Rewrite,StorageUpdate,StorageLocation,TStorageItem,Exp,TypedExp)
import Syntax.TimeAgnostic as Syntax.Typed (pattern Invariant, pattern Constructor, pattern Behaviour, pattern Rewrite, pattern Exp)
import qualified Syntax.TimeAgnostic as Agnostic

type Claim           = Agnostic.Claim           Untimed
type Transition      = Agnostic.Transition      Untimed
type Invariant       = Agnostic.Invariant       Untimed
type InvariantExp    = Agnostic.InvariantExp    Untimed
type Constructor     = Agnostic.Constructor     Untimed
type Behaviour       = Agnostic.Behaviour       Untimed
type Rewrite         = Agnostic.Rewrite         Untimed
type StorageUpdate   = Agnostic.StorageUpdate   Untimed
type StorageLocation = Agnostic.StorageLocation Untimed

type TStorageItem    = Agnostic.TStorageItem
type TypedExp        = Agnostic.TypedExp
type Exp             = Agnostic.Exp
