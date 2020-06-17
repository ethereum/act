{-
 -
 - This file contains the data types for the parsed syntax. Each
 - construct is annotated with an example. The types here should
 - mirror the structure in the happy grammar directly.
 -
 - Every node is annotated with position information.
 -
 - TODO:
 - + implement remaining expressions
 - + external storage
 -
 -}

{-# LANGUAGE DeriveFunctor #-}

{-# LANGUAGE GADTs     #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax where

import Data.Functor.Foldable
import Data.Functor.Product
import Data.Functor.Const
-- import Data.List (intercalate)
import EVM.ABI (AbiType)
import EVM.Solidity (SlotType)
import Lex

import Text.Show.Deriving

type Id = String

{-

data RawConstructor = RawConstructor
  Id -- name
  Id -- contract
  Interface
  [Creation] -- creates
  -- missing return
  deriving (Eq, Show)

data RawBehaviour = RawBehaviour
  Id -- name
  Id -- contract
  Interface
  (Maybe [UntypedExp]) -- preconditions
  [Case] -- cases
  deriving (Eq, Show)

data Creation
  = CDefn Defn      -- `uint a := 1`
  | CDecl Decl      -- `mapping(address => uint) m`
  deriving (Eq, Show)

-- `interface transfer(uint256 value, address to)`
data Interface = Interface Id [Decl]
  deriving (Eq)

data Case = Case UntypedExp [Claim]
  deriving (Eq, Show)

data Claim
  = StorageClaim [Store]        -- storage s => 1
  | ReturnClaim UntypedExp            -- returns 1
  deriving (Eq, Show)

data Store = Store Ref UntypedExp
  deriving (Eq, Show)

data Ref
  = Ref Id
  | Zoom Id UntypedExp
  deriving (Eq, Show)

data Decl = Decl Type Id
  deriving (Eq)

data Defn = Defn Type Id UntypedExp
  deriving (Eq, Show)

-}

data Type
  = AbiType AbiType
  | Mapping Type Type
  deriving (Eq, Show)

data ExpF e

  -- booleans
  = EBoolLit Bool       -- `true`
  | EAnd e e            -- `a and b`
  | EOr e e             -- `a or b`
  | ENot e              -- `not a`
  | EEq e e             -- `a == b`
  | ENeq e e            -- `a =/= b`
  | ELE e e             -- `a <= b`
  | ELT e e             -- `a < b`
  | EGE e e             -- `a >= b`
  | EGT e e             -- `a > b`

  -- numbers
  | EIntLit Integer     -- `666`
  | EAdd e e            -- `a + b`
  | ESub e e            -- `a - b`
  | EMul e e            -- `a * b`
  | EDiv e e            -- `a / b`
  | EMod e e            -- `a % b`
  | EExp e e            -- `a ^ b`

  -- other
  -- | ERead Ref           -- `a`
  | EEnv EthEnv         -- `CALLVALUE`
  | EITE e e e          -- `if a then b else c`
  | EScore              -- `_`

  deriving (Eq, Show, Functor)

data EthEnv
  = EnvCaller
  | EnvCallValue
  | EnvCallDepth
  | EnvOrigin
  | EnvBlockHash
  | EnvBlockNumber
  | EnvDifficulty
  | EnvChainID
  | EnvGasLimit
  | EnvCoinbase
  | EnvTimestamp
  | EnvAddress
  | EnvNonce
  deriving (Show, Eq)

$(deriveShow1 ''ExpF)

type Untyped = Fix ExpF

-- position annotation
type AnnExp = Fix (Product ExpF (Const AlexPosn))

-- data Act = Act RawConstructor [RawBehaviour]
--   deriving (Eq, Show)
data Act = Act AnnExp
  deriving Show

{- 

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

instance Show Decl where
  show (Decl t a) = show t <> " " <> a

 -}

