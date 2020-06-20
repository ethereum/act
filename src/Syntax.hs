{-
 -
 - This file contains the data types for the parsed syntax. Each
 - construct is annotated with an example. The types here should
 - mirror the structure in the happy grammar almost directly.
 -
 - TODO:
 - + implement remaining expressions and types
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
import Data.Functor.Classes
import Text.Show.Deriving
import Data.List (intercalate)
import Lex


type Id = String
type Pn = AlexPosn
type Annotated t = (t, Pn)

data Act = Act
  (Annotated RawConstructor)
  [Annotated RawBehaviour]

-- missing return
data RawConstructor = RawConstructor
  Id -- contract
  (Annotated Interface)
  [Annotated Creation] -- creates
  (Maybe (Annotated Claim))

data RawBehaviour = RawBehaviour
  Id -- name
  Id -- contract
  (Annotated Interface)
  (Maybe [AnnExpr]) -- preconditions
  [Annotated Case] -- cases

-- `interface transfer(uint256 value, address to)`
data Interface = Interface Id [Annotated Decl]

data Creation
  = CDefn (Annotated Defn)       -- `uint a := 1`
  | CDecl (Annotated Decl)       -- `mapping(address => uint) m`

data Case = Case AnnExpr [Annotated Claim]

data Claim
  = StorageClaim [Annotated Store]
  | ReturnClaim AnnExpr

-- typechecker should ensure that only storage references appear
-- on the LHS
data Store = Store AnnExpr AnnExpr

data Decl = Decl AnnType Id

data Defn = Defn AnnType Id AnnExpr

data TypeF t
  = TUInt Int
  | TInt Int
  | TBool
  | TAddress
  | TMapping t t
  deriving Functor

type Type = Fix TypeF
type AnnType = Fix (Product TypeF (Const Pn))

data ExpF e

  -- booleans
  = EBoolLit Bool       -- `true`
  | ENot e              -- `not a`
  | EAnd e e            -- `a and b`
  | EOr e e             -- `a or b`
  | EImpl e e           -- `a => b`

  -- binary relations
  | EEq e e             -- `a == b`
  | ENEq e e            -- `a =/= b`
  | ELE e e             -- `a <= b`
  | ELT e e             -- `a < b`
  | EGE e e             -- `a >= b`
  | EGT e e             -- `a > b`

  -- integers
  | EIntLit Integer     -- `666`
  | EAdd e e            -- `a + b`
  | ESub e e            -- `a - b`
  | EMul e e            -- `a * b`
  | EDiv e e            -- `a / b`
  | EMod e e            -- `a % b`
  | EExp e e            -- `a ^ b`

  -- other
  | ERead Id            -- `a`
  | EZoom e e
  | EEnv EthEnv         -- `CALLVALUE`
  | EITE e e e          -- `if a then b else c`
  | EScore              -- `_`

  deriving Functor

-- position annotation
type Expr = Fix ExpF
type AnnExpr = Fix (Product ExpF (Const Pn))

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

-- would much rather do this without TH if possible
deriving instance Show EthEnv
$(deriveShow1 ''ExpF)
$(deriveShow1 ''TypeF)
deriving instance Show Act
deriving instance Show RawConstructor
deriving instance Show RawBehaviour
deriving instance Show Interface
deriving instance Show Creation
deriving instance Show Case
deriving instance Show Claim
deriving instance Show Store
deriving instance Show Decl
deriving instance Show Defn
deriving instance Show a => Show (TypeF a)
deriving instance Show a => Show (ExpF a)
