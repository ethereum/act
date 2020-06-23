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
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GADTs     #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax where

import Data.Functor.Foldable
import Data.Functor.Product
import Data.Functor.Const
-- import Data.Functor.Identity
import Data.Functor.Classes
import Text.Show.Deriving
import Data.List (intercalate)
import Lex


type Id = String
type Pn = AlexPosn
type Annotated t = (Pn, t)

-- functor domain is expressions
data Act e = Act
  (Constructor e)
  [Behaviour e]
  deriving (Functor, Foldable)

data Constructor e = Constructor
  Id -- contract
  Interface
  [Creation e]  -- creates
  (Maybe e)     -- return
  deriving (Functor, Foldable)

data Behaviour e = Behaviour
  Id -- name
  Id -- contract
  Interface
  [e] -- preconditions
  [Case e] -- cases
  deriving (Functor, Foldable)

-- `interface transfer(uint256 value, address to)`
data Interface = Interface Id [Decl']

data Creation e
  = CDefn (Defn e)      -- `uint a := 1`
  | CDecl Decl'         -- `mapping(address => uint) m`
  deriving (Functor, Foldable)

data Case e
  = Case e (Maybe [Store e]) (Maybe e)
  deriving (Functor, Foldable)

data Store e = Store (Ref' e) e
  deriving (Functor, Foldable)

data Ref e
  = Ref Id
  | MapRef Id e
  deriving (Functor, Foldable)
type Ref' e = Annotated (Ref e)

data Decl = Decl Type Id
type Decl' = Annotated Decl

data Defn e = Defn Decl e
  deriving (Functor, Foldable)

data Type
  = TUInt Int
  | TInt Int
  | TBool
  | TAddress
  | TMap Type Type
  deriving Show

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
  | ERead (Ref e)       -- `a`
  | EEnv EthEnv         -- `CALLVALUE`
  | EITE e e e          -- `if a then b else c`
  | EScore              -- `_`

  deriving (Functor, Foldable)

-- position annotation
type Expr = Fix ExpF
type AnnExpr = Fix (Product (Const Pn) ExpF)

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
  deriving Show

-- would much rather do this without TH if possible
$(deriveShow1 ''ExpF)
$(deriveShow1 ''Ref)
deriving instance Show e => Show (Act e)
deriving instance Show e => Show (Constructor e)
deriving instance Show e => Show (Behaviour e)
deriving instance Show Interface
deriving instance Show e => Show (Creation e)
deriving instance Show e => Show (Case e)
deriving instance Show e => Show (Store e)
deriving instance Show e => Show (Ref e)
deriving instance Show Decl
deriving instance Show e => Show (Defn e)
deriving instance Show a => Show (ExpF a)
