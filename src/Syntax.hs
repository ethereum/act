{-
 -
 - This file contains the data types for the parsed syntax. Each
 - construct is annotated with an example. The types here should
 - mirror the structure in the happy grammar directly.
 -
 - TODO:
 - + implement remaining expressions
 - + external storage
 -
 -}

module Syntax where

import Data.List (intercalate)
import EVM.ABI (AbiType)
import EVM.Solidity (SlotType)
-- import Data.Bitraversable


type Id = String

-- can't override show instance for AlexPosn
-- so seems reasonable to use our own
data Pn = Pn Int Int

data Act = Act RawConstructor [RawBehaviour]
  deriving (Eq, Show)

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
  (Maybe [Expr]) -- preconditions
  [Case] -- cases
  deriving (Eq, Show)

-- `uint a := 1`
-- `mapping(address => uint)`
data Creation
  = CDefn Defn
  | CDecl Decl
  deriving (Eq, Show)

data Interface = Interface Id [Decl]
  deriving (Eq)

data Case = Case Expr [Claim]
  deriving (Eq, Show)

data Claim
  = StorageClaim [Store]
  | ReturnClaim Expr
  deriving (Eq, Show)

data Store = Store Ref Expr
  deriving (Eq, Show)

data Ref
  = Ref Id
  | Zoom Id Expr
  deriving (Eq, Show)

data Decl = Decl Type Id
  deriving (Eq)

data Defn = Defn Type Id Expr
  deriving (Eq, Show)

data Type
  = AbiType AbiType
  | Mapping Type Type
  deriving (Eq, Show)

data Expr

  -- booleans
  = EBoolLit Bool       -- `true`
  | EAnd Expr Expr      -- `a and b`
  | EOr Expr Expr       -- `a or b`
  | ENot Expr           -- `not a`
  | EEq Expr Expr       -- `a == b`
  | ENeq Expr Expr      -- `a =/= b`
  | ELE Expr Expr       -- `a <= b`
  | ELT Expr Expr       -- `a < b`
  | EGE Expr Expr       -- `a >= b`
  | EGT Expr Expr       -- `a > b`

  -- numbers
  | EIntLit Integer     -- `666`
  | EAdd Expr Expr      -- `a + b`
  | ESub Expr Expr      -- `a - b`
  | EMul Expr Expr      -- `a * b`
  | EDiv Expr Expr      -- `a / b`
  | EMod Expr Expr      -- `a % b`
  | EExp Expr Expr      -- `a ^ b`

  -- other
  | ERead Ref           -- `a`
  | EEnv EthEnv         -- `CALLVALUE`
  | EITE Expr Expr Expr -- `if a then b else c`

  deriving (Eq, Show)

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


instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

instance Show Decl where
  show (Decl t a) = show t <> " " <> a

