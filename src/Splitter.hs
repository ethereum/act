
module Splitter where

import Syntax
import RefinedAst
import Data.Map.Strict    (Map) -- abandon in favor of [(a,b)]?


data Implementation = Implementation
  {_contractBinaries :: Map Contract Code,
   _storageLayout :: Map Contract Layout
  }

type Code = (String, String)

data Layout = Layout {
  slot :: Int,
  offset :: Int,
  label :: Id,
  encoding :: Encoding,
  length :: Int
  }

data Encoding = Inplace | Mapping | DynamicArray | Bytes

data KSpec = KSpec {
  k :: KTerm,
  program :: String,
  jumpDests :: String,
  callData :: TypedExp,
  output :: TypedExp,
  statusCode :: StatusCode,
  kreturn :: String
--  accounts :: Map Contract
}

data KTerm = Execute | Halt

data StatusCode
  = EVMC_SUCCESS
  | EVMC_REVERT
  | EVMC_OOG

kaseSplit :: Behaviour -> Implementation -> [KSpec]
kaseSplit = error "TODO"
