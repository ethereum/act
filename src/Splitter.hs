{-# LANGUAGE RecordWildCards #-}
module Splitter where

import Syntax
import RefinedAst
import ErrM
import Data.Text
import Parse
import EVM (VM)
import EVM.Symbolic (verify, Precondition, Postcondition)
--import EVM.Solidity (AbiType)
import EVM.Solidity (SolcContract(..))
import Data.Map.Strict    (Map) -- abandon in favor of [(a,b)]?

-- data Implementation = Implementation
--   {_contractBinaries :: Map Id Code,
--    _storageLayout :: Map Id Layout
--   }

-- type Code = (String, String)

-- data Layout = Layout {
--   slot :: Int,
--   offset :: Int,
--   label :: Id,
--   encoding :: Encoding,
--   length :: Int
--   }
-- data Encoding = Inplace | Mapping | DynamicArray | Bytes
-- data KSpec = KSpec {
--   k :: KTerm,
--   program :: String,
--   jumpDests :: String,
--   callData :: String,
--   output :: ReturnExp,
--   statusCode :: StatusCode,
--   kreturn :: String
--  accounts :: Map Contract
-- deriving (Ord, Eq, Read)

-- instance Show KSpec whereR
--   show KSpec { .. }  = error "TODO"

-- data KTerm = Execute | Halt
--   deriving (Ord, Eq, Read)

-- instance Show KTerm where
--   show Execute = "execute"
--   show Halt = "halt"

-- data StatusCode
--   = EVMC_SUCCESS
--   | EVMC_REVERT
--   | EVMC_OOG
--   deriving (Show, Ord, Eq, Read)
--type Signature = (Text, AbiType)

type KSpec = String

makekSpec :: Map Text SolcContract -> Behaviour -> Err (String, KSpec)
makekSpec sources  Behaviour{..} = Bad (nowhere, "todo: make k spec")
