{-# LANGUAGE GADTs #-}

module SMT (runSMT, asSMT) where

import qualified Data.Map.Strict as Map
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.List

import RefinedAst
import Extract
import Syntax (Id, EthEnv(..))
import Print (prettyEnv)
import Type (defaultStore)

{-
   This module contains low level utilities for:
    - constructing smt queries from Act expressions
    - dispatching those queries to an smt solver
    - getting a model for unsatisfiable queries
-}

--- Data ---

data Solver = Z3 | CVC4
data When = Pre | Post

type SMT2 = String

instance Show When where
  show Pre = "pre"
  show Post = "post"

data SMTConfig = SMTConfig
  { _solver :: Solver
  , _timeout :: Integer
  , _debug :: Bool
  , _processes :: Integer
  }

data SMTExp = SMTExp
  { _storage :: Map Id (SMT2, SMT2)
  , _calldata :: Map Id SMT2
  , _environment :: Map Id SMT2
  , _assertions :: [ SMT2 ]
  }

data Model = Model
  { _mstorage :: Map Id (MType, MType)
  , _mcalldata :: Map Id MType
  , _menvironment :: Map Id MType
  }

data SMTResult
  = Sat
  | Unsat Model
  | Unknown

--- External Interface ---

runSMT :: SMTConfig -> [SMTExp] -> IO [(SMTExp, SMTResult)]
runSMT conf exps = undefined

asSMT :: Exp a -> SMTExp
asSMT e = SMTExp store args environment assertions
  where
    store = foldl' addToStore Map.empty (locsFromExp e)
    environment = Map.fromList $ fmap (\env -> (prettyEnv env, declareEthEnv env)) (ethEnvFromExp e)
    args = Map.empty
    assertions = []

    addToStore store' loc = case Map.lookup (nameFromLoc loc) store' of
      Just _ -> store'
      Nothing -> Map.insert
                   (nameFromLoc loc)
                   (declareStorageLocation Pre loc, declareStorageLocation Post loc)
                   store'

--- SMT2 generation ---

declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ defaultStore

declareStorageLocation :: When -> StorageLocation -> SMT2
declareStorageLocation when loc = case loc of
  IntLoc item -> case item of
    DirectInt {} -> constant (name item) Integer
    MappedInt _ _ ixs -> array (name item) ixs Integer
  BoolLoc item -> case item of
    DirectBool {} -> constant (name item) Boolean
    MappedBool _ _ ixs -> array (name item) ixs Boolean
  BytesLoc item -> case item of
    DirectBytes {} -> constant (name item) ByteStr
    MappedBytes _ _ ixs -> array (name item) ixs ByteStr
  where
    name :: TStorageItem a -> Id
    name item = nameFromItem item @@ show when

constant :: Id -> MType -> SMT2
constant name tp = "(declare-const " <> name <> " " <> (sType tp) <> ")"

array :: Id -> NonEmpty ReturnExp -> MType -> SMT2
array name ixs ret = "(declare-const " <> name <> " " <> arrayDecl ixs <> ")"
  where
    arrayDecl (hd :| []) = "(Array " <> sType' hd <> " " <> sType ret <> ")"
    arrayDecl (hd :| tl) = "(Array " <> sType' hd <> " " <> (arrayDecl (NonEmpty.fromList tl)) <> ")"

sType :: MType -> SMT2
sType Integer = "Int"
sType Boolean = "Bool"
sType ByteStr = "String"

sType' :: ReturnExp -> SMT2
sType' (ExpInt {}) = "Int"
sType' (ExpBool {}) = "Bool"
sType' (ExpBytes {}) = "String"

--- Variable Names ---

nameFromItem :: TStorageItem a -> Id
nameFromItem item = case item of
  DirectInt c name -> c @@ name
  DirectBool c name -> c @@ name
  DirectBytes c name -> c @@ name
  MappedInt c name _ -> c @@ name
  MappedBool c name _ -> c @@ name
  MappedBytes c name _ -> c @@ name

nameFromLoc :: StorageLocation -> Id
nameFromLoc loc = case loc of
  IntLoc item -> nameFromItem item
  BoolLoc item -> nameFromItem item
  BytesLoc item -> nameFromItem item

(@@) :: String -> String -> String
x @@ y = x <> "_" <> y

