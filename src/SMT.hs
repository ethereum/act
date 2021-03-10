{-# LANGUAGE GADTs #-}

module SMT (runSMT, asSMT, expToSMT2, mkSMT, testConf, testExp) where

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

import Debug.Trace

import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))

{-
   This module contains low level utilities for:
    - constructing smt queries from Act expressions
    - dispatching those queries to an smt solver
    - getting a model for unsatisfiable queries
-}

--- Data ---

data Solver = Z3 | CVC4
instance Show Solver where
  show Z3 = "z3"
  show CVC4 = "cvc4"

data When = Pre | Post

type SMT2 = String

instance Show When where
  show Pre = "pre"
  show Post = "post"

data SMTConfig = SMTConfig
  { _solver :: Solver
  , _timeout :: Integer
  , _debug :: Bool
  }

data SMTExp = SMTExp
  { _storage :: Map Id (SMT2, SMT2)
  , _calldata :: Map Id SMT2
  , _environment :: Map Id SMT2
  , _assertions :: [ SMT2 ]
  }

instance Show SMTExp where
  show e = intercalate "\n" [storage, calldata, environment, assertions]
    where
      storage = intercalate "\n" $ (\(pre, post) -> pre <> "\n" <> post) <$> Map.elems (_storage e)
      calldata = intercalate "\n" $ Map.elems (_calldata e)
      environment = intercalate "\n" $ Map.elems (_environment e)
      assertions = intercalate "\n" (_assertions e)

data Model = Model
  { _mstorage :: Map Id (MType, MType)
  , _mcalldata :: Map Id MType
  , _menvironment :: Map Id MType
  }
  deriving (Show)

data SMTResult
  = Sat
  | Unsat --Model
  | Unknown
  | Error Int String
  deriving (Show)

testConf = SMTConfig
  { _solver = Z3
  , _timeout = 1
  , _debug = False
  }

testExp = SMTExp
  { _storage = Map.fromList [ ("hi", ("(declare-const hi_pre Int)", "(declare-const hi_post Int)")) ]
  , _calldata = Map.fromList [ ("yo", "(declare-const yo Bool)") ]
  , _environment = Map.fromList [ ("bye" , "(declare-const bye String)") ]
  , _assertions = [
    "(assert (> hi_pre hi_post))",
    "(assert (= yo false))",
    "(assert (= true true))"]
  }

--- External Interface ---

mkSMT :: [Claim] -> [(Invariant, [SMTExp])]
mkSMT = undefined
  {-
mkSMT :: [Claim] -> [(Invariant, [SMTExp])]
mkSMT claims = fmap mkQueries gathered
  where
    gathered = fmap (\inv -> (inv, definition inv, getBehaviours inv)) invariants
    invariants = [i | I i <- claims]
    getBehaviours (Invariant c _ _) = filter (\b -> isPass b && contractMatches c b) [b | B b <- claims]
    definition (Invariant c _ _) = head $ filter (\b -> Pass == _cmode b && _cname b == c) [c' | C c' <- claims]
    contractMatches c b = c == (_contract b)
    isPass b = (_mode b) == Pass
  -}

runSMT :: SMTConfig -> SMTExp -> IO SMTResult
runSMT (SMTConfig solver _ _) e = do
  let input = intercalate "\n" [(show e), "(check-sat)"]
  (exitCode, stdout, _) <- readProcessWithExitCode (show solver) ["-in"] input
  pure $ case exitCode of
    ExitFailure code -> Error code stdout
    ExitSuccess -> case stdout of
                     "sat\n" -> Sat
                     "unsat\n" -> Unsat
                     _ -> error "fuck"

asSMT :: Exp a -> SMTExp
asSMT e = SMTExp store args environment assertions
  where
    store = foldl' addToStore Map.empty (locsFromExp e)
    environment = Map.fromList $ fmap (\env -> (prettyEnv env, declareEthEnv env)) (ethEnvFromExp e)
    args = Map.empty
    assertions = []

    addToStore store' loc = Map.insertWith
                              (const id) -- if the name exists we want to keep its value as-is
                              (nameFromLoc loc)
                              (declareStorageLocation Pre loc, declareStorageLocation Post loc)
                              store'

--- SMT2 generation ---

  {-
mkQueries :: (Invariant, Constructor, [Behaviour]) -> (Invariant, [SMTExp])
mkQueries (inv, constr, behvs) = (inv, inits:methods)
  where
    inits = mkInit inv constr
    methods = mkMethod inv constr <$> behvs
  -}


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

expToSMT2 :: When -> Exp a -> SMT2
expToSMT2 w e = case e of

  -- booleans
  And a b -> binop "and" a b
  Or a b -> binop "or" a b
  Impl a b -> binop "=>" a b
  Neg a -> unop "not" a
  LE a b -> binop "<" a b
  LEQ a b -> binop "<=" a b
  GEQ a b -> binop ">=" a b
  GE a b -> binop ">" a b
  LitBool a -> if a then "true" else "false"
  BoolVar a -> a

  -- integers
  Add a b -> binop "+" a b
  Sub a b -> binop "-" a b
  Mul a b -> binop "*" a b
  Div a b -> binop "div" a b
  Mod a b -> binop "mod" a b
  Exp {} -> error "Internal Error: exponentiation is not supported in smt-lib"
  LitInt a -> show a
  IntVar a -> a
  IntEnv a -> prettyEnv a

  -- bounds
  IntMin a -> show $ intmin a
  IntMax a -> show $ intmax a
  UIntMin a -> show $ uintmin a
  UIntMax a -> show $ uintmax a

  -- bytestrings
  Cat a b -> binop "str.++" a b
  Slice a start end -> triop "str.substr" a start (Sub end start)
  ByVar a -> a
  ByStr a -> a
  ByLit a -> show a
  ByEnv a -> prettyEnv a

  -- builtins
  NewAddr {} -> error "TODO: NewAddr"

  -- polymorphic
  Eq a b -> binop "=" a b
  NEq a b -> unop "not" (Eq a b)
  ITE a b c -> triop "ite" a b c
  TEntry item -> case item of
    DirectInt {} -> nameFromItem item
    DirectBool {} -> nameFromItem item
    DirectBytes {} -> nameFromItem item
    MappedInt _ _ ixs -> select (nameFromItem item) ixs
    MappedBool _ _ ixs -> select (nameFromItem item) ixs
    MappedBytes _ _ ixs -> select (nameFromItem item) ixs

  where
    unop :: String -> Exp a -> SMT2
    unop op a = "(" <> op <> " " <> expToSMT2 w a <> ")"

    binop :: String -> Exp a -> Exp b -> SMT2
    binop op a b = "(" <> op <> " " <> expToSMT2 w a <> " " <> expToSMT2 w b <> ")"

    triop :: String -> Exp a -> Exp b -> Exp c -> SMT2
    triop op a b c = "(" <> op <> " " <> expToSMT2 w a <> " " <> expToSMT2 w b <> " " <> expToSMT2 w c <> ")"

    select :: String -> NonEmpty ReturnExp -> SMT2
    select name ixs = "(" <> "select" <> " " <> name <> foldMap ((" " <>) . ixsToSMT2) ixs <> ")"
      where
        ixsToSMT2 :: ReturnExp -> SMT2
        ixsToSMT2 e = case e of
          ExpInt ei -> expToSMT2 w ei
          ExpBool eb -> expToSMT2 w eb
          ExpBytes ebs -> expToSMT2 w ebs

constant :: Id -> MType -> SMT2
constant name tp = "(declare-const " <> name <> " " <> (sType tp) <> ")"

array :: Id -> NonEmpty ReturnExp -> MType -> SMT2
array name ixs ret = "(declare-const " <> name <> " " <> arrayDecl <> ")"
  where
    arrayDecl = "(Array" <> foldMap ((" " <>) . sType') ixs <> " " <> sType ret <> ")"

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

