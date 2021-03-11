{-# LANGUAGE GADTs #-}

module SMT (runSMT, asSMT, expToSMT2, mkSMT, isError, SMTConfig(..), SMTResult(..), Solver(..), When(..)) where

import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.List

import RefinedAst
import Extract
import Syntax (Id, EthEnv(..))
import Print (prettyEnv)
import Type (defaultStore)

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

isError :: SMTResult -> Bool
isError (Error {}) = True
isError _          = False

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

mkPostconditionQueries :: Behaviour -> [(ReturnExp, SMT2)]
mkPostconditionQueries behv@(Behaviour _ _ _ interface preconds postconds stateUpdates _) = undefined
  where
    storage = concatMap tup2List $ declareStorageLocation' . getLoc <$> stateUpdates

    args = declareVar <$> varsFromBehaviour behv
    envs = declareEthEnv <$> ethEnvFromBehaviour behv
    pres = expToSMT2 Pre <$> preconds
    posts = expToSMT2 Post <$> postconds
    updates = encodeUpdate <$> stateUpdates

    tup2List (a,b) = [a, b]

runSMT :: SMTConfig -> SMT2 -> IO SMTResult
runSMT (SMTConfig solver _ _) e = do
  let input = intercalate "\n" [e, "(check-sat)"]
  (exitCode, stdout, _) <- readProcessWithExitCode (show solver) ["-in"] input
  pure $ case exitCode of
    ExitFailure code -> Error code stdout
    ExitSuccess -> case stdout of
                     "sat\n" -> Sat
                     "unsat\n" -> Unsat
                     _ -> error "fuck"

asSMT :: When -> Exp Bool -> SMTExp
asSMT when e = SMTExp store args environment assertions
  where
    store = foldl' addToStore Map.empty (locsFromExp e)
    environment = Map.fromList $ fmap (\env -> (prettyEnv env, declareEthEnv env)) (ethEnvFromExp e)
    args = Map.fromList $ fmap (\var -> (nameFromVar var, declareVar var)) (varsFromExp e)
    assertions = ["(assert " <> expToSMT2 when e <> ")"]

    addToStore :: Map Id (SMT2, SMT2) -> StorageLocation -> Map Id (SMT2, SMT2)
    addToStore store' loc = Map.insertWith
                              (const id) -- if the name exists we want to keep its value as-is
                              (nameFromLoc when loc)
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

encodeUpdate :: Either StorageLocation StorageUpdate -> SMT2
encodeUpdate (Left loc) = "(assert (= " <> nameFromLoc Pre loc <> " " <> nameFromLoc Post loc <> "))"
encodeUpdate (Right update) = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode item e = "(assert (= " <> nameFromItem Post item <> " " <> expToSMT2 Pre e <> "))"

declareVar :: Var -> SMT2
declareVar v = case v of
  VarInt (IntVar a) -> constant a (varType v)
  VarBool (BoolVar a) -> constant a (varType v)
  VarBytes (ByVar a) -> constant a (varType v)
  _ -> error "TODO: refine types so this never happens"

declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ defaultStore

declareStorage :: [StorageLocation] -> [SMT2]
declareStorage = undefined

declareMappings :: [StorageLocation] -> [(SMT2, SMT2)]
declareMappings = undefined

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
    name item = nameFromItem when item

declareStorageLocation' :: StorageLocation -> (SMT2, SMT2)
declareStorageLocation' loc = case loc of
  IntLoc item -> case item of
    DirectInt {} -> mkdirect item Integer
    MappedInt _ _ ixs -> mkarray item ixs Integer
  BoolLoc item -> case item of
    DirectBool {} -> mkdirect item Boolean
    MappedBool _ _ ixs -> mkarray item ixs Boolean
  BytesLoc item -> case item of
    DirectBytes {} -> mkdirect item ByteStr
    MappedBytes _ _ ixs -> mkarray item ixs ByteStr
  where
    mkdirect item tp = (constant (nameFromItem Pre item) tp, constant (nameFromItem Post item) tp)
    mkarray item ixs tp = (array (nameFromItem Pre item) ixs tp, array (nameFromItem Post item) ixs tp)

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
    DirectInt {} -> nameFromItem w item
    DirectBool {} -> nameFromItem w item
    DirectBytes {} -> nameFromItem w item
    MappedInt _ _ ixs -> select (nameFromItem w item) ixs
    MappedBool _ _ ixs -> select (nameFromItem w item) ixs
    MappedBytes _ _ ixs -> select (nameFromItem w item) ixs

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
        ixsToSMT2 e' = case e' of
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

varType :: Var -> MType
varType (VarInt {}) = Integer
varType (VarBool {}) = Boolean
varType (VarBytes {}) = ByteStr

--- Variable Names ---

nameFromItem :: When -> TStorageItem a -> Id
nameFromItem when item = case item of
  DirectInt c name -> c @@ name @@ show when
  DirectBool c name -> c @@ name @@ show when
  DirectBytes c name -> c @@ name @@ show when
  MappedInt c name _ -> c @@ name @@ show when
  MappedBool c name _ -> c @@ name @@ show when
  MappedBytes c name _ -> c @@ name @@ show when

nameFromLoc :: When -> StorageLocation -> Id
nameFromLoc when loc = case loc of
  IntLoc item -> nameFromItem when item
  BoolLoc item -> nameFromItem when item
  BytesLoc item -> nameFromItem when item

nameFromVar :: Var -> Id
nameFromVar v = case v of
  VarInt (IntVar a) -> a
  VarBool (BoolVar a) -> a
  VarBytes (ByVar a) -> a
  _ -> error "TODO: refine AST so this isn't needed anymore"

(@@) :: String -> String -> String
x @@ y = x <> "_" <> y

