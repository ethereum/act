{-# LANGUAGE GADTs #-}

module SMT where -- (mkPostC runSMT, asSMT, expToSMT2, mkSMT, isError, SMTConfig(..), SMTResult(..), Solver(..), When(..), SMTExp(..)) where

import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.List

import RefinedAst
import Extract
import Syntax (Id, EthEnv(..), Interface(..), Decl(..))
import Print (prettyEnv)
import Type (defaultStore, metaType)

import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))

--- Data ---

data Solver = Z3 | CVC4
  deriving Eq

instance Show Solver where
  show Z3 = "z3"
  show CVC4 = "cvc4"

data SMTConfig = SMTConfig
  { _solver :: Solver
  , _timeout :: Integer
  , _debug :: Bool
  , _checkSat :: Bool
  }

type SMT2 = String

-- Some expressions should be constructed over the poststate, and some over the prestate...
data When = Pre | Post

instance Show When where
  show Pre = "pre"
  show Post = "post"

-- An SMTExp is a structured representation of an SMT Expression
-- The _storage, _calldata, and _environment fields hold variable declarations
-- The assertions field holds the various constraints that should be satisfied
data SMTExp = SMTExp
  { _storage :: [SMT2]
  , _calldata :: [SMT2]
  , _environment :: [SMT2]
  , _assertions :: [SMT2]
  }

-- TODO: can we get rid of these nubs? or at least use something non quadratic....
instance Show SMTExp where
  show e = intercalate "\n" ["", storage, "", calldata, "", environment, "", assertions, ""]
    where
      storage = ";STORAGE:\n" <> intercalate "\n" (nub $ _storage e)
      calldata = ";CALLDATA:\n" <> intercalate "\n" (nub $ _calldata e)
      environment = ";ENVIRONMENT:\n" <> intercalate "\n" (nub $ _environment e)
      assertions = ";ASSERTIONS:\n" <> intercalate "\n" (nub $ _assertions e)

-- A Query is a structured representation of an SMT query for an individual
-- expression, along with the metadata needed to pretty print the result
data Query
  = Postcondition Claim (Exp Bool) SMTExp
  | Inv Claim Invariant SMTExp
  deriving (Show)

data SMTResult
  = Sat
  | Unsat --Model
  | Unknown
  | Error Int String
  deriving (Show)

data Model = Model
  { _mstorage :: Map Id (MType, MType)
  , _mcalldata :: Map Id MType
  , _menvironment :: Map Id MType
  }
  deriving (Show)

--- External Interface ---

mkPostconditionQueries :: Claim -> [Query]
mkPostconditionQueries (B behv@(Behaviour _ _ _ (Interface _ decls) preconds postconds stateUpdates _)) = mkQuery <$> postconds
  where
    storage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = encodeDecl <$> decls
    envs = declareEthEnv <$> ethEnvFromBehaviour behv

    pres = mkAssert Pre <$> preconds
    updates = encodeUpdate <$> stateUpdates

    mksmt e = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = envs
      , _assertions = pres <> updates <> [mkAssert Pre . Neg $ e]
      }
    mkQuery e = Postcondition (B behv) e (mksmt e)
mkPostconditionQueries (C constructor@(Constructor _ _ (Interface _ decls) preconds postconds initialStorage stateUpdates)) = mkQuery <$> postconds
  where
    localStorage = declareInitialStorage <$> initialStorage
    externalStorage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = encodeDecl <$> decls
    envs = declareEthEnv <$> ethEnvFromConstructor constructor

    pres = mkAssert Pre <$> preconds
    updates = encodeUpdate <$> ((Right <$> initialStorage) <> stateUpdates)

    mksmt e = SMTExp
      { _storage = localStorage <> externalStorage
      , _calldata = args
      , _environment = envs
      , _assertions = pres <> updates <> [mkAssert Pre . Neg $ e]
      }
    mkQuery e = Postcondition (C constructor) e (mksmt e)
mkPostconditionQueries _ = []

mkInvariantQueries :: [Claim] -> [Query]
mkInvariantQueries claims = concatMap mkQuery gathered
  where
    gathered = fmap (\inv -> (inv, definition inv, getBehaviours inv)) invariants
    invariants = [i | I i <- claims]
    getBehaviours (Invariant c _ _ _) = filter (\b -> isPass b && contractMatches c b) [b | B b <- claims]
    definition (Invariant c _ _ _) = head $ filter
      (\b -> Pass == _cmode b && _cname b == c)
      [c' | C c' <- claims]
    contractMatches c b = c == (_contract b)
    isPass b = (_mode b) == Pass

    mkQuery (inv, constructor, behvs) = mkInit inv constructor : fmap (mkBehv inv constructor) behvs

mkInit :: Invariant -> Constructor -> Query
mkInit inv@(Invariant _ invConds _ invExp) constr@(Constructor _ _ (Interface _ decls) preconds _ initialStorage stateUpdates) = Inv (C constr) inv smt
  where
    localStorage = declareInitialStorage <$> initialStorage
    externalStorage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = encodeDecl <$> decls
    envs = declareEthEnv <$> (ethEnvFromConstructor constr)

    pres = (mkAssert Pre <$> preconds) <> (mkAssert Pre <$> invConds)
    updates = encodeUpdate <$> stateUpdates
    initialStorage' = encodeInitialStorage <$> initialStorage

    smt = SMTExp
      { _storage = localStorage <> externalStorage
      , _calldata = args
      , _environment = envs
      , _assertions = pres <> updates <> initialStorage' <> [mkAssert Post . Neg $ invExp]
      }

mkBehv :: Invariant -> Constructor -> Behaviour -> Query
mkBehv inv@(Invariant _ invConds invStorageBounds invExp) constr behv = Inv (B behv) inv smt
  where
    (Interface _ initDecls) = _cinterface constr
    (Interface _ behvDecls) = _interface behv

    -- storage locs mentioned in the invariant but not in the behaviour
    implicitStorageLocs = locsFromExp invExp \\ (getLoc <$> _stateUpdates behv)

    storage = concatMap (declareStorageLocation . getLoc) (_stateUpdates behv) <> (concatMap declareStorageLocation implicitStorageLocs)
    initArgs = encodeDecl <$> initDecls
    behvArgs = encodeDecl <$> behvDecls
    envs = declareEthEnv <$> (ethEnvFromBehaviour behv <> ethEnvFromConstructor constr)

    preInv = mkAssert Pre invExp
    postInv = mkAssert Post . Neg $ invExp
    preConds = mkAssert Pre <$> (_preconditions behv <> invConds <> invStorageBounds)
    updates = encodeUpdate <$> (_stateUpdates behv <> (Left <$> implicitStorageLocs))

    smt = SMTExp
      { _storage = storage
      , _calldata = initArgs <> behvArgs
      , _environment = envs
      , _assertions = preConds <> updates <> [preInv, postInv]
      }

runQuery :: SMTConfig -> Query -> IO (Query, SMTResult)
runQuery conf q = do
  res <- runSMT conf (getSMT q)
  pure (q, res)

runSMT :: SMTConfig -> SMTExp -> IO SMTResult
runSMT (SMTConfig solver timeout _ checkSat) e = do
  let input = intercalate "\n" [show e, if checkSat then "(check-sat)" else ""]
      args = case solver of
               Z3 -> ["-in", "-t:" <> show timeout]
               CVC4 -> ["--lang=smt", "--interactive", "--no-interactive-prompt", "--tlimit-per=" <> show timeout]
  (exitCode, stdout, _) <- readProcessWithExitCode (show solver) args input

  let output = filter (/= "") . lines $ stdout
      containsErrors = any (isPrefixOf "(error") output
  pure $ case exitCode of
    ExitFailure code -> Error code stdout
    ExitSuccess -> if containsErrors
                      then Error 0 stdout -- cvc4 returns exit code zero even if there are smt errors present... :/
                      else case last output of
                             "sat" -> Sat
                             "unsat" -> Unsat
                             "timeout" -> Unknown -- TODO: disambiguate
                             "unknown" -> Unknown
                             "" -> Unknown
                             _ -> Error 0 $ "Unable to parse SMT output: " <> stdout

--- SMT2 generation ---

encodeUpdate :: Either StorageLocation StorageUpdate -> SMT2
encodeUpdate (Left loc) = "(assert (= " <> nameFromLoc Pre loc <> " " <> nameFromLoc Post loc <> "))"
encodeUpdate (Right update) = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode item e = "(assert (= " <> expToSMT2 Post (TEntry item) <> " " <> expToSMT2 Pre e <> "))"

encodeInitialStorage :: StorageUpdate -> SMT2
encodeInitialStorage update = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode item e = "(assert (= " <> expToSMT2 Post (TEntry item) <> " " <> expToSMT2 Post e <> "))"

encodeDecl :: Decl -> SMT2
encodeDecl (Decl typ name) = constant name (metaType typ)

declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ defaultStore

-- declares a storage location that is created by the constructor, these locations have no prestate, so we declare a post var only
declareInitialStorage :: StorageUpdate -> SMT2
declareInitialStorage update = case getLoc . Right $ update of
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
    mkdirect item tp = constant (nameFromItem Post item) tp
    mkarray item ixs tp = array (nameFromItem Post item) ixs tp

-- declares a storage location that exists both in the pre state and the post state (i.e. anything except a loc created by a constructor claim)
declareStorageLocation :: StorageLocation -> [SMT2]
declareStorageLocation loc = case loc of
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
    mkdirect item tp = [constant (nameFromItem Pre item) tp, constant (nameFromItem Post item) tp]
    mkarray item ixs tp = [array (nameFromItem Pre item) ixs tp, array (nameFromItem Post item) ixs tp]

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
  Exp a b -> expToSMT2 w (simplifyExponentiation a b)
  LitInt a -> if a > 0 then show a else "(- " <> (show . negate $ a) <> ")"
  IntVar a -> a
  IntEnv a -> prettyEnv a

  -- bounds
  IntMin a -> expToSMT2 w (LitInt $ intmin a)
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

-- TODO: support any exponentiation expression where the RHS evaluates to a concrete value
simplifyExponentiation :: Exp Integer -> Exp Integer -> Exp Integer
simplifyExponentiation (LitInt a) (LitInt b) = (LitInt (a ^ b))
simplifyExponentiation _ _ = error "Internal Error: exponentiation is unsupported in SMT lib"

constant :: Id -> MType -> SMT2
constant name tp = "(declare-const " <> name <> " " <> (sType tp) <> ")"

mkAssert :: When -> Exp Bool -> SMT2
mkAssert w e = "(assert " <> expToSMT2 w e <> ")"

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

(@@) :: String -> String -> String
x @@ y = x <> "_" <> y

--- Util ---

isError :: SMTResult -> Bool
isError (Error {}) = True
isError _          = False

getTarget :: Query -> Exp Bool
getTarget (Postcondition _ t _) = t
getTarget (Inv _ (Invariant _ _ _ t) _) = t

getSMT :: Query -> SMTExp
getSMT (Postcondition _ _ e) = e
getSMT (Inv _ _ e) = e
