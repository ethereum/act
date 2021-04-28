{-# LANGUAGE GADTs #-}

module SMT (Solver(..), SMTConfig(..), Query(..), SMTResult(..), runSMT, runQuery, mkPostconditionQueries, mkInvariantQueries, getTarget, getSMT) where

import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.List
import Data.Containers.ListUtils (nubOrd)

import RefinedAst
import Extract
import Syntax (Id, EthEnv(..), Interface(..), Decl(..))
import Print (prettyEnv)
import Type (defaultStore, metaType)

import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))


--- ** Data ** ---


data Solver = Z3 | CVC4
  deriving Eq

instance Show Solver where
  show Z3 = "z3"
  show CVC4 = "cvc4"

data SMTConfig = SMTConfig
  { _solver :: Solver
  , _timeout :: Integer
  , _debug :: Bool
  }

type SMT2 = String

-- | Some expressions should be constructed over the poststate, and some over the prestate...
data When = Pre | Post

instance Show When where
  show Pre = "pre"
  show Post = "post"

-- | An SMTExp is a structured representation of an SMT Expression
--   The _storage, _calldata, and _environment fields hold variable declarations
--   The assertions field holds the various constraints that should be satisfied
data SMTExp = SMTExp
  { _storage :: [SMT2]
  , _calldata :: [SMT2]
  , _environment :: [SMT2]
  , _assertions :: [SMT2]
  }

instance Show SMTExp where
  show e = intercalate "\n" ["", storage, "", calldata, "", environment, "", assertions, ""]
    where
      storage = ";STORAGE:\n" <> intercalate "\n" (nubOrd $ _storage e)
      calldata = ";CALLDATA:\n" <> intercalate "\n" (nubOrd $ _calldata e)
      environment = ";ENVIRONMENT:\n" <> intercalate "\n" (nubOrd $ _environment e)
      assertions = ";ASSERTIONS:\n" <> intercalate "\n" (nubOrd $ _assertions e)

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


--- ** Analysis Passes ** ---


-- | For each postcondition in the claim we construct a query that:
--    - Asserts that the preconditions hold
--    - Asserts that storage has been updated according to the rewrites in the behaviour
--    - Asserts that the postcondition cannot be reached
--   If this query is unsatisfiable, then there exists no case where the postcondition can be violated.
mkPostconditionQueries :: Claim -> [Query]
mkPostconditionQueries (B behv@(Behaviour _ _ _ (Interface _ decls) preconds postconds stateUpdates _)) = mkQuery <$> postconds
  where
    -- declare vars
    storage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = declareArg <$> decls
    envs = declareEthEnv <$> ethEnvFromBehaviour behv

    -- constraints
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
    -- declare vars
    localStorage = declareInitialStorage <$> initialStorage
    externalStorage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = declareArg <$> decls
    envs = declareEthEnv <$> ethEnvFromConstructor constructor

    -- constraints
    pres = mkAssert Pre <$> preconds
    updates = encodeUpdate <$> stateUpdates
    initialStorage' = encodeInitialStorage <$> initialStorage

    mksmt e = SMTExp
      { _storage = localStorage <> externalStorage
      , _calldata = args
      , _environment = envs
      , _assertions = pres <> updates <> initialStorage' <> [mkAssert Pre . Neg $ e]
      }
    mkQuery e = Postcondition (C constructor) e (mksmt e)
mkPostconditionQueries _ = []

-- | For each invariant in the list of input claims, we first gather all the
--   specs relevant to that invariant (i.e. the constructor for that contract,
--   and all passing behaviours for that contract).
--
--   For the constructor we build a query that:
--     - Asserts that all preconditions hold
--     - Asserts that external storage has been updated according to the spec
--     - Asserts that internal storage values have the value given in the creates block
--     - Asserts that the invariant does not hold over the poststate
--
--   For the behaviours, we build a query that:
--     - Asserts that the invariant holds over the prestate
--     - Asserts that all preconditions hold
--     - Asserts that external storage has been updated according to the spec
--     - Asserts that internal storage values have the value given in the creates block
--     - Asserts that the invariant does not hold over the poststate
--
--   If all of the queries return `unsat` then we have an inductive proof that
--   the invariant holds for all possible contract states.
mkInvariantQueries :: [Claim] -> [Query]
mkInvariantQueries claims = concatMap mkQueries gathered
  where
    mkQueries (inv, constructor, behvs) = mkInit inv constructor : fmap (mkBehv inv constructor) behvs
    gathered = fmap (\inv -> (inv, getConstructor inv, getBehaviours inv)) [i | I i <- claims]

    getBehaviours (Invariant c _ _ _) = filter (matchBehaviour c) [b | B b <- claims]
    getConstructor (Invariant c _ _ _) = head $ filter (matchConstructor c) [c' | C c' <- claims]
    matchBehaviour contract behv = (_mode behv) == Pass && (_contract behv) == contract
    matchConstructor contract defn = _cmode defn == Pass && _cname defn == contract

    mkInit :: Invariant -> Constructor -> Query
    mkInit inv@(Invariant _ invConds _ invExp) constr@(Constructor _ _ (Interface _ decls) preconds _ initialStorage stateUpdates) = Inv (C constr) inv smt
      where
        -- declare vars
        localStorage = declareInitialStorage <$> initialStorage
        externalStorage = concatMap (declareStorageLocation . getLoc) stateUpdates
        args = declareArg <$> decls
        envs = declareEthEnv <$> (ethEnvFromConstructor constr)

        -- constraints
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

        -- declare vars
        invEnv = declareEthEnv <$> (ethEnvFromExp invExp)
        behvEnv = declareEthEnv <$> (ethEnvFromBehaviour behv)
        -- TODO: handle args with the same name...
        initArgs = declareArg <$> initDecls
        behvArgs = declareArg <$> behvDecls
        -- storage locs mentioned in the invariant but not in the behaviour
        implicitStorageLocs = Left <$> (locsFromExp invExp \\ (getLoc <$> _stateUpdates behv))
        storage = concatMap (declareStorageLocation . getLoc) (_stateUpdates behv <> implicitStorageLocs)

        -- constraints
        preInv = mkAssert Pre invExp
        postInv = mkAssert Post . Neg $ invExp
        preConds = mkAssert Pre <$> (_preconditions behv <> invConds <> invStorageBounds)
        updates = encodeUpdate <$> (_stateUpdates behv <> implicitStorageLocs)

        smt = SMTExp
          { _storage = storage
          , _calldata = initArgs <> behvArgs
          , _environment = invEnv <> behvEnv
          , _assertions = preConds <> updates <> [preInv, postInv]
          }


--- ** Solver Interaction ** ---


runQuery :: SMTConfig -> Query -> IO (Query, SMTResult)
runQuery conf q = do
  (exitCode, stdout, _) <- runSMT conf ((show . getSMT $ q) <> "\n(check-sat)")
  let output = filter (/= "") . lines $ stdout
      containsErrors = any (isPrefixOf "(error") output
      res = case exitCode of
        ExitFailure code -> Error code stdout
        ExitSuccess ->
          if containsErrors
          then Error 0 stdout -- cvc4 returns exit code zero even if there are errors
          else case output of
                 [] -> Unknown
                 l -> case last l of
                   "sat" -> Sat
                   "unsat" -> Unsat
                   "timeout" -> Unknown -- TODO: disambiguate
                   "unknown" -> Unknown
                   _ -> Error 0 $ "Unable to parse SMT output: " <> stdout
  pure (q, res)

runSMT :: SMTConfig -> SMT2 -> IO (ExitCode, String, String)
runSMT (SMTConfig solver timeout _) e = do
  let input = intercalate "\n" ["(set-logic ALL)", e]
      args = case solver of
               Z3 ->
                 [ "-in"
                 , "-t:" <> show timeout]
               CVC4 ->
                 [ "--lang=smt"
                 , "--interactive"
                 , "--no-interactive-prompt"
                 , "--tlimit=" <> show timeout]
  readProcessWithExitCode (show solver) args input


--- ** SMT2 generation ** ---


-- | encodes a storage update from a constructor creates block as an smt assertion
encodeInitialStorage :: StorageUpdate -> SMT2
encodeInitialStorage update = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode item e = "(assert (= " <> expToSMT2 Post (TEntry item) <> " " <> expToSMT2 Post e <> "))"

-- | declares a storage location that is created by the constructor, these
--   locations have no prestate, so we declare a post var only
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

-- | encodes a storge update rewrite as an smt assertion
encodeUpdate :: Either StorageLocation StorageUpdate -> SMT2
encodeUpdate (Left loc) = "(assert (= " <> nameFromLoc Pre loc <> " " <> nameFromLoc Post loc <> "))"
encodeUpdate (Right update) = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode item e = "(assert (= " <> expToSMT2 Post (TEntry item) <> " " <> expToSMT2 Pre e <> "))"

-- | declares a storage location that exists both in the pre state and the post
--   state (i.e. anything except a loc created by a constructor claim)
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

declareArg :: Decl -> SMT2
declareArg (Decl typ name) = constant name (metaType typ)

declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ defaultStore

returnExpToSMT2 :: When -> ReturnExp -> SMT2
returnExpToSMT2 w e = case e of
  ExpInt ei -> expToSMT2 w ei
  ExpBool eb -> expToSMT2 w eb
  ExpBytes ebs -> expToSMT2 w ebs

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
  LitInt a -> if a > 0
              then show a
              else "(- " <> (show . negate $ a) <> ")" -- cvc4 does not accept negative integer literals
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
    asSMT2 :: Exp a -> SMT2
    asSMT2 = expToSMT2 w

    unop :: String -> Exp a -> SMT2
    unop op a = "(" <> op <> " " <> asSMT2 a <> ")"

    binop :: String -> Exp a -> Exp b -> SMT2
    binop op a b = "(" <> op <> " " <> asSMT2 a <> " " <> asSMT2 b <> ")"

    triop :: String -> Exp a -> Exp b -> Exp c -> SMT2
    triop op a b c = "(" <> op <> " " <> asSMT2 a <> " " <> asSMT2 b <> " " <> asSMT2 c <> ")"

    select :: String -> NonEmpty ReturnExp -> SMT2
    select name (hd :| tl) = foldl' (\smt ix -> "(select " <> smt <> " " <> returnExpToSMT2 w ix <> ")") inner tl
      where
        inner = "(" <> "select" <> " " <> name <> " " <> returnExpToSMT2 w hd <> ")"

-- | SMT2 has no support for exponentiation, but we can do some preprocessing
--   if the RHS is concrete to provide some limited support for exponentiation
--   TODO: support any exponentiation expression where the RHS evaluates to a concrete value
simplifyExponentiation :: Exp Integer -> Exp Integer -> Exp Integer
simplifyExponentiation (LitInt a) (LitInt b) = LitInt (a ^ b)
simplifyExponentiation _ _ = error "Internal Error: exponentiation is unsupported in SMT lib"

constant :: Id -> MType -> SMT2
constant name tp = "(declare-const " <> name <> " " <> (sType tp) <> ")"

mkAssert :: When -> Exp Bool -> SMT2
mkAssert w e = "(assert " <> expToSMT2 w e <> ")"

array :: Id -> NonEmpty ReturnExp -> MType -> SMT2
array name (hd :| tl) ret = "(declare-const " <> name <> " (Array " <> sType' hd <> " " <> valueDecl tl <> "))"
  where
    valueDecl [] = sType ret
    valueDecl (h : t) = "(Array " <> sType' h <> " " <> valueDecl t <> ")"

sType :: MType -> SMT2
sType Integer = "Int"
sType Boolean = "Bool"
sType ByteStr = "String"

sType' :: ReturnExp -> SMT2
sType' (ExpInt {}) = "Int"
sType' (ExpBool {}) = "Bool"
sType' (ExpBytes {}) = "String"


--- ** Variable Names ** ---


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


--- ** Util ** ---


getTarget :: Query -> Exp Bool
getTarget (Postcondition _ t _) = t
getTarget (Inv _ (Invariant _ _ _ t) _) = t

getSMT :: Query -> SMTExp
getSMT (Postcondition _ _ e) = e
getSMT (Inv _ _ e) = e
