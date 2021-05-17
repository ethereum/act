{-# LANGUAGE GADTs #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}

module SMT (
  Solver(..),
  SMTConfig(..),
  Query(..),
  SMTResult(..),
  spawnSolver,
  stopSolver,
  sendLines,
  runQuery,
  mkPostconditionQueries,
  mkInvariantQueries,
  getTarget,
  getContract,
  isFail,
  isPass,
  ifExists,
  getBehvName,
  identifier,
  getSMT
) where

import Data.Containers.ListUtils (nubOrd)
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))
import Text.Regex.TDFA hiding (empty)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Control.Applicative ((<|>))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.List
import GHC.IO.Handle (Handle, hGetLine, hPutStr, hFlush)
import Data.ByteString.UTF8 (fromString)
import Control.Monad (when, void)

import RefinedAst
import Extract hiding (getContract)
import Syntax (Id, EthEnv(..), Interface(..), Decl(..))
import Print
import Type (defaultStore, metaType)


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

-- | Context needed to produce SMT from an act expression
--   - Id : The name of the interface from which calldata vars were extracted
--   - When : Whether or not storage references should refer to the pre or post state
data Ctx = Ctx Id When

data When = Pre | Post

instance Show When where
  show Pre = "pre"
  show Post = "post"

-- | An SMTExp is a structured representation of an SMT Expression
--   The _storage, _calldata, and _environment fields hold variable declarations
--   The _assertions field holds the various constraints that should be satisfied
data SMTExp = SMTExp
  { _storage :: [SMT2]
  , _calldata :: [SMT2]
  , _environment :: [SMT2]
  , _assertions :: [SMT2]
  }
  deriving (Show)

instance Pretty SMTExp where
  pretty e = vsep [storage, calldata, environment, assertions]
    where
      storage = text ";STORAGE:" <$$> (vsep . (fmap text) . nubOrd . _storage $ e) <> line
      calldata = text ";CALLDATA:" <$$> (vsep . (fmap text) . nubOrd . _calldata $ e) <> line
      environment = text ";ENVIRONMENT" <$$> (vsep . (fmap text) . nubOrd . _environment $ e) <> line
      assertions = text ";ASSERTIONS:" <$$> (vsep . (fmap text) . nubOrd . _assertions $ e) <> line

-- | A Query is a structured representation of an SMT query for an individual
--   expression, along with the metadata needed to extract a model from a satisfiable query
data Query
  = Postcondition Transition (Exp Bool) SMTExp
  | Inv Invariant (Constructor, SMTExp) [(Behaviour, SMTExp)]
  deriving (Show)

data SMTResult
  = Sat Model
  | Unsat
  | Unknown
  | Error Int String
  deriving (Show)

-- | An assignment of concrete values to symbolic variables structured in a way
--   to allow for easy pretty printing. The LHS of each pair is the symbolic
--   variable, and the RHS is the concrete value assigned to that variable in the
--   counterexample
data Model = Model
  { _mprestate :: [(StorageLocation, ReturnExp)]
  , _mpoststate :: [(StorageLocation, ReturnExp)]
  , _mcalldata :: (String, [(Decl, ReturnExp)])
  , _menvironment :: [(EthEnv, ReturnExp)]
  -- invariants always have access to the constructor context
  , _minitargs :: [(Decl, ReturnExp)]
  }
  deriving (Show)

instance Pretty Model where
  pretty (Model prestate poststate (ifaceName, args) environment initargs) =
    (underline . text $ "counterexample:") <$$> line
      <> (indent 2
        (    calldata'
        <$$> ifExists environment (line <> environment' <> line)
        <$$> storage
        <$$> ifExists initargs (line <> initargs')
        ))
    where
      calldata' = text "calldata:" <$$> line <> (indent 2 $ formatSig ifaceName args)
      environment' = text "environment:" <$$> line <> (indent 2 . vsep $ fmap formatEnvironment environment)
      storage = text "storage:" <$$> (indent 2 . vsep $ [ifExists prestate (line <> prestate'), poststate'])
      initargs' = text "constructor arguments:" <$$> line <> (indent 2 $ formatSig "constructor" initargs)

      prestate' = text "prestate:" <$$> line <> (indent 2 . vsep $ fmap formatStorage prestate) <> line
      poststate' = text "poststate:" <$$> line <> (indent 2 . vsep $ fmap formatStorage poststate)

      formatSig iface cd = text iface <> (encloseSep lparen rparen (text ", ") $ fmap formatCalldata cd)
      formatCalldata (Decl _ name, val) = text $ name <> " = " <> prettyReturnExp val
      formatEnvironment (env, val) = text $ prettyEnv env <> " = " <> prettyReturnExp val
      formatStorage (loc, val) = text $ prettyLocation loc <> " = " <> prettyReturnExp val

data SolverInstance = SolverInstance
  { _type :: Solver
  , _stdin :: Handle
  , _stdout :: Handle
  , _stderr :: Handle
  , _process :: ProcessHandle
  }


--- ** Analysis Passes ** ---


-- | For each postcondition in the claim we construct a query that:
--    - Asserts that the preconditions hold
--    - Asserts that storage has been updated according to the rewrites in the behaviour
--    - Asserts that the postcondition cannot be reached
--   If this query is unsatisfiable, then there exists no case where the postcondition can be violated.
mkPostconditionQueries :: Claim -> [Query]
mkPostconditionQueries (B behv@(Behaviour _ Pass _ (Interface ifaceName decls) preconds postconds stateUpdates _)) = mkQuery <$> postconds
  where
    -- declare vars
    storage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = declareArg ifaceName <$> decls
    envs = declareEthEnv <$> ethEnvFromBehaviour behv

    -- constraints
    pres = mkAssert (Ctx ifaceName Pre) <$> preconds
    updates = encodeUpdate ifaceName <$> stateUpdates

    mksmt e = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = envs
      , _assertions = [mkAssert (Ctx ifaceName Pre) . Neg $ e] <> pres <> updates
      }
    mkQuery e = Postcondition (Behv behv) e (mksmt e)
mkPostconditionQueries (C constructor@(Constructor _ Pass (Interface ifaceName decls) preconds postconds initialStorage stateUpdates)) = mkQuery <$> postconds
  where
    -- declare vars
    localStorage = declareInitialStorage <$> initialStorage
    externalStorage = concatMap (declareStorageLocation . getLoc) stateUpdates
    args = declareArg ifaceName <$> decls
    envs = declareEthEnv <$> ethEnvFromConstructor constructor

    -- constraints
    pres = mkAssert (Ctx ifaceName Pre) <$> preconds
    updates = encodeUpdate ifaceName <$> stateUpdates
    initialStorage' = encodeInitialStorage ifaceName <$> initialStorage

    mksmt e = SMTExp
      { _storage = localStorage <> externalStorage
      , _calldata = args
      , _environment = envs
      , _assertions = [mkAssert (Ctx ifaceName Pre) . Neg $ e] <> pres <> updates <> initialStorage'
      }
    mkQuery e = Postcondition (Ctor constructor) e (mksmt e)
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
--     - Asserts that storage has been updated according to the spec
--     - Asserts that the invariant does not hold over the poststate
--
--   If all of the queries return `unsat` then we have an inductive proof that
--   the invariant holds for all possible contract states.
mkInvariantQueries :: [Claim] -> [Query]
mkInvariantQueries claims = fmap mkQuery gathered
  where
    mkQuery (inv, ctor, behvs) = Inv inv (mkInit inv ctor) (fmap (mkBehv inv ctor) behvs)
    gathered = fmap (\inv -> (inv, getConstructor inv, getBehaviours inv)) [i | I i <- claims]

    getBehaviours (Invariant c _ _ _) = [b | B b <- claims, matchBehaviour c b]
    getConstructor (Invariant c _ _ _) = head [c' | C c' <- claims, matchConstructor c c']
    matchBehaviour contract behv = (_mode behv) == Pass && (_contract behv) == contract
    matchConstructor contract defn = _cmode defn == Pass && _cname defn == contract

    mkInit :: Invariant -> Constructor -> (Constructor, SMTExp)
    mkInit (Invariant _ invConds _ invExp) ctor@(Constructor _ _ (Interface ifaceName decls) preconds _ initialStorage stateUpdates) = (ctor, smt)
      where
        -- declare vars
        localStorage = declareInitialStorage <$> initialStorage
        externalStorage = concatMap (declareStorageLocation . getLoc) stateUpdates
        args = declareArg ifaceName <$> decls
        envs = declareEthEnv <$> ethEnvFromConstructor ctor

        -- constraints
        pres = (mkAssert (Ctx ifaceName Pre)) <$> (preconds <> invConds)
        updates = encodeUpdate ifaceName <$> stateUpdates
        initialStorage' = encodeInitialStorage ifaceName <$> initialStorage
        postInv = mkAssert (Ctx ifaceName Post) . Neg $ invExp

        smt = SMTExp
          { _storage = localStorage <> externalStorage
          , _calldata = args
          , _environment = envs
          , _assertions = postInv : pres <> updates <> initialStorage'
          }

    mkBehv :: Invariant -> Constructor -> Behaviour -> (Behaviour, SMTExp)
    mkBehv (Invariant _ invConds invStorageBounds invExp) ctor behv = (behv, smt)
      where
        (Interface ctorIface ctorDecls) = _cinterface ctor
        (Interface behvIface behvDecls) = _interface behv
        -- storage locs mentioned in the invariant but not in the behaviour
        implicitLocs = Left <$> (locsFromExp invExp \\ (getLoc <$> _stateUpdates behv))

        -- declare vars
        invEnv = declareEthEnv <$> ethEnvFromExp invExp
        behvEnv = declareEthEnv <$> ethEnvFromBehaviour behv
        initArgs = declareArg ctorIface <$> ctorDecls
        behvArgs = declareArg behvIface <$> behvDecls
        storage = concatMap (declareStorageLocation . getLoc) (_stateUpdates behv <> implicitLocs)

        -- constraints
        preInv = mkAssert (Ctx ctorIface Pre) invExp
        postInv = mkAssert (Ctx ctorIface Post) . Neg $ invExp
        behvConds = mkAssert (Ctx behvIface Pre) <$> (_preconditions behv)
        invConds' = mkAssert (Ctx ctorIface Pre) <$> (invConds <> invStorageBounds)
        implicitLocs' = encodeUpdate ctorIface <$> implicitLocs
        updates = encodeUpdate behvIface <$> (_stateUpdates behv)

        smt = SMTExp
          { _storage = storage
          , _calldata = initArgs <> behvArgs
          , _environment = invEnv <> behvEnv
          , _assertions = [preInv, postInv] <> behvConds <> invConds' <> implicitLocs' <> updates
          }


--- ** Solver Interaction ** ---


runQuery :: SolverInstance -> Query -> IO (Query, [SMTResult])
runQuery solver query@(Postcondition trans _ smt) = do
  res <- checkSat solver (getPostconditionModel trans) smt
  pure (query, [res])
runQuery solver query@(Inv (Invariant _ _ _ invExp) (ctor, ctorSMT) behvs) = do
  ctorRes <- runCtor
  behvRes <- mapM runBehv behvs
  pure (query, ctorRes : behvRes)
  where
    runCtor = checkSat solver (getInvariantModel invExp ctor Nothing) ctorSMT
    runBehv (b, smt) = checkSat solver (getInvariantModel invExp ctor (Just b)) smt

checkSat :: SolverInstance -> (SolverInstance -> IO Model) -> SMTExp -> IO SMTResult
checkSat solver modelFn smt = do
  err <- sendLines solver ("(reset)" : (lines . show . pretty $ smt))
  case err of
    Nothing -> do
      sat <- sendCommand solver "(check-sat)"
      case sat of
        "sat" -> Sat <$> modelFn solver
        "unsat" -> pure Unsat
        "timeout" -> pure Unknown
        "unknown" -> pure Unknown
        _ -> pure $ Error 0 $ "Unable to parse solver output: " <> sat
    Just msg -> do
      pure $ Error 0 msg

-- | Global settings applied directly after each solver instance is spawned
smtPreamble :: [SMT2]
smtPreamble = [ "(set-logic ALL)" ]

solverArgs :: SMTConfig -> [String]
solverArgs (SMTConfig solver timeout _) = case solver of
  Z3 ->
    [ "-in"
    , "-t:" <> show timeout]
  CVC4 ->
    [ "--lang=smt"
    , "--interactive"
    , "--no-interactive-prompt"
    , "--produce-models"
    , "--tlimit-per=" <> show timeout]

spawnSolver :: SMTConfig -> IO SolverInstance
spawnSolver config@(SMTConfig solver _ _) = do
  let cmd = (proc (show solver) (solverArgs config)) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
  (Just stdin, Just stdout, Just stderr, process) <- createProcess cmd
  let solverInstance = SolverInstance solver stdin stdout stderr process

  _ <- sendCommand solverInstance "(set-option :print-success true)"
  err <- sendLines solverInstance smtPreamble
  case err of
    Nothing -> pure solverInstance
    Just msg -> error $ "could not spawn solver: " <> msg

stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout stderr process) = cleanupProcess (Just stdin, Just stdout, Just stderr, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendLines :: SolverInstance -> [SMT2] -> IO (Maybe String)
sendLines solver smt = case smt of
  [] -> pure Nothing
  hd : tl -> do
    suc <- sendCommand solver hd
    if suc == "success"
       then sendLines solver tl
       else pure (Just suc)

sendCommand :: SolverInstance -> SMT2 -> IO String
sendCommand (SolverInstance solver stdin stdout _ _) cmd = do
  if null cmd || ";" `isPrefixOf` cmd then pure "success" -- blank lines and comments do not produce any output from the solver
  else do
    hPutStr stdin (cmd <> "\n")
    hFlush stdin
    hGetLine stdout


--- ** Model Extraction ** ---


getPostconditionModel :: Transition -> SolverInstance -> IO Model
getPostconditionModel (Ctor ctor) solver = do
  let locs = locsFromConstructor ctor
      env = ethEnvFromConstructor ctor
      Interface ifaceName decls = _cinterface ctor
  poststate <- mapM (getStorageValue solver (Ctx ifaceName Post)) locs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = []
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _menvironment = environment
    , _minitargs = []
    }
getPostconditionModel (Behv behv) solver = do
  let locs = locsFromBehaviour behv
      env = ethEnvFromBehaviour behv
      Interface ifaceName decls = _interface behv
  prestate <- mapM (getStorageValue solver (Ctx ifaceName Pre)) locs
  poststate <- mapM (getStorageValue solver (Ctx ifaceName Post)) locs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _menvironment = environment
    , _minitargs = []
    }

getInvariantModel :: Exp Bool -> Constructor -> Maybe Behaviour -> SolverInstance -> IO Model
getInvariantModel _ ctor Nothing solver = do
  let locs = locsFromConstructor ctor
      env = ethEnvFromConstructor ctor
      Interface ifaceName decls = _cinterface ctor
  poststate <- mapM (getStorageValue solver (Ctx ifaceName Post)) locs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = []
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _menvironment = environment
    , _minitargs = []
    }
getInvariantModel invExp ctor (Just behv) solver = do
  let locs = nub $ locsFromBehaviour behv <> locsFromExp invExp
      env = nub $ ethEnvFromBehaviour behv <> ethEnvFromExp invExp
      Interface behvIface behvDecls = _interface behv
      Interface ctorIface ctorDecls = _cinterface ctor
  -- TODO: v ugly to ignore the ifaceName here, but it's safe...
  prestate <- mapM (getStorageValue solver (Ctx "" Pre)) locs
  poststate <- mapM (getStorageValue solver (Ctx "" Post)) locs
  behvCalldata <- mapM (getCalldataValue solver behvIface) behvDecls
  ctorCalldata <- mapM (getCalldataValue solver ctorIface) ctorDecls
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (behvIface, behvCalldata)
    , _menvironment = environment
    , _minitargs = ctorCalldata
    }

parseSMTModel :: String -> String
parseSMTModel s = if length s0Caps == 1
                  then if length s1Caps == 1 then head s1Caps else head s0Caps
                  else ""
  where
    -- output should be in the form "((identifier value))" for positive integers / booleans / strings
    -- or "((identifier (value)))" for negative integers.

    -- The stage0 regex first extracts either value or (value), and then the
    -- stage1 regex is used to strip the additional brackets if required.
    stage0 = "\\`\\(\\([a-zA-Z0-9_]+ ([ \"\\(\\)a-zA-Z0-9_\\-]+)\\)\\)\\'"
    stage1 = "\\(([ a-zA-Z0-9_\\-]+)\\)"

    s0Caps = getCaptures s stage0
    s1Caps = getCaptures (head s0Caps) stage1

    getCaptures str regex = captures
      where (_, _, _, captures) = str =~ regex :: (String, String, String, [String])

getStorageValue :: SolverInstance -> Ctx -> StorageLocation -> IO (StorageLocation, ReturnExp)
getStorageValue solver ctx@(Ctx _ whn) loc = do
  let name = if isMapping loc
                then select ctx (nameFromLoc whn loc) (NonEmpty.fromList $ getContainerIxs loc)
                else nameFromLoc whn loc
  output <- getValue solver name
  -- TODO: handle errors here...
  let val = case loc of
              IntLoc {} -> parseIntModel output
              BoolLoc {} -> parseBoolModel output
              BytesLoc {} -> parseBytesModel output
  pure (loc, val)

getCalldataValue :: SolverInstance -> Id -> Decl -> IO (Decl, ReturnExp)
getCalldataValue solver ifaceName decl@(Decl tp _) = do
  output <- getValue solver $ nameFromDecl ifaceName decl
  let val = case metaType tp of
              Integer -> parseIntModel output
              Boolean -> parseBoolModel output
              ByteStr -> parseBytesModel output
  pure (decl, val)

getEnvironmentValue :: SolverInstance -> EthEnv -> IO (EthEnv, ReturnExp)
getEnvironmentValue solver env = do
  output <- getValue solver (prettyEnv env)
  let val = case lookup env defaultStore of
              Just Integer -> parseIntModel output
              Just Boolean -> parseBoolModel output
              Just ByteStr -> parseBytesModel output
              Nothing -> error $ "Internal Error: could not determine a type for" <> show env
  pure (env, val)

getValue :: SolverInstance -> String -> IO String
getValue solver name = sendCommand solver $ "(get-value (" <> name <> "))"

parseIntModel :: String -> ReturnExp
parseIntModel = ExpInt . LitInt . read . parseSMTModel

parseBoolModel :: String -> ReturnExp
parseBoolModel = ExpBool . LitBool . readBool . parseSMTModel
  where
    readBool "true" = True
    readBool "false" = False
    readBool s = error ("Could not parse " <> s <> "into a bool")

parseBytesModel :: String -> ReturnExp
parseBytesModel = ExpBytes . ByLit . fromString . parseSMTModel


--- ** SMT2 Generation ** ---


-- | encodes a storage update from a constructor creates block as an smt assertion
encodeInitialStorage :: Id -> StorageUpdate -> SMT2
encodeInitialStorage behvName update = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode :: TStorageItem a -> Exp a -> SMT2
    encode item e = "(assert (= " <> expToSMT2 (Ctx behvName Post) (TEntry item) <> " " <> expToSMT2 (Ctx behvName Pre) e <> "))"

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
encodeUpdate :: Id -> Either StorageLocation StorageUpdate -> SMT2
encodeUpdate _ (Left loc) = "(assert (= " <> nameFromLoc Pre loc <> " " <> nameFromLoc Post loc <> "))"
encodeUpdate behvName (Right update) = case update of
  IntUpdate item e -> encode item e
  BoolUpdate item e -> encode item e
  BytesUpdate item e -> encode item e
  where
    encode :: TStorageItem a -> Exp a -> SMT2
    encode item e = "(assert (= " <> expToSMT2 (Ctx behvName Post) (TEntry item) <> " " <> expToSMT2 (Ctx behvName Pre) e <> "))"

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

declareArg :: Id -> Decl -> SMT2
declareArg behvName d@(Decl typ _) = constant (nameFromDecl behvName d) (metaType typ)

declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ defaultStore

returnExpToSMT2 :: Ctx -> ReturnExp -> SMT2
returnExpToSMT2 c e = case e of
  ExpInt ei -> expToSMT2 c ei
  ExpBool eb -> expToSMT2 c eb
  ExpBytes ebs -> expToSMT2 c ebs

expToSMT2 :: Ctx -> Exp a -> SMT2
expToSMT2 ctx@(Ctx behvName whn) e = case e of

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
  BoolVar _ -> nameFromVar behvName e

  -- integers
  Add a b -> binop "+" a b
  Sub a b -> binop "-" a b
  Mul a b -> binop "*" a b
  Div a b -> binop "div" a b
  Mod a b -> binop "mod" a b
  Exp a b -> expToSMT2 ctx (simplifyExponentiation a b)
  LitInt a -> if a >= 0
              then show a
              else "(- " <> (show . negate $ a) <> ")" -- cvc4 does not accept negative integer literals
  IntVar _ -> nameFromVar behvName e
  IntEnv a -> prettyEnv a

  -- bounds
  IntMin a -> expToSMT2 ctx (LitInt $ intmin a)
  IntMax a -> show $ intmax a
  UIntMin a -> show $ uintmin a
  UIntMax a -> show $ uintmax a

  -- bytestrings
  Cat a b -> binop "str.++" a b
  Slice a start end -> triop "str.substr" a start (Sub end start)
  ByVar _ -> nameFromVar behvName e
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
    DirectInt {} -> nameFromItem whn item
    DirectBool {} -> nameFromItem whn item
    DirectBytes {} -> nameFromItem whn item
    MappedInt _ _ ixs -> select ctx (nameFromItem whn item) ixs
    MappedBool _ _ ixs -> select ctx (nameFromItem whn item) ixs
    MappedBytes _ _ ixs -> select ctx (nameFromItem whn item) ixs

  where
    asSMT2 :: Exp a -> SMT2
    asSMT2 = expToSMT2 ctx

    unop :: String -> Exp a -> SMT2
    unop op a = "(" <> op <> " " <> asSMT2 a <> ")"

    binop :: String -> Exp a -> Exp b -> SMT2
    binop op a b = "(" <> op <> " " <> asSMT2 a <> " " <> asSMT2 b <> ")"

    triop :: String -> Exp a -> Exp b -> Exp c -> SMT2
    triop op a b c = "(" <> op <> " " <> asSMT2 a <> " " <> asSMT2 b <> " " <> asSMT2 c <> ")"

-- | SMT2 has no support for exponentiation, but we can do some preprocessing
--   if the RHS is concrete to provide some limited support for exponentiation
simplifyExponentiation :: Exp Integer -> Exp Integer -> Exp Integer
simplifyExponentiation a b = fromMaybe (error "Internal Error: no support for symbolic exponents in SMT lib")
                             $   [LitInt $ a' ^ b'               | a' <- eval a, b' <- evalb]
                             <|> [foldr Mul (LitInt 1) (genericReplicate b' a) | b' <- evalb]
  where
    evalb = eval b

constant :: Id -> MType -> SMT2
constant name tp = "(declare-const " <> name <> " " <> (sType tp) <> ")"

mkAssert :: Ctx -> Exp Bool -> SMT2
mkAssert c e = "(assert " <> expToSMT2 c e <> ")"

array :: Id -> NonEmpty ReturnExp -> MType -> SMT2
array name (hd :| tl) ret = "(declare-const " <> name <> " (Array " <> sType' hd <> " " <> valueDecl tl <> "))"
  where
    valueDecl [] = sType ret
    valueDecl (h : t) = "(Array " <> sType' h <> " " <> valueDecl t <> ")"

select :: Ctx -> String -> NonEmpty ReturnExp -> SMT2
select ctx name (hd :| tl) = foldl' (\smt ix -> "(select " <> smt <> " " <> returnExpToSMT2 ctx ix <> ")") inner tl
  where
    inner = "(" <> "select" <> " " <> name <> " " <> returnExpToSMT2 ctx hd <> ")"


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
nameFromItem whn item = case item of
  DirectInt c name -> c @@ name @@ show whn
  DirectBool c name -> c @@ name @@ show whn
  DirectBytes c name -> c @@ name @@ show whn
  MappedInt c name _ -> c @@ name @@ show whn
  MappedBool c name _ -> c @@ name @@ show whn
  MappedBytes c name _ -> c @@ name @@ show whn

nameFromLoc :: When -> StorageLocation -> Id
nameFromLoc whn loc = case loc of
  IntLoc item -> nameFromItem whn item
  BoolLoc item -> nameFromItem whn item
  BytesLoc item -> nameFromItem whn item

nameFromDecl :: Id -> Decl -> Id
nameFromDecl ifaceName (Decl _ name) = ifaceName @@ name

nameFromVar :: Id -> Exp a -> Id
nameFromVar ifaceName (IntVar name) = ifaceName @@ name
nameFromVar ifaceName (ByVar name) = ifaceName @@ name
nameFromVar ifaceName (BoolVar name) = ifaceName @@ name
nameFromVar _ _ = error "Internal Error: cannot produce a variable name for non variable expressions"

(@@) :: String -> String -> String
x @@ y = x <> "_" <> y


--- ** Util ** ---


getTarget :: Query -> Exp Bool
getTarget (Postcondition _ t _) = t
getTarget (Inv (Invariant _ _ _ t) _ _) = t

getContract :: Query -> String
getContract (Postcondition (Ctor ctor) _ _) = _cname ctor
getContract (Postcondition (Behv behv) _ _) = _contract behv
getContract (Inv (Invariant c _ _ _) _ _) = c

isFail :: SMTResult -> Bool
isFail Unsat = False
isFail _ = True

isPass :: SMTResult -> Bool
isPass = not . isFail

getBehvName :: Query -> Doc
getBehvName (Postcondition (Ctor _) _ _) = (text "the") <+> (bold . text $ "constructor")
getBehvName (Postcondition (Behv behv) _ _) = (text "behaviour") <+> (bold . text $ _name behv)
getBehvName (Inv {}) = error "Internal Error: invariant queries do not have an associated behaviour"

identifier :: Query -> Doc
identifier (q@Inv {}) = (bold . text. prettyExp . getTarget $ q) <+> text "of" <+> (bold . text . getContract $ q)
identifier (q@Postcondition {}) = (bold . text. prettyExp . getTarget $ q) <+> text "in" <+> getBehvName q <+> text "of" <+> (bold . text . getContract $ q)

getSMT :: Query -> Doc
getSMT (Postcondition _ _ smt) = pretty smt
getSMT (Inv _ (_, csmt) behvs) = text "; constructor" <$$> sep' <$$> line <> pretty csmt <$$> vsep (fmap formatBehv behvs)
  where
    formatBehv (b, smt) = line <> text "; behaviour: " <> (text . _name $ b) <$$> sep' <$$> line <> pretty smt
    sep' = text "; -------------------------------"

ifExists :: Foldable t => t a -> Doc -> Doc
ifExists a b = if null a then empty else b
