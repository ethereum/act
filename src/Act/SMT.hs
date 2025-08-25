{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Act.SMT (
  Solver(..),
  SMTConfig(..),
  Query(..),
  SMTResult(..),
  SMTExp(..),
  SolverInstance(..),
  Model(..),
  CallDataValue(..),
  Transition(..),
  SMT2,
  spawnSolver,
  stopSolver,
  sendLines,
  runQuery,
  mkPostconditionQueries,
  mkPostconditionQueriesBehv,
  mkInvariantQueries,
  target,
  getQueryContract,
  isFail,
  isPass,
  ifExists,
  getBehvName,
  identifier,
  getSMT,
  checkSat,
  getPostconditionModel,
  mkAssert,
  declareStorage,
  declareArg,
  declareEthEnv,
  getStorageValue,
  getCalldataValue,
  getCalldataLocValue,
  getEnvironmentValue,
  declareInitialStorage,
  declareStorageLocation,
  declareCalldataLocation,
  encodeUpdate,
  encodeConstant,
) where

import Prelude hiding (GT, LT)

import Data.Containers.ListUtils (nubOrd)
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))
import Text.Regex.TDFA hiding (empty)
import Prettyprinter hiding (Doc)

import Control.Applicative ((<|>))
import Control.Monad.Reader
import Control.Monad

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.List
import GHC.IO.Handle (Handle, hGetLine, hPutStr, hFlush)
import Data.ByteString.UTF8 (fromString)

import Act.Syntax
import Act.Syntax.TypedExplicit hiding (array)

import Act.Print
import Act.Type (globalEnv)

import EVM.Solvers (Solver(..))

--- ** Data ** ---


data SMTConfig = SMTConfig
  { _solver :: Solver
  , _timeout :: Integer
  , _debug :: Bool
  }

type SMT2 = String

-- | The context is a `Reader` monad which allows us to read
-- the name of the current interface.
type Ctx = Reader Id

-- | Specify the name to use as the current interface when creating SMT-code.
withInterface :: Id -> Ctx SMT2 -> SMT2
withInterface = flip runReader

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

instance PrettyAnsi SMTExp where
  prettyAnsi e = vsep [storage, calldata, environment, assertions]
    where
      storage = pretty ";STORAGE:" <$$> (vsep . (fmap pretty) . nubOrd . _storage $ e) <> line
      calldata = pretty ";CALLDATA:" <$$> (vsep . (fmap pretty) . nubOrd . _calldata $ e) <> line
      environment = pretty ";ENVIRONMENT" <$$> (vsep . (fmap pretty) . nubOrd . _environment $ e) <> line
      assertions = pretty ";ASSERTIONS:" <$$> (vsep . (fmap pretty) . nubOrd . _assertions $ e) <> line

data Transition
  = Behv Behaviour
  | Ctor Constructor
  deriving (Show)

-- | A Query is a structured representation of an SMT query for an individual
--   expression, along with the metadata needed to extract a model from a satisfiable query
data Query
  = Postcondition Transition (Exp ABoolean) SMTExp
  | Inv Invariant (Constructor, SMTExp) [(Behaviour, SMTExp)]
  deriving (Show)

data SMTResult
  = Sat Model
  | Unsat
  | Unknown
  | Error Int String
  deriving (Show)

data CallDataValue = CallValue TypedExp | CallArray (NestedList () TypedExp)

instance Show CallDataValue where
  show (CallValue te) = show te
  show (CallArray te) = show te

-- | An assignment of concrete values to symbolic variables structured in a way
--   to allow for easy pretty printing. The LHS of each pair is the symbolic
--   variable, and the RHS is the concrete value assigned to that variable in the
--   counterexample
data Model = Model
  { _mprestate :: [(StorageLocation, TypedExp)]
  , _mpoststate :: [(StorageLocation, TypedExp)]
  , _mcalldata :: (String, [(Decl, CallDataValue)])
  , _mcalllocs :: [(CalldataLocation, TypedExp)]
  , _menvironment :: [(EthEnv, TypedExp)]
  -- invariants always have access to the constructor context
  , _minitargs :: [(Decl, CallDataValue)]
  }
  deriving (Show)

instance PrettyAnsi Model where
  prettyAnsi (Model prestate poststate (ifaceName, args) _ environment initargs) =
    (underline . pretty $ "counterexample:") <$$> line
      <> (indent 2
        (    calldata'
        <$$> ifExists environment (line <> environment' <> line)
        <$$> storage
        <$$> ifExists initargs (line <> initargs')
        ))
    where
      calldata' = pretty "calldata:" <$$> line <> (indent 2 $ formatSig ifaceName args)
      environment' = pretty "environment:" <$$> line <> (indent 2 . vsep $ fmap formatEnvironment environment)
      storage = pretty "storage:" <$$> (indent 2 . vsep $ [ifExists prestate (line <> prestate'),ifExists poststate (line <> poststate')])
      initargs' = pretty "constructor arguments:" <$$> line <> (indent 2 $ formatSig "constructor" initargs)

      prestate' = pretty "prestate:" <$$> line <> (indent 2 . vsep $ fmap formatStorage prestate) <> line
      poststate' = pretty "poststate:" <$$> line <> (indent 2 . vsep $ fmap formatStorage poststate)

      formatSig iface cd = pretty iface <> (encloseSep lparen rparen (pretty ", ") $ fmap formatCalldata cd)
      formatCalldata (Decl _ name, CallValue val) = pretty $ name <> " = " <> prettyTypedExp val
      formatCalldata (Decl _ name, CallArray arr) = pretty $ name <> " = " <> prettyNestedTypedExp arr
      formatEnvironment (env, val) = pretty $ prettyEnv env <> " = " <> prettyTypedExp val
      formatStorage (loc, val) = pretty $ prettyLocation loc <> " = " <> prettyTypedExp val


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
mkPostconditionQueries :: Act -> [Query]
mkPostconditionQueries (Act _ contr) = concatMap mkPostconditionQueriesContract contr
  where
    mkPostconditionQueriesContract (Contract constr behvs) =
      mkPostconditionQueriesConstr constr <> concatMap mkPostconditionQueriesBehv behvs

mkPostconditionQueriesBehv :: Behaviour -> [Query]
mkPostconditionQueriesBehv behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds postconds stateUpdates _) =
    mkQuery <$> postconds
  where
    -- declare vars
    activeSLocs = slocsFromBehaviour behv
    storage = concatMap declareStorageLocation activeSLocs
    activeCLocs = clocsFromBehaviour behv
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCLocs
    args = nub ifaceArgs <> activeArgs
    envs = declareEthEnv <$> ethEnvFromBehaviour behv
    constLocs = (nub activeSLocs) \\ (locFromUpdate <$> stateUpdates)

    -- constraints
    pres = mkAssert ifaceName <$> preconds <> caseconds
    updates = encodeUpdate ifaceName <$> stateUpdates
    constants = encodeConstant <$> constLocs

    mksmt e = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = envs
      , _assertions = [mkAssert ifaceName . Neg nowhere $ e] <> pres <> updates <> constants
      }
    mkQuery e = Postcondition (Behv behv) e (mksmt e)

mkPostconditionQueriesConstr :: Constructor -> [Query]
mkPostconditionQueriesConstr constructor@(Constructor _ (Interface ifaceName decls) _ preconds postconds _ initialStorage) = mkQuery <$> postconds
  where
    -- declare vars
    activeSLocs = slocsFromConstructor constructor
    localStorage = concatMap declareInitialStorage activeSLocs
    activeCLocs = clocsFromConstructor constructor
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = declareCalldataLocation ifaceName <$> activeCLocs
    args = nub ifaceArgs <> activeArgs
    envs = declareEthEnv <$> ethEnvFromConstructor constructor

    -- constraints
    pres = mkAssert ifaceName <$> preconds
    initialStorage' = encodeUpdate ifaceName <$> initialStorage

    mksmt e = SMTExp
      { _storage = localStorage
      , _calldata = args
      , _environment = envs
      , _assertions = [mkAssert ifaceName . Neg nowhere $ e] <> pres <> initialStorage'
      }
    mkQuery e = Postcondition (Ctor constructor) e (mksmt e)

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
mkInvariantQueries :: Act -> [Query]
mkInvariantQueries (Act _ contracts) = fmap mkQuery gathered
  where
    mkQuery (inv, ctor, behvs) = Inv inv (mkInit inv ctor) (fmap (mkBehv inv ctor) behvs)
    gathered = concatMap getInvariants contracts

    getInvariants (Contract (c@Constructor{..}) behvs) = fmap (, c, behvs) _invariants

    mkInit :: Invariant -> Constructor -> (Constructor, SMTExp)
    mkInit (Invariant _ invConds _ (PredTimed _ invPost)) ctor@(Constructor _ (Interface ifaceName decls) _ preconds _ _ initialStorage) = (ctor, smt)
      where
        -- declare vars
        activeSLocs = slocsFromConstructor ctor
        localStorage = concatMap declareInitialStorage activeSLocs
        activeCLocs = clocsFromConstructor ctor
        ifaceArgs = declareArg ifaceName <$> decls
        activeArgs = declareCalldataLocation ifaceName <$> activeCLocs
        args = nub ifaceArgs <> activeArgs
        envs = declareEthEnv <$> ethEnvFromConstructor ctor

        -- constraints
        pres = mkAssert ifaceName <$> preconds <> invConds
        initialStorage' = encodeUpdate ifaceName <$> initialStorage
        postInv = mkAssert ifaceName $ Neg nowhere invPost

        smt = SMTExp
          { _storage = localStorage
          , _calldata = args
          , _environment = envs
          , _assertions = postInv : pres <> initialStorage'
          }

    mkBehv :: Invariant -> Constructor -> Behaviour -> (Behaviour, SMTExp)
    mkBehv inv@(Invariant _ invConds invStorageBounds (PredTimed invPre invPost)) ctor behv = (behv, smt)
      where

        (Interface ctorIface ctorDecls) = _cinterface ctor
        (Interface behvIface behvDecls) = _interface behv


        -- declare vars
        invEnv = declareEthEnv <$> ethEnvFromExp invPre
        behvEnv = declareEthEnv <$> ethEnvFromBehaviour behv
        initArgs = declareArg ctorIface <$> ctorDecls
        behvArgs = declareArg behvIface <$> behvDecls
        activeCLocs = clocsFromInvariant inv
        activeArgs = declareCalldataLocation ctorIface <$> activeCLocs
        args = nub initArgs <> behvArgs <> activeArgs
        activeLocs = nub $ slocsFromBehaviour behv <> slocsFromInvariant inv
        -- storage locs that are mentioned but not explictly updated (i.e., constant)
        constLocs = ((nub activeLocs) \\ fmap locFromUpdate (_stateUpdates behv))

        storage = concatMap declareStorageLocation activeLocs

        -- constraints
        preInv = mkAssert ctorIface invPre
        postInv = mkAssert ctorIface . Neg nowhere $ invPost
        behvConds = mkAssert behvIface <$> _preconditions behv <> _caseconditions behv
        invConds' = mkAssert ctorIface <$> invConds <> invStorageBounds
        constants = encodeConstant <$> constLocs
        updates = encodeUpdate behvIface <$> _stateUpdates behv

        smt = SMTExp
          { _storage = storage
          , _calldata = args
          , _environment = invEnv <> behvEnv
          , _assertions = [preInv, postInv] <> behvConds <> invConds' <> constants <> updates
          }


--- ** Solver Interaction ** ---


-- | Checks the satisfiability of all smt expressions contained with a query, and returns the results as a list
runQuery :: SolverInstance -> Query -> IO (Query, [SMTResult])
runQuery solver query@(Postcondition trans _ smt) = do
  res <- checkSat solver (getPostconditionModel trans) smt
  pure (query, [res])
runQuery solver query@(Inv (Invariant _ _ _ predicate) (ctor, ctorSMT) behvs) = do
  ctorRes <- runCtor
  behvRes <- mapM runBehv behvs
  pure (query, ctorRes : behvRes)
  where
    runCtor = checkSat solver (getInvariantModel predicate ctor Nothing) ctorSMT
    runBehv (b, smt) = checkSat solver (getInvariantModel predicate ctor (Just b)) smt

-- | Checks the satisfiability of a single SMT expression, and uses the
-- provided `modelFn` to extract a model if the solver returns `sat`
checkSat :: SolverInstance -> (SolverInstance -> IO Model) -> SMTExp -> IO SMTResult
checkSat solver modelFn smt = do
  -- render (pretty smt)
  err <- sendLines solver ("(reset)" : (lines . show . prettyAnsi $ smt))
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

-- | Arguments used when spawing a solver instance
solverArgs :: SMTConfig -> [String]
solverArgs (SMTConfig solver timeout _) = case solver of
  Z3 ->
    [ "-in"
    , "-t:" <> show timeout]
  CVC5 ->
    [ "--lang=smt"
    , "--interactive"
    , "--produce-models"
    , "--print-success"
    , "--tlimit-per=" <> show timeout]
  _ -> error "Unsupported solver"

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
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

-- | Cleanly shutdown a running solver instnace
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

-- | Sends a single command to the solver, returns the first available line from the output buffer
sendCommand :: SolverInstance -> SMT2 -> IO String
sendCommand (SolverInstance _ stdin stdout _ _) cmd =
  if null cmd || ";" `isPrefixOf` cmd then pure "success" -- blank lines and comments do not produce any output from the solver
  else do
    hPutStr stdin (cmd <> "\n")
    hFlush stdin
    hGetLine stdout


--- ** Model Extraction ** ---


-- | Extracts an assignment of values for the variables in the given
-- transition. Assumes that a postcondition query for the given transition has
-- previously been checked in the given solver instance.
getPostconditionModel :: Transition -> SolverInstance -> IO Model
getPostconditionModel (Ctor ctor) solver = getCtorModel ctor solver
getPostconditionModel (Behv behv) solver = do
  let slocs = slocsFromBehaviour behv
      clocs = clocsFromBehaviour behv
      env = ethEnvFromBehaviour behv
      Interface ifaceName decls = _interface behv
  prestate <- mapM (getStorageValue solver ifaceName Pre) slocs
  poststate <- mapM (getStorageValue solver ifaceName Post) slocs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  calllocs <- mapM (getCalldataLocValue solver ifaceName) clocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = []
    }

-- | Extracts an assignment of values for the variables in the given
-- transition. Assumes that an invariant query has previously been checked
-- in the given solver instance.
getInvariantModel :: InvariantPred -> Constructor -> Maybe Behaviour -> SolverInstance -> IO Model
getInvariantModel _ ctor Nothing solver = getCtorModel ctor solver
getInvariantModel predicate ctor (Just behv) solver = do
  let slocs = nub $ slocsFromBehaviour behv <> slocsFromExp (invExp predicate)
      clocs = clocsFromExp (invExp predicate)
      env = nub $ ethEnvFromBehaviour behv <> ethEnvFromExp (invExp predicate)
      Interface behvIface behvDecls = _interface behv
      Interface ctorIface ctorDecls = _cinterface ctor
  -- TODO: v ugly to ignore the ifaceName here, but it's safe...
  prestate <- mapM (getStorageValue solver "" Pre) slocs
  poststate <- mapM (getStorageValue solver "" Post) slocs
  behvCalldata <- mapM (getCalldataValue solver behvIface) behvDecls
  ctorCalldata <- mapM (getCalldataValue solver ctorIface) ctorDecls
  calllocs <- mapM (getCalldataLocValue solver ctorIface) clocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (behvIface, behvCalldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = ctorCalldata
    }

-- | Extracts an assignment for the variables in the given constructor
getCtorModel :: Constructor -> SolverInstance -> IO Model
getCtorModel ctor solver = do
  let slocs = slocsFromConstructor ctor
      clocs = clocsFromConstructor ctor
      env = ethEnvFromConstructor ctor
      Interface ifaceName decls = _cinterface ctor
  poststate <- mapM (getStorageValue solver ifaceName Post) slocs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  calllocs <- mapM (getCalldataLocValue solver ifaceName) clocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = []
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = []
    }

-- | Gets a concrete value from the solver for the given storage location
getStorageValue :: SolverInstance -> Id -> When -> StorageLocation -> IO (StorageLocation, TypedExp)
getStorageValue solver ifaceName whn loc@(SLoc typ _) = do
  output <- getValue solver name
  -- TODO: handle errors here...
  pure (loc, parseModel typ output)
  where
    name = if isMapping loc || isArray loc
            then withInterface ifaceName
                 $ select
                    (nameFromSLoc whn loc)
                    (NonEmpty.fromList $ ixsFromLocation loc)
            else nameFromSLoc whn loc

getCalldataLocValue :: SolverInstance -> Id -> CalldataLocation -> IO (CalldataLocation, TypedExp)
getCalldataLocValue solver ifaceName call@(CLoc typ _) = do
  output <- getValue solver name
  -- TODO: handle errors here...
  pure (call, parseModel typ output)
  where
    name = if isCalldataMapping call || isCalldataArray call
            then withInterface ifaceName
                 $ select
                    (nameFromCLoc ifaceName call)
                    (NonEmpty.fromList $ ixsFromCalldata call)
            else nameFromCLoc ifaceName call

-- | Gets a concrete value from the solver for the given calldata argument
getCalldataValue :: SolverInstance -> Id -> Decl -> IO (Decl, CallDataValue)
getCalldataValue solver ifaceName decl@(Decl vt _) =
  case parseAbiArrayType vt of
    Just (baseTyp, shape) -> do
      array' <- traverse (getTypedExp baseTyp) (nestedListIdcs shape [])
      pure (decl, CallArray array')
    Nothing ->
      case vt of
        (FromAbi tp) -> do
          val <- parseModel tp <$> getValue solver (nameFromDecl ifaceName decl)
          pure (decl, CallValue val)
  where
    name idcs = selectIntIdx (nameFromDecl ifaceName decl) (NonEmpty.fromList idcs)

    -- Creates a nested list of the given shape
    -- (i.e. list sizes a each level, starting from the outer level),
    -- with a list of the element idcs at each leaf element
    --                Shape        -> Idcs  -> ...
    nestedListIdcs :: NonEmpty Int -> [Int] -> NestedList () [Int]
    nestedListIdcs (h:|[]) idcs = LeafList () $ map ((++) idcs . singleton)  [0..(h-1)]
    nestedListIdcs (h:|_) _ | h <= 0 = LeafList () []
    nestedListIdcs (h:|t) idcs = NodeList () $ NonEmpty.fromList $
      nestedListIdcs (NonEmpty.fromList t) <$> map ((++) idcs . singleton)  [0..(h-1)]

    getTypedExp :: AbiType -> [Int] -> IO TypedExp
    getTypedExp (FromAbi typ) idcs =
      parseModel typ <$> getValue solver (name idcs)

-- | Gets a concrete value from the solver for the given environment variable
getEnvironmentValue :: SolverInstance -> EthEnv -> IO (EthEnv, TypedExp)
getEnvironmentValue solver env = do
  output <- getValue solver (prettyEnv env)
  let val = case lookup env globalEnv of
        Just (FromAct typ) -> parseModel typ output
        _ -> error $ "Internal Error: could not determine a type for" <> show env
  pure (env, val)

-- | Calls `(get-value)` for the given identifier in the given solver instance.
getValue :: SolverInstance -> String -> IO String
getValue solver name = sendCommand solver $ "(get-value (" <> name <> "))"

-- | Parse the result of a call to getValue as the supplied type.
parseModel :: SType a -> String -> TypedExp
parseModel = \case
  SInteger -> _TExp . LitInt  nowhere . read       . parseSMTModel
  SBoolean -> _TExp . LitBool nowhere . readBool   . parseSMTModel
  SByteStr -> _TExp . ByLit   nowhere . fromString . parseSMTModel
  where
    readBool "true" = True
    readBool "false" = False
    readBool s = error ("Could not parse " <> s <> "into a bool")

-- | Extracts a string representation of the value in the output from a call to `(get-value)`
parseSMTModel :: String -> String
parseSMTModel s
  | length capNoPar == 1 = head capNoPar
  | length capPar == 1 = head capPar
  | otherwise = ""
  where
    -- output should be in the form "((reference value))" for positive integers / booleans / strings
    -- or "((reference (value)))" for negative integers.
    -- where reference is either an identifier or a sequence of nested selections
    noPar = "\\`\\(\\([ \\(\\)a-zA-Z0-9_\\+\\*\\=\\<\\>\\.\\-]+ ([ \"a-zA-Z0-9_\\-]+)\\)\\)\\'" :: String
    par = "\\`\\(\\([ \\(\\)a-zA-Z0-9_\\+\\*\\=\\<\\>\\.\\-]+ \\(([ \"a-zA-Z0-9_\\-]+)\\)\\)\\)\\'" :: String

    capNoPar = getCaptures s noPar
    capPar = getCaptures s par

    getCaptures :: String -> String -> [String]
    getCaptures str regex = captures
      where (_, _, _, captures) = str =~ regex :: (String, String, String, [String])


--- ** SMT2 Generation ** ---


-- | encodes a storage update rewrite as an smt assertion
encodeUpdate :: Id -> StorageUpdate -> SMT2
encodeUpdate behvName (Update _ item expr) =
  let
    postentry  = withInterface behvName $ expToSMT2 (VarRef nowhere Post SStorage item)
    expression = withInterface behvName $ expToSMT2 expr
  in "(assert (= " <> postentry <> " " <> expression <> "))"

encodeConstant :: StorageLocation -> SMT2
encodeConstant loc = "(assert (= " <> nameFromSLoc Pre loc <> " " <> nameFromSLoc Post loc <> "))"

-- | declares a storage location with the given timing
-- TODO: support nested references i.e. array field
declareStorage :: [When] -> StorageLocation -> [SMT2]
declareStorage times (SLoc _ item@(Item _ _ ref)) = declareRef ref
  where
    declareRef (SVar _ _ _) = (\t -> constant (nameFromSItem t item) (itemType item) ) <$> times
    declareRef (SArray _ _ _ ixs) = (\t -> array (nameFromSItem t item) (length ixs) (itemType item)) <$> times
    declareRef (SMapping _ _ _ ixs) = (\t -> mappingArray (nameFromSItem t item) ixs (itemType item)) <$> times
    declareRef (SField _ ref' _ _) = declareRef ref'

-- | declares a calldata location
declareCalldataLocation :: Id -> CalldataLocation -> SMT2
declareCalldataLocation behvName (CLoc _ item@(Item _ _ ref)) = declareRef ref
  where
    declareRef (CVar {}) = constant (nameFromCItem behvName item) (itemType item)
    declareRef (SArray _ _ _ ixs) = array (nameFromCItem behvName item) (length ixs) (itemType item)
    declareRef (SMapping _ _ _ ixs) = mappingArray (nameFromCItem behvName item) ixs (itemType item)
    declareRef (SField _ ref' _ _) = declareRef ref'


-- | declares a storage location that is created by the constructor, these
--   locations have no prestate, so we declare a post var only
declareInitialStorage :: StorageLocation -> [SMT2]
declareInitialStorage loc = declareStorage [Post] loc

-- | declares a storage location that exists both in the pre state and the post
--   state (i.e. anything except a loc created by a constructor claim)
declareStorageLocation :: StorageLocation -> [SMT2]
declareStorageLocation item = declareStorage [Pre, Post] item

-- | produces an SMT2 expression declaring the given decl as a symbolic constant
declareArg :: Id -> Decl -> SMT2
declareArg behvName d@(Decl typ _) =
  case parseAbiArrayType typ of
    Just (baseTyp, shape) ->
       array (nameFromDecl behvName d) (length shape) (fromAbiType baseTyp)
    Nothing -> constant (nameFromDecl behvName d) (fromAbiType typ)

-- | produces an SMT2 expression declaring the given EthEnv as a symbolic constant
declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ globalEnv

-- | encodes a typed expression as an smt2 expression
typedExpToSMT2 :: TypedExp -> Ctx SMT2
typedExpToSMT2 (TExp _ e) = expToSMT2 e

-- | encodes the given Exp as an smt2 expression
expToSMT2 :: Exp a -> Ctx SMT2
expToSMT2 expr = case expr of
  -- booleans
  And _ a b -> binop "and" a b
  Or _ a b -> binop "or" a b
  Impl _ a b -> binop "=>" a b
  Neg _ a -> unop "not" a
  LT _ a b -> binop "<" a b
  LEQ _ a b -> binop "<=" a b
  GEQ _ a b -> binop ">=" a b
  GT _ a b -> binop ">" a b
  LitBool _ a -> pure $ if a then "true" else "false"

  -- integers
  Add _ a b -> binop "+" a b
  Sub _ a b -> binop "-" a b
  Mul _ a b -> binop "*" a b
  Div _ a b -> binop "div" a b
  Mod _ a b -> binop "mod" a b
  Exp _ a b -> expToSMT2 $ simplifyExponentiation a b
  LitInt _ a -> pure $ if a >= 0
                      then show a
                      else "(- " <> (show . negate $ a) <> ")" -- cvc4 does not accept negative integer literals
  IntEnv _ a -> pure $ prettyEnv a

  -- bounds
  IntMin p a -> expToSMT2 . LitInt p $ intmin a
  IntMax _ a -> pure . show $ intmax a
  UIntMin _ a -> pure . show $ uintmin a
  UIntMax _ a -> pure . show $ uintmax a
  InRange _ t e -> expToSMT2 (bound t e)

  -- bytestrings
  Cat _ a b -> binop "str.++" a b
  Slice p a start end -> triop "str.substr" a start (Sub p end start)
  ByStr _ a -> pure a
  ByLit _ a -> pure $ show a
  ByEnv _ a -> pure $ prettyEnv a

  -- contracts
  Create _ _ _ -> pure "0" -- TODO just a dummy address for now
  -- polymorphic
  Eq _ _ a b -> binop "=" a b
  NEq p s a b -> unop "not" (Eq p s a b)
  ITE _ a b c -> triop "ite" a b c
  VarRef _ whn _ item -> entry whn item
  where
    unop :: String -> Exp a -> Ctx SMT2
    unop op a = ["(" <> op <> " " <> a' <> ")" | a' <- expToSMT2 a]

    binop :: String -> Exp a -> Exp b -> Ctx SMT2
    binop op a b = ["(" <> op <> " " <> a' <> " " <> b' <> ")"
                      | a' <- expToSMT2 a, b' <- expToSMT2 b]

    triop :: String -> Exp a -> Exp b -> Exp c -> Ctx SMT2
    triop op a b c = ["(" <> op <> " " <> a' <> " " <> b' <> " " <> c' <> ")"
                        | a' <- expToSMT2 a, b' <- expToSMT2 b, c' <- expToSMT2 c]

    entry :: When -> TItem k a -> Ctx SMT2
    entry whn item = case ixsFromItem item of
      []       -> nameFromItem whn item
      (ix:ixs) -> do
        name <- nameFromItem whn item
        select name (ix :| ixs)

-- | SMT2 has no support for exponentiation, but we can do some preprocessing
--   if the RHS is concrete to provide some limited support for exponentiation
simplifyExponentiation :: Exp AInteger -> Exp AInteger -> Exp AInteger
simplifyExponentiation a b = fromMaybe (error "Internal Error: no support for symbolic exponents in SMT lib")
                           $ [LitInt nowhere $ a' ^ b'                         | a' <- eval a, b' <- evalb]
                         <|> [foldr (Mul nowhere) (LitInt nowhere 1) (genericReplicate b' a) | b' <- evalb]
  where
    evalb = eval b -- TODO is this actually necessary to prevent double evaluation?

-- | declare a constant in smt2
constant :: Id -> ActType -> SMT2
constant name tp = "(declare-const " <> name <> " " <> sType tp <> ")"

-- | encode the given boolean expression as an assertion in smt2
mkAssert :: Id -> Exp ABoolean -> SMT2
mkAssert c e = "(assert " <> withInterface c (expToSMT2 e) <> ")"

-- | declare a (potentially nested) array in smt2
array :: Id -> Int -> ActType -> SMT2
array name argNum ret = "(declare-const " <> name <> valueDecl argNum <> ")"
  where
    valueDecl n | n <= 0 = sType ret
    valueDecl n = "(Array " <> sType AInteger <> " " <> valueDecl (n-1) <> ")"

-- | declare a (potentially nested) array representing a mapping in smt2
mappingArray :: Id -> [TypedExp] -> ActType -> SMT2
mappingArray name args ret = "(declare-const " <> name <> valueDecl args <> ")"
  where
    valueDecl [] = sType ret
    valueDecl (h : t) = "(Array " <> sType' h <> " " <> valueDecl t <> ")"

-- | encode an array lookup with Integer indices in smt2
selectIntIdx :: String -> NonEmpty Int -> SMT2
selectIntIdx name (hd :| tl) = do
  foldl (\smt ix -> "(select " <> smt <> " " <> show ix <> ")" ) ("(select " <> name <> " " <> show hd <> ")") tl

-- | encode an indexed lookup in smt2
select :: String -> NonEmpty TypedExp -> Ctx SMT2
select name (hd :| tl) = do
  inner <- ["(select " <> name <> " " <> hd' <> ")" | hd' <- typedExpToSMT2 hd]
  foldM (\smt ix -> ["(select " <> smt <> " " <> ix' <> ")" | ix' <- typedExpToSMT2 ix]) inner tl

-- | act -> smt2 type translation
sType :: ActType -> SMT2
sType AInteger = "Int"
sType ABoolean = "Bool"
sType AByteStr = "String"

-- | act -> smt2 type translation
sType' :: TypedExp -> SMT2
sType' (TExp t _) = sType $ actType t

--- ** Variable Names ** ---

-- Construct the smt2 variable name for a given storage item
nameFromSItem :: When -> TItem a Storage -> Id
nameFromSItem whn (Item _ _ ref) = nameFromSRef whn ref

nameFromSRef :: When -> Ref Storage -> Id
nameFromSRef whn (SVar _ c name) = c @@ name @@ show whn
nameFromSRef whn (SArray _ e _ _) = nameFromSRef whn e
nameFromSRef whn (SMapping _ e _ _) = nameFromSRef whn e
nameFromSRef whn (SField _ ref c x) = nameFromSRef whn ref @@ c @@ x

nameFromCItem :: Id -> TItem a Calldata -> Id
nameFromCItem behvName (Item _ _ ref) = nameFromCRef behvName ref

nameFromCRef :: Id -> Ref Calldata -> Id
nameFromCRef behvName (CVar _ _ name) = behvName @@ name
nameFromCRef behvName (SArray _ e _ _) = nameFromCRef behvName e
nameFromCRef behvName (SMapping _ e _ _) = nameFromCRef behvName e
nameFromCRef behvName (SField _ ref c x) = nameFromCRef behvName ref @@ c @@ x

nameFromItem ::When ->  TItem k a -> Ctx Id
nameFromItem whn (Item _ _ ref) = nameFromRef whn ref

nameFromRef :: When -> Ref k -> Ctx Id
nameFromRef _ (CVar _ _ name) = nameFromVarId name
nameFromRef whn (SVar _ c name) = pure $ c @@ name @@ show whn
nameFromRef whn (SArray _ e _ _) = nameFromRef whn e
nameFromRef whn (SMapping _ e _ _) = nameFromRef whn e
nameFromRef whn (SField _ ref c x) = do
  name <- nameFromRef whn ref
  pure $ name @@ c @@ x


-- Construct the smt2 variable name for a given storage location
nameFromSLoc :: When -> StorageLocation -> Id
nameFromSLoc whn (SLoc _ item) = nameFromSItem whn item

nameFromCLoc :: Id -> CalldataLocation -> Id
nameFromCLoc behvName (CLoc _ item) = nameFromCItem behvName item

-- Construct the smt2 variable name for a given decl
nameFromDecl :: Id -> Decl -> Id
nameFromDecl ifaceName (Decl _ name) = ifaceName @@ name

-- Construct the smt2 variable name for a given act variable
nameFromVarId :: Id -> Ctx Id
nameFromVarId name = [behvName @@ name | behvName <- ask]

(@@) :: String -> String -> String
x @@ y = x <> "_" <> y

--- ** Util ** ---

-- | The target expression of a query.
target :: Query -> Exp ABoolean
target (Postcondition _ e _)         = e
target (Inv (Invariant _ _ _ e) _ _) = invExp e

getQueryContract :: Query -> Id
getQueryContract (Postcondition (Ctor ctor) _ _) = _cname ctor
getQueryContract (Postcondition (Behv behv) _ _) = _contract behv
getQueryContract (Inv (Invariant c _ _ _) _ _) = c

isFail :: SMTResult -> Bool
isFail Unsat = False
isFail _ = True

isPass :: SMTResult -> Bool
isPass = not . isFail

getBehvName :: Query -> DocAnsi
getBehvName (Postcondition (Ctor _) _ _) = (pretty "the") <+> (bold . pretty $ "constructor")
getBehvName (Postcondition (Behv behv) _ _) = (pretty "behaviour") <+> (bold . pretty $ _name behv)
getBehvName (Inv {}) = error "Internal Error: invariant queries do not have an associated behaviour"

identifier :: Query -> DocAnsi
identifier q@(Inv (Invariant _ _ _ e) _ _)    = (bold . pretty . prettyInvPred $ e) <+> pretty "of" <+> (bold . pretty . getQueryContract $ q)
identifier q@Postcondition {} = (bold . pretty . prettyExp . target $ q) <+> pretty "in" <+> getBehvName q <+> pretty "of" <+> (bold . pretty . getQueryContract $ q)

getSMT :: Query -> DocAnsi
getSMT (Postcondition _ _ smt) = prettyAnsi smt
getSMT (Inv _ (_, csmt) behvs) = pretty "; constructor" <$$> sep' <$$> line <> prettyAnsi csmt <$$> vsep (fmap formatBehv behvs)
  where
    formatBehv (b, smt) = line <> pretty "; behaviour: " <> (pretty . _name $ b) <$$> sep' <$$> line <> prettyAnsi smt
    sep' = pretty "; -------------------------------"

ifExists :: Foldable t => t a -> DocAnsi -> DocAnsi
ifExists a b = if null a then emptyDoc else b
