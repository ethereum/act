{-# LANGUAGE GADTs #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ExistentialQuantification #-}

module SMT where
--module SMT (
  --Solver(..),
  --SMTConfig(..),
  --Query(..),
  --SMTResult(..),
  --spawnSolver,
  --stopSolver,
  --sendLines,
  --runQuery,
  --mkPostconditionQueries,
  --mkInvariantQueries,
  --getTarget,
  --getSMT) where

import Data.Containers.ListUtils (nubOrd)
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))
import EVM.ABI (AbiType(..))

import Control.Applicative ((<|>))
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.List
import GHC.IO.Handle (Handle, hGetLine, hPutStr, hFlush)
import Data.ByteString.UTF8 (fromString)

import RefinedAst
import Extract
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

instance Show SMTExp where
  show e = unlines [storage, calldata, environment, assertions]
    where
      storage = unlines $ ";STORAGE:" : (nubOrd $ _storage e)
      calldata = unlines $ ";CALLDATA:" : (nubOrd $ _calldata e)
      environment = unlines $ ";ENVIRONMENT:" : (nubOrd $ _environment e)
      assertions = unlines $ ";ASSERTIONS:" : (nubOrd $ _assertions e)

-- | A Query is a structured representation of an SMT query for an individual
--   expression, along with the metadata needed to extract a model from a satisfiable query
data Query
  = Postcondition Claim (Exp Bool) SMTExp
  | Inv Claim Invariant SMTExp
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
  , _minitargs :: [(ReturnExp, ReturnExp)]
  , _minitenv :: [(Decl, ReturnExp)]
  }

instance Show Model where
  show (Model prestate poststate (ifaceName, args) environment initargs initenv) = unlines $
    ["", "counterexample:"]
      <> indent 2
        (  calldata'
        <> ifExists environment environment'
        <> storage
        )
    where
      calldata' = (header "calldata:") <> (indent 2 [ifaceName <> "(" <> (intercalate ", " $ fmap formatCalldata args) <> ")"])
      environment' = (header "environment:") <> (indent 2 $ fmap formatEnvironment environment)
      storage = ["", "storage:"] <> (indent 2 $ (ifExists prestate prestate') <> poststate')

      prestate' = (header "prestate:") <> (indent 2 $ fmap formatStorage poststate)
      poststate' = (header "poststate:") <> (indent 2 $ fmap formatStorage poststate)

      formatCalldata ((Decl _ name), val) = name <> " : " <> prettyReturnExp val
      formatEnvironment (env, val) = prettyEnv env <> " : " <> prettyReturnExp val
      formatStorage (loc, val) = prettyLocation loc <> " : " <> prettyReturnExp val

      ifExists a b = if null a then [] else b

      header s = ["", s, ""]


indent :: Int -> [String] -> [String]
indent n text = ((replicate n ' ') <>) <$> text

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
mkPostconditionQueries (B behv@(Behaviour _ _ _ (Interface ifaceName decls) preconds postconds stateUpdates _)) = mkQuery <$> postconds
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
    mkQuery e = Postcondition (B behv) e (mksmt e)
mkPostconditionQueries (C constructor@(Constructor _ _ (Interface ifaceName decls) preconds postconds initialStorage stateUpdates)) = mkQuery <$> postconds
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
--     - Asserts that storage has been updated according to the spec
--     - Asserts that the invariant does not hold over the poststate
--
--   If all of the queries return `unsat` then we have an inductive proof that
--   the invariant holds for all possible contract states.
mkInvariantQueries :: [Claim] -> [Query]
mkInvariantQueries claims = concatMap mkQueries gathered
  where
    mkQueries (inv, constructor, behvs) = mkInit inv constructor : fmap (mkBehv inv constructor) behvs
    gathered = fmap (\inv -> (inv, getConstructor inv, getBehaviours inv)) [i | I i <- claims]

    getBehaviours (Invariant c _ _ _) = [b | B b <- claims, matchBehaviour c b]
    getConstructor (Invariant c _ _ _) = head [c' | C c' <- claims, matchConstructor c c']
    matchBehaviour contract behv = (_mode behv) == Pass && (_contract behv) == contract
    matchConstructor contract defn = _cmode defn == Pass && _cname defn == contract

    mkInit :: Invariant -> Constructor -> Query
    mkInit inv@(Invariant _ invConds _ invExp) ctor@(Constructor _ _ (Interface ifaceName decls) preconds _ initialStorage stateUpdates) = Inv (C ctor) inv smt
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

    mkBehv :: Invariant -> Constructor -> Behaviour -> Query
    mkBehv inv@(Invariant _ invConds invStorageBounds invExp) ctor behv = Inv (B behv) inv smt
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


getModel :: SolverInstance -> Query -> IO Model
getModel solver (Postcondition (C ctor) _ _) = do
  let locs = locsFromConstructor ctor
      env = ethEnvFromConstructor ctor
      (Interface ifaceName decls) = _cinterface ctor
  poststate <- mapM (getStorageValue solver (Ctx ifaceName Post)) locs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = []
    , _mpoststate = nub poststate -- TODO: dedup in extract
    , _mcalldata = (ifaceName, nub calldata)
    , _menvironment = nub environment
    , _minitargs = []
    , _minitenv = []
    }
getModel solver (Postcondition (B behv) _ _) = do
  let locs = locsFromBehaviour behv
      env = ethEnvFromBehaviour behv
      (Interface ifaceName decls) = _interface behv
  prestate <- mapM (getStorageValue solver (Ctx ifaceName Pre)) locs
  poststate <- mapM (getStorageValue solver (Ctx ifaceName Post)) locs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = nub prestate
    , _mpoststate = nub poststate
    , _mcalldata = (ifaceName, nub calldata)
    , _menvironment = nub environment
    , _minitargs = []
    , _minitenv = []
    }
getModel _ _ = undefined

-- output should be in the form "((identifier value))"
-- we therefore return the non-whitespace group before the last two ')' chars
-- TODO: this could probably be faster with a regex
parseSMTModel :: String -> String
parseSMTModel s = init . init $ last (words s)

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
  let name = nameFromDecl ifaceName decl
  output <- getValue solver name
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
              Nothing -> error "whoops" -- TODO: handle errors properly...
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

runQuery :: SolverInstance -> Query -> IO (Query, SMTResult)
runQuery solver query = do
  err <- sendLines solver ("(reset)" : (lines . show . getSMT $ query))
  case err of
    Nothing -> do
      sat <- sendCommand solver "(check-sat)"
      case sat of
        "sat" -> do
          model <- getModel solver query
          pure (query, Sat model)
        "unsat" -> pure (query, Unsat)
        "timeout" -> pure (query, Unknown) -- TODO: disambiguate?
        "unknown" -> pure (query, Unknown)
        _ -> pure (query, Error 0 $ "Unable to parse solver output: " <> sat)
    Just msg -> do
      pure (query, Error 0 msg)

smtPreamble :: [SMT2]
smtPreamble =
  [ "(set-logic ALL)"
  , "(set-option :produce-models true)"
  ]

solverArgs :: SMTConfig -> [String]
solverArgs (SMTConfig solver timeout _) = case solver of
  Z3 ->
    [ "-in"
    , "-t:" <> show timeout]
  CVC4 ->
    [ "--lang=smt"
    , "--interactive"
    , "--no-interactive-prompt"
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
  if (cmd == "") || (";" `isPrefixOf` cmd) then pure "success" -- blank lines and comments do not produce any output from the solver
  else do
    hPutStr stdin (cmd <> "\n")
    hFlush stdin
    case solver of
      Z3 -> hGetLine stdout
      CVC4 -> do
        _ <- hGetLine stdout -- cvc4 echos back each input line as part of the output
        hGetLine stdout


--- ** SMT2 generation ** ---


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
getTarget (Inv _ (Invariant _ _ _ t) _) = t

getSMT :: Query -> SMTExp
getSMT (Postcondition _ _ e) = e
getSMT (Inv _ _ e) = e

getContract :: Query -> String
getContract (Postcondition (C ctor) _ _) = _cname ctor
getContract (Postcondition (B behv) _ _) = _contract behv
getContract (Inv (C ctor) _ _) = _cname ctor
getContract (Inv (B behv) _ _) = _contract behv
getContract _ = error "Internal Error: invalid query" -- TODO: refine types
