{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
import Data.List
import Data.Aeson hiding (Bool)
import Data.Aeson.Types hiding (Bool)
import GHC.Generics
import System.Environment ( getArgs )
import System.Exit ( exitFailure )
import Data.Text          (Text, pack, unpack)
import Data.Map.Strict    (Map)
import Data.Maybe
import qualified Data.Map.Strict      as Map
import Data.Vector (fromList)
import qualified Data.ByteString.Lazy.Char8 as B

import AbsAct
import LexAct
import ParAct
import ErrM
import Options.Generic
--command line options
data Command w
  = Parse { file  :: w ::: String <?> "Path to file to parse"}
  | TypeCheck { file  :: w ::: String <?> "Path to file to parse"}
  | Compile { file :: w ::: String <?> "Path to file to parse"
            , k    :: w ::: Bool <?> "output k files"
            , ir   :: w ::: Bool <?> "output intermediate representation"
            , coq  :: w ::: Bool <?> "output coq files"
            , out  :: w ::: Maybe String <?> "output path"
            }
    deriving (Generic)

instance ParseRecord (Command Wrapped)
deriving instance Show (Command Unwrapped)

main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      (Parse f) -> do contents <- readFile f      
                      case pAct $ myLexer contents of
                        (Ok (Main a)) -> do print "success"
                                            print a
                        (Bad s) -> error s

      (TypeCheck f) -> do contents <- readFile f      
                          case pAct $ myLexer contents of --todo: proper monadic lifts
                            (Ok (Main a)) -> case typecheck a of
                              (Ok a)  -> print "success"
                              (Bad s) -> error s
                            (Bad s) -> error s
      -- (Compile f _ _ _ out) -> case (ir cmd) of
      --   True -> do contents <- readFile f
      --              case pAct $ myLexer contents of
      --                (Ok (Main behaviours)) -> mapM_ (B.putStrLn . encode . split) behaviours
      --                (Bad errormsg)         -> error errormsg
      --   False -> error "TODO"

typecheck :: [RawBehaviour] -> Err [Behaviour]
typecheck behvs = let store = lookupVars behvs in
                  mapM (checkBehaviour store) behvs

type Contract = Var

-- get the storage definitions from the constructor
lookupVars :: [RawBehaviour] -> Map Contract (Map Var Type)
lookupVars ((Transition _ _ _ _ _ _):bs) = lookupVars bs
lookupVars ((Constructor _ contract _ _ (Layout assigns)):bs) =
  Map.singleton contract (Map.fromList $ map fromAssign assigns)
  <> lookupVars bs
lookupVars [] = mempty

fromAssign :: Assign -> (Var, Type)
fromAssign (Assignval typ var _) = (var, typ)
fromAssign (Assignmap typ var _) = (var, typ)

defaultStore :: Map Var Type
defaultStore = Map.fromList
  [(Var "CALLVALUE", Type_uint),
   (Var "CALLER", Type_address)
   --others TODO
  ]

--typing of vars: other contract scopes, global (to this function)
type Env = (Map Contract (Map Var Type), Map Var Type)

-- checks a transition given a typing of its storage variables
checkBehaviour :: Map Contract (Map Var Type) -> RawBehaviour -> Err Behaviour
checkBehaviour store (Transition name contract method decls iffs cases) = do
  iff <- checkIffs env contract iffs
  cases <- case cases of
    Direct (ReturnP exp) -> inferExpr env exp
    Direct (StorageP updates) -> error "TODO: storage"
    Direct (StorageReturnP updates exp) -> do typedExp <- inferExpr exp
                                              error "TODO: storage"
  return (Behaviour name contract (method, decls) iff cases)
  where env = (store, fromMaybe mempty (Map.lookup contract store) <> abiVars <> defaultStore)
        abiVars = Map.fromList $ map (\(Dec typ var) -> (var, typ)) decls
checkBehaviour store (Constructor name contract decls iffs cases) = error "TODO"

checkIffs :: Env -> [IffH] -> Err [BExp]
checkIffs env c ((Iff exps):xs) = do
  head <- mapM (checkBool env) exps
  tail <- checkIffs env c xs
  Ok $ head <> tail
checkIffs env c ((IffIn typ exps):xs) = do
  head <- mapM (checkInt env) exps
  tail <- checkIffs env c xs
  Ok $ map (bound typ) head <> tail
checkIffs _ _ [] = Ok []

bound :: Type -> IExp -> BExp
bound typ exp = And (LEQ (lowerBound typ) exp) $ LEQ exp (upperBound typ)

lowerBound :: Type -> IExp
lowerBound Type_int = Lit $ 0 - 57896044618658097711785492504343953926634992332820282019728792003956564819968
lowerBound Type_int256 = Lit $ 0 - 57896044618658097711785492504343953926634992332820282019728792003956564819968
lowerBound Type_int126 = Lit $ 0 - 42535295865117307932921825928971026432
-- todo: other negatives
lowerBound _ = Lit 0

--todo, the rest
upperBound :: Type -> IExp
upperBound Type_uint    = Lit 115792089237316195423570985008687907853269984665640564039
upperBound Type_uint256 = Lit 115792089237316195423570985008687907853269984665640564039
upperBound _ = error "todo: max"

data MType = 
    Integer
  | Boolean
  | ByteStr
--  | IntList [Integer]

abiTypeToMeta :: Type -> MType
abiTypeToMeta Type_uint    = Integer
abiTypeToMeta Type_int     = Integer
abiTypeToMeta Type_uint256 = Integer
abiTypeToMeta Type_int256  = Integer
abiTypeToMeta Type_int126  = Integer
abiTypeToMeta Type_uint126 = Integer
abiTypeToMeta Type_int8    = Integer
abiTypeToMeta Type_uint8   = Integer
abiTypeToMeta Type_address = Integer
abiTypeToMeta Type_bool    = Boolean
abiTypeToMeta Type_bytes   = ByteStr
abiTypeToMeta Type_bytes32 = ByteStr
abiTypeToMeta Type_bytes4  = ByteStr
abiTypeToMeta Type_string  = ByteStr

inferExpr :: Env -> Exp -> Err TypedExp
inferExpr = _

checkExpr :: Env -> MType -> Exp -> Err TypedExp
checkExpr env Integer exp = checkInt   env exp
checkExpr env Boolean exp = checkBool  env exp
checkExpr env ByteStr exp = checkBytes env exp

checkBool :: Env -> Exp -> Err BExp
checkBool env@(others,thisContext) b =
  let checkInts op v1 v2 = do w1 <- checkInt env v1
                              w2 <- checkInt env v2
                              Ok $ op w1 w2
      checkBools op v1 v2 = do w1 <- checkBool env v1
                               w2 <- checkBool env v2
                               Ok $ op w1 w2
  in case b of
    EAnd  v1 v2 -> checkBools And  v1 v2
    EOr   v1 v2 -> checkBools Or   v1 v2
    EImpl v1 v2 -> checkBools Impl v1 v2
    EEq   v1 v2 -> checkInts  IEq  v1 v2
    ENeq  v1 v2 -> checkInts  INEq v1 v2
    ELE   v1 v2 -> checkInts  LE   v1 v2
    ELEQ  v1 v2 -> checkInts  LEQ  v1 v2
    EGE   v1 v2 -> checkInts  GE   v1 v2
    EGEQ  v1 v2 -> checkInts  GEQ  v1 v2
    ETrue  -> Ok BTrue
    EFalse -> Ok BFalse
    -- 
    VarLit v -> case Map.lookup v thisContext of
      Just Type_bool -> Ok (BoolVar v)
      _ -> Bad $ "Unexpected variable: " <> pprint v <> " of type boolean"
    Look v1 v2 -> case Map.lookup v1 thisContext of
      Just (MappingType t1 t2) -> error "TODO: lookups"
                                  --do checkExpr store contract (abiTypeToMeta t1)
      Just (ArrayType typ len) -> error "TODO: arrays"
      _ -> Bad $ "Unexpected lookup in " <> pprint v1 <> ": not array or mapping."
    -- TODO: zoom, lookup and functions
    s -> Bad $ "Unexpected expression: " <> show s <> " of type boolean"

checkInt :: Env -> Exp -> Err IExp
checkInt env e =
  let checkInts op v1 v2 = do w1 <- checkInt env v1
                              w2 <- checkInt env v2
                              Ok $ op w1 w2
  in case e of
  EAdd v1 v2 -> checkInts Add v1 v2
  ESub v1 v2 -> checkInts Sub v1 v2
  EMul v1 v2 -> checkInts Mul v1 v2
  EDiv v1 v2 -> checkInts Div v1 v2
  EMod v1 v2 -> checkInts Mod v1 v2
  _ -> error "TODO"

checkBytes :: Map Contract (Map Var Type) -> Contract -> Exp -> Err ByExp
checkBytes = error ""

-- AST post typechecking
data Behaviour = Behaviour
  {_name :: Var,
   _contract :: Var,
   _interface :: (Var, [Decl]),
--   _storage :: Maybe (Map Var Type),
   _preconditions :: [BExp],
   _cases :: Map BExp PrePost
  }

data PrePost = PrePost (Map Var [StorageUpdate], Maybe TypedExp)

            --                     pre       , post
data StorageUpdate = StorageUpdate StorageVar TypedExp

data TypedExp
  = BoolExp BExp
  | IntExp  IExp
  | ByteExp ByExp

data BExp
    = And  BExp BExp
    | Or   BExp BExp
    | Impl BExp BExp
    | IEq  IExp IExp
    | INEq IExp IExp
    | YEq  ByExp ByExp
    | Neg  BExp
    | LE   IExp IExp
    | GE   IExp IExp
    | LEQ  IExp IExp
    | GEQ  IExp IExp
    | BTrue
    | BFalse
    | BoolVar Var

data IExp
    = Add IExp IExp
    | Sub IExp IExp
    | ITE BExp IExp IExp
    | Mul IExp IExp
    | Div IExp IExp
    | Mod IExp IExp
    | Exp IExp IExp
    | Lit Integer
    | IntVar Var

data ByExp
    = Cat ByExp ByExp
    | Slice ByExp IExp IExp


data StorageVar
    = Entry Var
    | Struct StorageVar Var
    | Lookup StorageVar 


-- --Intermediate format
-- data Obligation = Obligation
--   { _name      :: String,
--     _contract  :: String,
--     _StatusCode :: String,
--     _methodName :: String,
--     _inputArgs  :: [Decl],
--     _return     :: (Exp, Type),
--     _preConditions :: [Exp]
-- --    _env        :: [(String, Var)],
-- -- --    _variables :: [(Var, Type)],
-- --     _preStore  :: [(Entry, Exp)],
-- --     _postStore :: [(Entry, Exp)],-
-- --     _postCondition :: [BExp]
--   } deriving (Show)

-- instance ToJSON Obligation where
--   toJSON (Obligation { .. }) =
--     object [ "name" .= _name
--            , "contract"  .= _contract
--            , "statusCode"  .= _StatusCode
--            , "methodName"  .= _methodName
--            , "inputArgs"   .= (Data.Aeson.Types.Array $ fromList (map
--                                                 (\(Dec abiType name) ->
--                                                   object [ "name" .= pprint name, "type" .= pprint abiType ])
--                                                  _inputArgs))
--            , "return"  .= object [ "value" .= pprint (fst _return), "type" .= pprint (snd _return) ]
--            , "preConditions"  .= (Data.Aeson.Types.Array $ fromList (fmap (String . pack . pprint) _preConditions))
--            -- , "calldata"  .= show _calldata
--            -- , "preStore"  .= show _preStore
--            -- , "postStore"  .= show _postStore
--            -- , "postCondition"  .= show _postCondition
--            ]


-- split :: Behaviour -> [Obligation]
-- split (Transition (Var name) (Var contract) (Var methodName) args iffs claim) =
--   case claim of
--     Direct (ReturnP returnExpr)  ->
--       --success case:
--       [Obligation
--       {_name     = name,
--        _contract = contract,
--        _StatusCode = "EVMC_SUCCESS",
--        _methodName = methodName,
--        _inputArgs  = args,
--        _return     = (returnExpr, getExpType returnExpr),
--        _preConditions  = concat $ fmap iffHToBool iffs
-- --       _env        = defaultEnv,
-- --       _calldata   = methodName args,
--        -- _variables  = [], --hmmm
--        -- _preStore   = [],
--        -- _postStore  = [],
--        -- _postCondition = []
--       }]
--     CaseSplit _ -> error "TODO"

-- getExpType :: Exp -> Type
-- getExpType (Int _) = Type_uint
-- getExpType (Bool _) = Type_bool
-- getExpType (Bytes _) = Type_bytes


-- defaultEnv :: [(String, Var)]
-- defaultEnv = [("CALLER", Var "CALLER_VAR")]

class Pretty a where
  pprint :: a -> String

instance Pretty Var where
  pprint (Var a) = a

-- -- instance Pretty Arg where
-- --   pprint (Argm a) = pprint a


-- instance Pretty Exp where
-- -- integers
--   pprint (EAdd x y) = pprint x <> " + " <> pprint y
--   pprint (ESub x y) = pprint x <> " - " <> pprint y
--   pprint (EMul x y) = pprint x <> " * " <> pprint y
--   pprint (EDiv x y) = pprint x <> " / " <> pprint y
--   pprint (EMod x y) = pprint x <> " % " <> pprint y
--   pprint (EExp x y) = pprint x <> " ^ " <> pprint y
--   pprint (EITE b x y) = "if" <> pprint b <>
--                      "then" <> pprint x <>
--                      "else" <> pprint y
--   pprint Wild = "_"
--   pprint (Func x y) = pprint x <> "(" <> intercalate "," (fmap pprint y) <> ")"
-- -- booleans
--   pprint (EAnd x y)  = pprint x <> " and " <> pprint y
--   pprint (EOr x y)   = pprint x <> " or "  <> pprint y
--   pprint (EImpl x y) = pprint x <> " => "  <> pprint y
--   pprint (EEq x y)   = pprint x <> " == "  <> pprint y
--   pprint (ENeq x y)  = pprint x <> " =/= " <> pprint y
--   pprint (ELEQ x y)  = pprint x <> " <= "  <> pprint y
--   pprint (ELE x y)   = pprint x <> " < "   <> pprint y
--   pprint (EGEQ x y)  = pprint x <> " >= "  <> pprint y
--   pprint (EGE x y)   = pprint x <> " > "   <> pprint y
--   pprint ETrue = "true"
--   pprint EFalse = "false"
-- -- bytes
--   pprint (Cat x y)  = pprint x <> "++" <> pprint y
--   pprint (Slice byexp a b) = pprint byexp
--     <> "[" <> show a <> ".." <> show b <> "]"
--   pprint (Newaddr x y) = "newAddr"  <> pprint x <> pprint y
--   pprint (Newaddr2 x y z) = "newAddr" <> pprint x <> pprint y <> pprint z
--   pprint (BYHash x) = "keccak256" <> pprint x
--   pprint (BYAbiE x) = "abiEncode" <> pprint x


-- instance Pretty Type where
--   pprint Type_uint = "uint256"
--   pprint Type_int = "int256"
--   pprint Type_bytes = "bytes"
--   pprint Type_uint256 = "uint256"
--   pprint Type_int256 = "int256"
--   pprint Type_int126 = "int126"
--   pprint Type_uint126 = "uint126"
--   pprint Type_int8 = "int8"
--   pprint Type_uint8 = "uint8"
--   pprint Type_address = "address"
--   pprint Type_bytes32 = "bytes32"
--   pprint Type_bytes4 = "bytes4"
--   pprint Type_bool = "bool"
--   pprint Type_string = "string"

-- min :: Type -> Exp
-- min Type_uint = IntLit 0
-- min Type_uint256 = IntLit 0
-- min Type_uint126 = IntLit 0
-- min Type_uint8 = IntLit 0
-- --todo, the rest

-- max :: Type -> Exp
-- max Type_uint    = EInt 115792089237316195423570985008687907853269984665640564039
-- max Type_uint256 = EInt 115792089237316195423570985008687907853269984665640564039
-- max _ = error "todo: max"


-- --Prints an act expression as a K ByteArray
-- kPrintBytes :: Exp -> String
-- kPrintBytes _ = "TODO: krpintBytes" --todo

-- iffHToBool :: IffH -> [Exp]
-- iffHToBool (Iff bexps) = bexps
-- iffHToBool (IffIn abitype exprs) =
--   fmap
--     (\exp -> BAnd (BLEQ (Main.min abitype) exp) (BLEQ exp (Main.max abitype)))
--     exprs
