{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# OPTIONS -XMagicHash #-}
import Data.List
import Data.Aeson hiding (Bool)
import Data.Aeson.Types hiding (Bool)
import GHC.Generics
import System.Environment ( getArgs )
import System.Exit ( exitFailure )
import Data.Text          (Text, pack, unpack)
import Data.Map.Strict    (Map)
import Data.Maybe
import qualified Data.Map.Strict      as Map -- abandon in favor of [(a,b)]?
import Data.Vector (fromList)
import qualified Data.ByteString.Lazy.Char8 as B
import Control.Monad

import Syntax
import ErrM
import Splitter
import LexAct
import Options.Generic
import RefinedAst


-- to be defined by parser
myLexer :: String -> [Token]
myLexer = error "import ParAct to parse"

pAct :: [Token] -> Err Act
pAct = error "to be defined by parser"

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
                      let tokens = myLexer contents
                          getErrPos ((Err x):xs) = Just x
                          getErrPos (_:xs) = getErrPos xs
                          getErrPos [] = Nothing
                      case getErrPos tokens of
                               Just (Pn col lin _) -> print $ "syntax error at line " <> show lin <> ", column " <> show col
                               Nothing -> case pAct tokens of
                                            Ok (Main act) -> do print "success"
                                                                print act
                                            Bad s -> error s -- todo: get position information

      (TypeCheck f) -> do contents <- readFile f
                          case pAct $ myLexer contents of --todo: proper monadic lifts
                            (Ok (Main a)) -> case typecheck a of
                              (Ok a)  -> do print "success:"
                                            print $ show a
                              (Bad s) -> error s
                            (Bad s) -> error s

typecheck :: [RawBehaviour] -> Err [Behaviour]
typecheck behvs = let store = lookupVars behvs in
                  mapM (checkBehaviour store) behvs

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Map Contract (Map Id Type)
lookupVars ((Transition _ _ _ _ _ _):bs) = lookupVars bs
lookupVars ((Constructor _ contract _ _ form):bs) =
  let assigns
        = case form of
            CCases _ cases -> error "TODO: cases (or should we remove this?)"
            CDirect (PostCreates defs _ ) -> defs
  in
  Map.singleton (IntVar contract) (Map.fromList $ map fromAssign assigns)
  <> lookupVars bs
  where fromAssign (Assignval (Dec typ var) _) = (var, typ)
        fromAssign (AssignMany (Dec typ var) _) = (var, typ)
        fromAssign (AssignStruct _ _) = error "TODO: assignstruct"
lookupVars [] = mempty


-- typing of eth env variables
defaultStore :: [(EthEnv, Type)]
defaultStore =
  [(CALLVALUE, T_uint 256),
   (CALLER, T_address),
   (BLOCKNUMBER, T_uint 256)
   --others TODO
  ]

--typing of vars: other contract scopes, global (to this function)
type Env = (Map Contract (Map Id Type), Map Id Type)

-- checks a transition given a typing of its storage variables
checkBehaviour :: Map Contract (Map Id Type) -> RawBehaviour -> Err Behaviour
checkBehaviour store (Transition name contract method decls iffs claim) = do
  iff <- checkIffs env iffs
  claims <- case claim of
    TDirect post -> do p <- checkPost env (IntVar contract) post
                       Ok [(BTrue, p)]
    TCases cases -> sequence $ fmap
      (\(Case _ cond post) -> do p <- checkPost env (IntVar contract) post
                                 c <- checkBool env cond
                                 Ok (c, p))
      cases
  return (Behaviour name contract (method, decls) iff (Map.fromList claims))
  where env = (store, fromMaybe mempty (Map.lookup (IntVar contract) store) <> abiVars)
        abiVars = Map.fromList $ map (\(Dec typ var) -> (var, typ)) decls
checkBehaviour store (Constructor name contract decls iffs cases) = error "TODO: check constructor"

checkPost :: Env -> Contract -> Post -> Err Claim
checkPost env contract (Post maybeStorage extStorage maybeReturn) =
  do  returnexp <- sequence $ fmap (inferExpr env) maybeReturn
      ourStorage <- case maybeStorage of
        Just entries -> checkEntries contract entries
        Nothing -> Ok []
      otherStorage <- checkStorages extStorage
      Ok (Map.fromList $ ((contract, ourStorage):otherStorage), returnexp)
  where checkEntries name entries = sequence $ fmap (uncurry $ checkStorageExpr env name) entries
        checkStorages :: [ExtStorage] -> Err [(Contract, [StorageUpdate])]
        checkStorages [] = Ok []
        checkStorages ((ExtStorage name entries):xs) = do contract <- checkInt env name
                                                          p <- checkEntries contract entries
                                                          ps <- checkStorages xs
                                                          Ok $ (contract, p):ps
        checkStorages ((ExtCreates _ name entries):xs) = error "TODO: check other storages"


checkStorageExpr :: Env -> Contract -> Entry -> Expr -> Err (Entry, TypedExp)
checkStorageExpr = error "TODO: checkStorageExpr"

checkIffs :: Env -> [IffH] -> Err [BExp]
checkIffs env ((Iff pos exps):xs) = do
  head <- mapM (checkBool env) exps
  tail <- checkIffs env xs
  Ok $ head <> tail
checkIffs env ((IffIn pos typ exps):xs) = do
  head <- mapM (checkInt env) exps
  tail <- checkIffs env xs
  Ok $ map (bound typ) head <> tail
checkIffs _ [] = Ok []

bound :: Type -> IExp -> BExp
bound typ exp = And (LEQ (lowerBound typ) exp) $ LEQ exp (upperBound typ)

lowerBound :: Type -> IExp
lowerBound (T_int a) = Lit $ 0 - 2 ^ (a - 1)
-- todo: other negatives
lowerBound _ = Lit 0

--todo, the rest
upperBound :: Type -> IExp
upperBound (T_uint n) = Lit $ 2 ^ n - 1
upperBound (T_int n)  = Lit $ 2 ^ (n - 1) - 1
upperBound T_address = Lit $ 2 ^ 160 - 1

metaType :: Type -> MType
metaType (T_uint _)      = Integer
metaType (T_int _)       = Integer
metaType T_address       = Integer
metaType T_bool          = Boolean
--metaType T_bytes         = ByteStr
metaType T_bytes_dynamic = ByteStr
metaType T_string        = ByteStr
metaType _ = error "TODO"

checkExpr :: Env -> MType -> Expr -> Err TypedExp
checkExpr env Integer exp = checkInt   env exp >>= Ok . IntExp
checkExpr env Boolean exp = checkBool  env exp >>= Ok . BoolExp
checkExpr env ByteStr exp = checkBytes env exp >>= Ok . ByteExp

inferExpr :: Env -> Expr -> Err TypedExp
inferExpr env exp = let intintint op v1 v2 = do w1 <- checkInt env v1
                                                w2 <- checkInt env v2
                                                Ok $ IntExp $ op w1 w2
                        boolintint op v1 v2 = do w1 <- checkInt env v1
                                                 w2 <- checkInt env v2
                                                 Ok $ BoolExp $ op w1 w2
                        boolboolbool op v1 v2 = do w1 <- checkBool env v1
                                                   w2 <- checkBool env v2
                                                   Ok $ BoolExp $ op w1 w2
                    in case exp of
    EAnd _  v1 v2 -> boolboolbool And  v1 v2
    EOr _   v1 v2 -> boolboolbool Or   v1 v2
    EImpl _ v1 v2 -> boolboolbool Impl v1 v2
    EEq _   v1 v2 -> boolintint  IEq  v1 v2
    ENeq _  v1 v2 -> boolintint  INEq v1 v2
    ELE _   v1 v2 -> boolintint  LE   v1 v2
    ELEQ _  v1 v2 -> boolintint  LEQ  v1 v2
    EGE _   v1 v2 -> boolintint  GE   v1 v2
    EGEQ _  v1 v2 -> boolintint  GEQ  v1 v2
    ETrue _ ->  Ok $ BoolExp BTrue
    EFalse _ -> Ok $ BoolExp BFalse
    EITE _ v1 v2 v3 -> do w1 <- checkBool env v1
                          w2 <- checkInt env v2
                          w3 <- checkInt env v3
                          Ok $ IntExp $ ITE w1 w2 w3
    EAdd _ v1 v2 -> intintint Add v1 v2
    ESub _ v1 v2 -> intintint Sub v1 v2
    EMul _ v1 v2 -> intintint Mul v1 v2
    EDiv _ v1 v2 -> intintint Div v1 v2
    EMod _ v1 v2 -> intintint Mod v1 v2
    EExp _ v1 v2 -> intintint Exp v1 v2
    Var _ v1 -> error "TODO: infer var type"
    IntLit _ n -> Ok $ IntExp $ Lit n
    _ -> error "TODO: infer other stuff type"
    -- Wild ->
    -- Zoom Var Exp
    -- Func Var [Expr]
    -- Look Expr Expr
    -- ECat Expr Expr
    -- ESlice Expr Expr Expr
    -- Newaddr Expr Expr
    -- Newaddr2 Expr Expr Expr
    -- BYHash Expr
    -- BYAbiE Expr
    -- StringLit String

checkBool :: Env -> Expr -> Err BExp
checkBool env@(others,thisContext) b =
  let checkInts op v1 v2 = do w1 <- checkInt env v1
                              w2 <- checkInt env v2
                              Ok $ op w1 w2
      checkBools op v1 v2 = do w1 <- checkBool env v1
                               w2 <- checkBool env v2
                               Ok $ op w1 w2
  in case b of
    EAnd  _ v1 v2 -> checkBools And  v1 v2
    EOr   _ v1 v2 -> checkBools Or   v1 v2
    EImpl _ v1 v2 -> checkBools Impl v1 v2
    EEq   _ v1 v2 -> checkInts  IEq  v1 v2
    ENeq  _ v1 v2 -> checkInts  INEq v1 v2
    ELE   _ v1 v2 -> checkInts  LE   v1 v2
    ELEQ  _ v1 v2 -> checkInts  LEQ  v1 v2
    EGE   _ v1 v2 -> checkInts  GE   v1 v2
    EGEQ  _ v1 v2 -> checkInts  GEQ  v1 v2
    ETrue _  -> Ok BTrue
    EFalse _ -> Ok BFalse
    --
    Var _ v -> case Map.lookup v thisContext of
      Just T_bool -> Ok (BoolVar v)
      _ -> Bad $ "Unexpected variable: " <> show v <> " of type boolean"
    -- Look v1 v2 -> case Map.lookup v1 thisContext of
    --   Just (MappingType t1 t2) -> error "TODO: lookups"
    --                               --do checkExpr store contract (abiTypeToMeta t1)
    --   Just (ArrayType typ len) -> error "TODO: arrays"
    --   _ -> Bad $ "Unexpected lookup in " <> pprint v1 <> ": not array or mapping."
    -- TODO: zoom, lookup and functions
    s -> Bad $ "Unexpected expression: " <> show s <> " of type boolean"

checkInt :: Env -> Expr -> Err IExp
checkInt env@(others,thisContext) e =
  let checkInts op v1 v2 = do w1 <- checkInt env v1
                              w2 <- checkInt env v2
                              Ok $ op w1 w2
  in case e of
  EAdd _ v1 v2 -> checkInts Add v1 v2
  ESub _ v1 v2 -> checkInts Sub v1 v2
  EMul _ v1 v2 -> checkInts Mul v1 v2
  EDiv _ v1 v2 -> checkInts Div v1 v2
  EMod _ v1 v2 -> checkInts Mod v1 v2
  EExp _ v1 v2 -> checkInts Exp v1 v2
  Var _ v -> case Map.lookup v thisContext of
    Just typ -> case metaType typ of
                  Integer -> Ok (IntVar v)
                  _ -> Bad $ "Unexpected variable: " <> show v <> " of type integer"
    _ -> Bad $ "Uknown variable: " <> show v <> " of type integer"
  IntLit _ n -> Ok $ Lit n
  v -> error ("TODO: check int, case:" <> show v )

checkBytes :: Env -> Expr -> Err ByExp
checkBytes = error ""
