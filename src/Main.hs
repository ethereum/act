{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
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
--import qualified Data.ByteString as B
import Control.Monad

import Syntax
--import AbsAct
import ErrM
import Splitter
import LexAct
--import ParAct
import Options.Generic
import RefinedAst

-- to be defined by parser
myLexer :: String -> [Token]
myLexer = error "import ParAct to parse"

pAct :: [Token] -> Err Act
pAct = error "to be defined by parser"

--command line options
data Command w
  = Parse { file  :: w ::: String <?> "Path to file"}
  | ParseAndTypeCheck { file  :: w ::: String <?> "Path to file"}
  | KaseSplit { spec  :: w ::: String <?> "Path to spec",
                soljson  :: w ::: String <?> "Path to .sol.json"
              }
  | TypeCheck { file  :: w ::: String <?> "Path to file"}
  | Compile { file :: w ::: String <?> "Path to file"
            , k    :: w ::: Bool <?> "output k files"
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
                        Ok (Main act) -> do print act
                        Bad s -> error s -- todo: get position information

      (ParseAndTypeCheck f) -> do contents <- readFile f
                                  case pAct $ myLexer contents of --todo: proper monadic lifts
                                    (Ok (Main spec)) -> case typecheck spec of
                                      (Ok a)  -> B.putStrLn $ encode a
                                      (Bad s) -> error s
                                    (Bad s) -> error s

      (TypeCheck f) -> do contents <- readFile f
                          let act = read contents :: [RawBehaviour]
                          case typecheck act of
                            (Ok a)  -> B.putStrLn $ encode a
                            (Bad s) -> error s

      (KaseSplit specFile implFile) -> do specText <- readFile specFile
                                          let spec = read specText :: [RawBehaviour]
                                          case typecheck spec of
                                            (Ok a)  -> do implText <- readFile implFile
                                                          print "ok"
                                            (Bad s) -> error s





typecheck :: [RawBehaviour] -> Err [Behaviour]
typecheck behvs = let store = lookupVars behvs in
                  do bs <- mapM (splitBehaviour store) behvs
                     return $ join bs

--- Finds storage declarations from constructors
lookupVars :: [RawBehaviour] -> Map Id (Map Id Container)
lookupVars ((Transition _ _ _ _ _ _):bs) = lookupVars bs
lookupVars ((Constructor _ contract _ _ form _):bs) =
  let assigns
        = case form of
            CCases _ cases -> error "TODO: cases (or should we remove this?)"
            CDirect (PostCreates defs _ ) -> defs
  in
  Map.singleton contract (Map.fromList $ map fromAssign assigns)
  <> lookupVars bs
  where fromAssign (Assignval (StorageDec typ var) _) = (var, typ)
        fromAssign (AssignMany (StorageDec typ var) _) = (var, typ)
        fromAssign (AssignStruct _ _) = error "TODO: assignstruct"
lookupVars [] = mempty


-- typing of eth env variables
defaultStore :: [(EthEnv, MType)]
defaultStore =
  [(CALLVALUE, Integer),
   (CALLER, Integer),
   (BLOCKNUMBER, Integer)
   --others TODO
  ]

-- typing of vars: this contract storage, other contract scopes, calldata args
type Env = (Map Id Container, Map Id (Map Id Container), Map Id MType)

-- checks a transition given a typing of its storage variables
splitBehaviour :: Map Id (Map Id Container) -> RawBehaviour -> Err [Behaviour]
splitBehaviour store (Transition name contract (Interface method decls) iffs claim maybePost) = do
  iff <- checkIffs env iffs
  postcondition <- sequence $ fmap (checkBool env) (fromMaybe [] maybePost)
  case claim of
    TDirect post -> do (updates,maybeReturn) <- checkPost env contract post
                       return [mkCase iff maybeReturn updates postcondition]
    TCases cases -> error "coming soon"
  where env = (fromMaybe mempty (Map.lookup contract store), store, abiVars)
        abiVars = Map.fromList $ map (\(Dec typ var) -> (var, metaType typ)) decls
        mkCase pre return storage postc = Behaviour name contract (method, decls) pre postc storage return
splitBehaviour store (Constructor name contract decls iffs cases post) = Ok [] --error "TODO: check constructor"

checkPost :: Env -> Id -> Post -> Err (Map Id [StorageUpdate], Maybe ReturnExp)
checkPost env@(ours, theirs, localVars) contract (Post maybeStorage extStorage maybeReturn) =
  do  returnexp <- sequence $ fmap (inferExpr env) maybeReturn
      ourStorage <- case maybeStorage of
        Just entries -> checkEntries contract entries
        Nothing -> Ok []
      otherStorage <- checkStorages extStorage
      return $ ((Map.fromList $ (contract, ourStorage):otherStorage), returnexp)
  where checkEntries name entries = sequence $ fmap (uncurry $ checkStorageExpr (fromMaybe mempty (Map.lookup name theirs), theirs, localVars)) entries
        checkStorages :: [ExtStorage] -> Err [(Id, [StorageUpdate])]
        checkStorages [] = Ok []
        checkStorages ((ExtStorage name entries):xs) = do p <- checkEntries name entries
                                                          ps <- checkStorages xs
                                                          Ok $ (name, p):ps
        checkStorages ((ExtCreates _ name entries):xs) = error "TODO: check other storages"

checkStorageExpr :: Env -> Entry -> Expr -> Err StorageUpdate
checkStorageExpr env@(ours, theirs, localVars) entry@(Entry p id ixs) expr =
    case Map.lookup id ours of
      Just container -> case final container of
          Integer -> liftM2 IntUpdate (checkIntEntry env entry container) (checkInt env expr)
          Boolean -> liftM2 BoolUpdate (checkBoolEntry env entry container) (checkBool env expr)
          ByteStr -> liftM2 BytesUpdate (checkBytesEntry env entry container) (checkBytes env expr)
      Nothing -> Bad $ "Unknown storage variable: " <> show id <> " at: " <> show p
  where final (Direct m) = metaType m
        final (Syntax.Mapping t c) = final c

checkIntEntry :: Env -> Entry -> Container -> Err (TContainer () T_Int)
checkIntEntry _ (Entry p id []) (Direct t ) = case metaType t of
                                              Integer -> Ok $ DirectInt id
                                              Boolean -> Bad $ "Typing error"
                                              ByteStr -> Bad $ "Typing error"
checkIntEntry _ (Entry p id []) _ = Bad $ "Abstract container specifications not (yet) supported"
checkIntEntry env (Entry p id (e:es)) (Syntax.Mapping t c) =
  case metaType t of
    Integer -> do exp <- checkInt env e
                  rest <- checkIntEntry env (Entry p id es) c
                  return $ Lookup (IntIndexed rest) exp
    Boolean -> do exp <- checkBool env e
                  rest <- checkIntEntry env (Entry p id es) c
                  return $ Lookup (BoolIndexed rest) exp
    ByteStr -> do exp <- checkBytes env e
                  rest <- checkIntEntry env (Entry p id es) c
                  return $ Lookup (BytesIndexed rest) exp

checkBoolEntry :: Env -> Entry -> Container -> Err (TContainer () T_Bool)
checkBoolEntry env (Entry p id []) (Syntax.Direct t) = case metaType t of
                                            Integer -> Bad $ "Typing error"
                                            Boolean -> Ok $ DirectBool id
                                            ByteStr -> Bad $ "Typing error"
checkBoolEntry env (Entry p id (e:es)) (Syntax.Mapping t c) = case metaType t of
                                                  Integer -> do exp <- checkInt env e
                                                                rest <- checkBoolEntry env (Entry p id es) c
                                                                return $ Lookup (IntIndexed rest) exp
                                                  Boolean -> do exp <- checkBool env e
                                                                rest <- checkBoolEntry env (Entry p id es) c
                                                                return $ Lookup (BoolIndexed rest) exp
                                                  ByteStr -> do exp <- checkBytes env e
                                                                rest <- checkBoolEntry env (Entry p id es) c
                                                                return $ Lookup (BytesIndexed rest) exp
checkBoolEntry env _ _ = Bad $ "Wrong arguments given to mapping"

checkBytesEntry :: Env -> Entry -> Container -> Err (TContainer () T_Bytes)
checkBytesEntry env (Entry p id []) (Syntax.Direct t) = case metaType t of
                                            Integer -> Bad $ "Typing error"
                                            Boolean -> Bad $ "Typing error"
                                            ByteStr -> Ok $ DirectBytes id
checkBytesEntry env (Entry p id (e:es)) (Syntax.Mapping t c) = case metaType t of
                                                  Integer -> do exp <- checkInt env e
                                                                rest <- checkBytesEntry env (Entry p id es) c
                                                                return $ Lookup (IntIndexed rest) exp
                                                  Boolean -> do exp <- checkBool env e
                                                                rest <- checkBytesEntry env (Entry p id es) c
                                                                return $ Lookup (BoolIndexed rest) exp
                                                  ByteStr -> do exp <- checkBytes env e
                                                                rest <- checkBytesEntry env (Entry p id es) c
                                                                return $ Lookup (BytesIndexed rest) exp
checkBytesEntry env _ _ = Bad $ "Wrong arguments given to mapping"
        
checkIffs :: Env -> [IffH] -> Err [Exp T_Bool]
checkIffs env ((Iff pos exps):xs) = do
  head <- mapM (checkBool env) exps
  tail <- checkIffs env xs
  Ok $ head <> tail
checkIffs env ((IffIn pos typ exps):xs) = do
  head <- mapM (checkInt env) exps
  tail <- checkIffs env xs
  Ok $ map (bound typ) head <> tail
checkIffs _ [] = Ok []

bound :: Type -> (Exp T_Int) -> Exp T_Bool
bound typ exp = And (LEQ (lowerBound typ) exp) $ LEQ exp (upperBound typ)

lowerBound :: Type -> Exp T_Int
lowerBound (T_int a) = LitInt $ 0 - 2 ^ (a - 1)
-- todo: other negatives
lowerBound _ = LitInt 0

--todo, the rest
upperBound :: Type -> Exp T_Int
upperBound (T_uint n) = LitInt $ 2 ^ n - 1
upperBound (T_int n)  = LitInt $ 2 ^ (n - 1) - 1
upperBound T_address  = LitInt $ 2 ^ 160 - 1

metaType :: Type -> MType
metaType (T_uint _)      = Integer
metaType (T_int _)       = Integer
metaType T_address       = Integer
metaType T_bool          = Boolean
--metaType T_bytes         = ByteStr
metaType T_bytes_dynamic = ByteStr
metaType T_string        = ByteStr
metaType _ = error "TODO"

inferExpr :: Env -> Expr -> Err ReturnExp
inferExpr env exp = let intintint op v1 v2 = do w1 <- checkInt env v1
                                                w2 <- checkInt env v2
                                                Ok $ ExpInt $ op w1 w2
                        boolintint op v1 v2 = do w1 <- checkInt env v1
                                                 w2 <- checkInt env v2
                                                 Ok $ ExpBool $ op w1 w2
                        boolboolbool op v1 v2 = do w1 <- checkBool env v1
                                                   w2 <- checkBool env v2
                                                   Ok $ ExpBool $ op w1 w2
                    in case exp of
    EAnd _  v1 v2 -> boolboolbool And  v1 v2
    EOr _   v1 v2 -> boolboolbool Or   v1 v2
    EImpl _ v1 v2 -> boolboolbool Impl v1 v2
    EEq _   v1 v2 -> boolintint  Eq  v1 v2
    ENeq _  v1 v2 -> boolintint  NEq v1 v2
    ELE _   v1 v2 -> boolintint  LE   v1 v2
    ELEQ _  v1 v2 -> boolintint  LEQ  v1 v2
    EGE _   v1 v2 -> boolintint  GE   v1 v2
    ETrue _ ->  Ok  $ ExpBool $ LitBool True
    EFalse _ -> Ok $ ExpBool $ LitBool False
    -- EITE _ v1 v2 v3 -> do w1 <- checkBool env v1
    --                       w2 <- checkInt env v2
    --                       w3 <- checkInt env v3
    --                       Ok $ ITE w1 w2 w3
    EAdd _ v1 v2 -> intintint Add v1 v2
    ESub _ v1 v2 -> intintint Sub v1 v2
    EMul _ v1 v2 -> intintint Mul v1 v2
    EDiv _ v1 v2 -> intintint Div v1 v2
    EMod _ v1 v2 -> intintint Mod v1 v2
    EExp _ v1 v2 -> intintint Exp v1 v2
    Var _ v1 -> error "TODO: infer var type"
    IntLit _ n -> Ok $ ExpInt $ LitInt n
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

checkBool :: Env -> Expr -> Err (Exp T_Bool)
checkBool env@(ours, theirs,thisContext) b =
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
    EEq   _ v1 v2 -> checkInts  Eq  v1 v2
    ENeq  _ v1 v2 -> checkInts  NEq v1 v2
    ELE   _ v1 v2 -> checkInts  LE   v1 v2
    ELEQ  _ v1 v2 -> checkInts  LEQ  v1 v2
    EGE   _ v1 v2 -> checkInts  GE   v1 v2
    EGEQ  _ v1 v2 -> checkInts  GEQ  v1 v2
    ETrue _  -> Ok $ LitBool True
    EFalse _ -> Ok $ LitBool False
    --
    Var _ v -> case Map.lookup v thisContext of
      Just Boolean -> Ok (BoolVar v)
      _ -> Bad $ "Unexpected variable: " <> show v <> " of type boolean"
    -- Look v1 v2 -> case Map.lookup v1 thisContext of
    --   Just (MappingType t1 t2) -> error "TODO: lookups"
    --                               --do checkExpr store contract (abiTypeToMeta t1)
    --   Just (ArrayType typ len) -> error "TODO: arrays"
    --   _ -> Bad $ "Unexpected lookup in " <> pprint v1 <> ": not array or mapping."
    -- TODO: zoom, lookup and functions
    s -> Bad $ "Unexpected expression: " <> show s <> " of type boolean"


checkInt :: Env -> Expr -> Err (Exp T_Int)
checkInt env@(ours, theirs,thisContext) e =
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
    Just Integer -> Ok $ IntVar v
    _ -> Bad $ "Unexpected variable: " <> show v <> " of type integer"
  IntLit _ n -> Ok $ LitInt n
  EnvExpr _ n -> case lookup n defaultStore of
    Nothing -> Bad $ "unknown environment variable: " <> show n
    Just Integer -> Ok $ IntEnv n
  EntryExp e@(Entry p id _) -> case Map.lookup id ours of
    Nothing -> Bad $ "unknown environment variable: " <> show id
    Just c -> do a <- checkIntEntry env e c
                 return $ TEntry a
    
  v -> error ("TODO: check int, case:" <> show v )

checkBytes :: Env -> Expr -> Err (Exp T_Bytes)
checkBytes = error ""
