{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module RefinedAst where
import GHC.Generics
import Data.Map.Strict    (Map)
import qualified Data.Map.Strict      as Map
import Data.ByteString       (ByteString)

import Syntax

-- AST post typechecking
data Behaviour a = Behaviour
  {_name :: Id,
   _contract :: Id,
   _interface :: (Id, [Decl]),
   _preconditions :: [BExp],
   _cases :: Map BExp (Claim a)
  }   deriving (Eq, Ord, Show, Read)

type Contract = IExp

--types understood by proving tools
data MType 
  = Integer
  | Boolean
  | ByteStr
  deriving (Eq, Ord, Show, Read)

-- the type var a holds the type of the return expression
data Claim a = Claim (Map Contract [StorageUpdate]) (Maybe (TExp a))

-- meta types that work as GADT "tags"
data T_Int
data T_Bool
data Mapping k a

data StorageUpdate
  = IntUpdate (TEntry T_Int) (TExp T_Int)
  | BoolUpdate (TEntry T_Bool) (TExp T_Bool)

data TEntry typ where 
  IntEntry  :: Id -> T_Int -> TEntry T_Int
  BoolEntry :: Id -> T_Bool -> TEntry T_Bool
  TLookup  :: (TEntry (Mapping k a)) -> (TExp k) -> TEntry a
--  Struct  :: (TEntry (Mapping k a)) -> (TExp k) -> TEntry a

data TExp typ where
  Int  :: IExp -> TExp T_Int
  Bool :: BExp -> TExp T_Bool

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
    | BoolVar Id
  deriving (Eq, Ord, Show, Read)

data IExp
    = Add IExp IExp
    | Sub IExp IExp
    | ITE BExp IExp IExp
    | Mul IExp IExp
    | Div IExp IExp
    | Mod IExp IExp
    | Exp IExp IExp
    | Lit Integer
    | IEnv EthEnv
    | IntVar Id
  deriving (Eq, Ord, Show, Read)

data ByExp
    = Cat ByExp ByExp
    | Slice ByExp IExp IExp
    | ByVar Id
    | ByStr String
    | ByLit ByteString
  deriving (Eq, Ord, Show, Read)

-- add array MTypes and post conditions
