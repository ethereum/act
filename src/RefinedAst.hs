module RefinedAst where
import GHC.Generics
import Data.Map.Strict    (Map)
import qualified Data.Map.Strict      as Map
import Data.ByteString       (ByteString)

import Syntax

-- AST post typechecking
data Behaviour = Behaviour
  {_name :: Id,
   _contract :: Id,
   _interface :: (Id, [Decl]),
   _preconditions :: [BExp],
   _cases :: Map BExp Claim
  }   deriving (Eq, Ord, Show, Read)

type Contract = IExp

--types understood by proving tools
data MType 
  = Integer
  | Boolean
  | ByteStr
  deriving (Eq, Ord, Show, Read)
type Claim = (Map Contract [StorageUpdate], Maybe TypedExp)

--                    pre       , post
type StorageUpdate = (Entry, TypedExp)

data TypedExp
  = BoolExp BExp
  | IntExp  IExp
  | ByteExp ByExp
  deriving (Eq, Ord, Show, Read)

data TypedEntry
  = BoolEntry Entry
  | IntEntry Entry
  | ByteEntry Entry
  deriving (Eq, Ord, Show, Read)  
  
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
    | IntVar Id
  deriving (Eq, Ord, Show, Read)

data ByExp
    = Cat ByExp ByExp
    | Slice ByExp IExp IExp
    | ByVar Id
    | ByStr String
    | ByLit ByteString
  deriving (Eq, Ord, Show, Read)
