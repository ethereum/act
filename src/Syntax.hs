-- data types for the parsed syntax.
-- Has the correct basic structure, but doesn't necessarily type check
-- It is also equipped with position information for extra debugging xp
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax where
import Data.List          (intercalate)
import Lex

type Pn = AlexPosn
  
type Id = String

data Act = Main [RawBehaviour]
  deriving (Eq, Show)

data RawBehaviour
    = Transition Id Id Interface [IffH] TransitionClaim (Maybe Ensures)
    | Constructor Id Id Interface [IffH] Creates [ExtStorage] (Maybe Ensures) (Maybe Invariants)
  deriving (Eq, Show)

type Ensures = [Expr]

type Invariants = [Expr]

data Interface = Interface Id [Decl]
  deriving (Eq)

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

data TransitionClaim = Cases [Case] | TDirect Post
  deriving (Eq, Show)

data Case
    = Leaf Pn Expr Post
    | Branch Pn Expr [Case]
  deriving (Eq, Show)

data Post
    = Post (Maybe Storage) [ExtStorage] (Maybe Expr)
  deriving (Eq, Show)

data Creates
    = Creates [Assign]
  deriving (Eq, Show)

type Storage = [(Entry, Expr)]

data ExtStorage
    = ExtStorage Id [(Entry, Expr)]
    | ExtCreates Id Expr [Assign]
  deriving (Eq, Show)

data Assign = AssignVal StorageDecl Expr | AssignMany StorageDecl [Defn] | AssignStruct StorageDecl [Defn]
  deriving (Eq, Show)

data IffH = Iff Pn [Expr] | IffIn Pn Type [Expr]
  deriving (Eq, Show)

data Entry
  = Entry Id [Expr]
  deriving (Eq, Show)

--data Defn = Defn Pn Expr Expr
data Defn = Defn Expr Expr
  deriving (Eq, Show)

data Expr
    = EAnd Pn Expr Expr
    | EOr Pn Expr Expr
    | EImpl Pn Expr Expr
    | EEq Pn Expr Expr
    | ENeq Pn Expr Expr
    | ELEQ Pn Expr Expr
    | ELT Pn Expr Expr
    | EGEQ Pn Expr Expr
    | EGT Pn Expr Expr
    | ETrue Pn
    | EFalse Pn
    | EAdd Pn Expr Expr
    | ESub Pn Expr Expr
    | EITE Pn Expr Expr Expr
    | EMul Pn Expr Expr
    | EDiv Pn Expr Expr
    | EMod Pn Expr Expr
    | EExp Pn Expr Expr
    | Zoom Pn Expr Expr
    | Look Pn Expr Expr
    | Func Pn Id [Expr]
    | ListConst Expr
    | EmptyList
    | ECat Pn Expr Expr
    | ESlice Pn Expr Expr Expr
    | Newaddr Pn Expr Expr
    | Newaddr2 Pn Expr Expr Expr
    | BYHash Pn Expr
    | BYAbiE Pn Expr
    | StringLit Pn String
    | Var Id
    | Wild
    | EnvExpr Pn EthEnv
    | IntLit Integer
  deriving (Eq, Show)

data EthEnv
   = CALLER
   | CALLVALUE
   | BLOCKNUMBER
   | TXORIGIN
   | BLOCKHASH
  deriving (Eq, Show)

data StorageDecl = StorageDecl Container Id
  deriving (Eq, Show)

data Decl = Decl Type Id
  deriving (Eq)

instance Show Decl where
  show (Decl t a) = show t <> " " <> a

-- storage types
data Container
   = Direct Type
   | Mapping Type Container
  deriving (Eq, Show)

-- callvalue types
-- TODO: refine to "elementary" types and whatnot?
data Type
   = T_uint Int
   | T_int Int
   | T_address
   | T_bytes Int
   | T_bytes_dynamic
   | T_bool
   | T_string
   | T_array_static Type Integer
   | T_array_dynamic Type
   | T_tuple [Type]
   | T_contract Id
  deriving (Eq)

instance Show Type where
  show = abiTypeSolidity

abiTypeSolidity :: Type -> String
abiTypeSolidity t = case t of
  T_uint n         -> "uint" <> show n
  T_int n          -> "int" <> show n
  T_address        -> "address"
  T_bool           -> "bool"
  T_bytes n        -> "bytes" <> show n
  T_bytes_dynamic  -> "bytes"
  T_string         -> "string"
  T_array_static t n -> abiTypeSolidity t <> "[" <> show n <> "]"
  T_array_dynamic t -> abiTypeSolidity t <> "[]"
  T_tuple ts       -> "(" <> intercalate ", " (fmap abiTypeSolidity ts) <> ")"
