-- data types for the parsed syntax.
-- Has the correct basic structure, but doesn't necessarily type check
-- It is also equipped with position information for extra debugging xp
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax where
import Data.List          (intercalate)
data Pn = P !Int !Int !Int
   deriving (Eq, Read, Ord, Show)

type Id = String

data Act = Main [RawBehaviour]
  deriving (Eq, Ord, Show, Read)

data RawBehaviour
    = Transition Id Id Interface [IffH] TransitionClaim (Maybe Ensures)
    | Constructor Id Id Interface [IffH] ConstructionClaim (Maybe Ensures)
  deriving (Eq, Ord, Show, Read)

type Ensures = [Expr]

data Interface = Interface Id [Decl]
  deriving (Eq, Ord, Read)

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

data ConstructionClaim = CCases Pn [(Expr, PostCreates)] | CDirect PostCreates
  deriving (Eq, Ord, Show, Read)

data TransitionClaim = TCases [Case] | TDirect Post
  deriving (Eq, Ord, Show, Read)

data Case
    = Case Pn Expr Post
  deriving (Eq, Ord, Show, Read)

data Post
    = Post (Maybe Storage) [ExtStorage] (Maybe Expr)
  deriving (Eq, Ord, Show, Read)

data PostCreates
    = PostCreates [Assign] [ExtStorage]
  deriving (Eq, Ord, Show, Read)

type Storage = [(Entry, Expr)]

data ExtStorage
    = ExtStorage Id [(Entry, Expr)]
    | ExtCreates Id Expr [Assign]
  deriving (Eq, Ord, Show, Read)

data Assign = Assignval StorageDecl Expr | AssignMany StorageDecl [Defn] | AssignStruct StorageDecl [Defn]
  deriving (Eq, Ord, Show, Read)

data IffH = Iff Pn [Expr] | IffIn Pn Type [Expr]
  deriving (Eq, Ord, Show, Read)

data Entry
--  = Entry Pn Id [Either Expr Id] TODO
  = Entry Pn Id [Expr]
  deriving (Eq, Ord, Show, Read)

data Defn = Defn Pn Expr Expr
  deriving (Eq, Ord, Show, Read)

data Expr
    = EAnd Pn Expr Expr
    | EOr Pn Expr Expr
    | EImpl Pn Expr Expr
    | EEq Pn Expr Expr
    | ENeq Pn Expr Expr
    | ELEQ Pn Expr Expr
    | ELE Pn Expr Expr
    | EGEQ Pn Expr Expr
    | EGE Pn Expr Expr
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
    | EntryExp Entry
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
    | Var Pn Id
    | EnvExpr Pn EthEnv
    | IntLit Pn Integer
  deriving (Eq, Ord, Show, Read)

data EthEnv
   = CALLER
   | CALLVALUE
   | BLOCKNUMBER
   | TXORIGIN
   | BLOCKHASH
  deriving (Eq, Ord, Show, Read)

data StorageDecl = StorageDec Container Id
  deriving (Eq, Ord, Show, Read)

data Decl = Dec Type Id
  deriving (Eq, Ord, Read)

instance Show Decl where
  show (Dec t a) = show t <> " " <> a

-- storage types
data Container
   = Direct Type
   | Mapping Type Container
  deriving (Eq, Ord, Show, Read)

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
  deriving (Eq, Ord, Read)

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
