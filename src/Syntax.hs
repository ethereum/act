-- data types for the parsed syntax.
-- Has the correct basic structure, but doesn't necessarily type check
-- It is also equipped with position information for extra debugging xp

module Syntax where

data Pn = P !Int !Int !Int
   deriving (Eq, Read, Show,Ord)

type Id = (Pn, String)

data Act = Main [RawBehaviour]
  deriving (Eq, Ord, Show, Read)

data RawBehaviour
    = Transition Id Id Id [Decl] [IffH] TransitionClaim
    | Constructor Id Id [Decl] [IffH] ConstructionClaim
  deriving (Eq, Ord, Show, Read)

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
    = ExtStorage Expr [(Entry, Expr)]
    | ExtCreates Id Expr [Assign]
  deriving (Eq, Ord, Show, Read)

data Assign = Assignval Decl Expr | AssignMany Decl [Defn] | AssignStruct Decl [Defn]
  deriving (Eq, Ord, Show, Read)

data IffH = Iff Pn [Expr] | IffIn Pn Type [Expr]
  deriving (Eq, Ord, Show, Read)

data Entry
  = Simple Pn Id
  | Lookup Pn Entry Expr
  | Struct Pn Entry Id
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
    | Func Pn Id [Expr]
    | Look Pn Expr Expr
    | ECat Pn Expr Expr
    | ESlice Pn Expr Expr Expr
    | Newaddr Pn Expr Expr
    | Newaddr2 Pn Expr Expr Expr
    | BYHash Pn Expr
    | BYAbiE Pn Expr
    | StringLit Pn String
    | StorageEntry Pn Entry
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

data Decl = Dec Type Id
  deriving (Eq, Ord, Show, Read)

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
    | T_map Type Type
    | T_tuple [Type]
    | T_contract Id
  deriving (Eq, Ord, Show, Read)
