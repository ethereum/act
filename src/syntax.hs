-- data types for the parsed syntax.
-- Has the correct basic structure, but doesn't necessarily type check
-- It is also equipped with position information for extra debugging xp

module Syntax where

type Id = String
  -- deriving (Eq, Ord, Show, Read)

data Act = Main [RawBehaviour]
  deriving (Eq, Ord, Show, Read)

data RawBehaviour
    = Transition Id Id Id [Decl] (Maybe Conditional) TransitionClaim
    -- | Constructor Id Id [Decl] [IffH] ConstructionClaim
  deriving (Eq, Ord, Show, Read)

data ConstructionClaim = CCases [(Expr, Creates)] | CDirect Creates
  deriving (Eq, Ord, Show, Read)

data TransitionClaim = TCases [(Expr, Post)] | TDirect Post
  deriving (Eq, Ord, Show, Read)

data Post
    = Post (Maybe Storage) [ExtStorage] (Maybe Expr)
  deriving (Eq, Ord, Show, Read)

data Creates
    = Creates [Init] [ExtStorage]
  deriving (Eq, Ord, Show, Read)

type Storage = [(Entry, Expr)]

data ExtStorage
    = ExtStorage Expr [(Entry, Expr)]
    | ExtCreates Id Expr [Init]
  deriving (Eq, Ord, Show, Read)

data Init
  = Init Decl Expr
  | InitMany Decl [Defn]
  | InitStruct Decl [Defn]
  deriving (Eq, Ord, Show, Read)

newtype Conditional = Conditional [Expr]
  deriving (Eq, Ord, Show, Read)
-- data IffH = Iff [Expr] | IffIn Type [Expr]
--   deriving (Eq, Ord, Show, Read)

data Entry
  = Simple Id
  | Lookup Entry Expr
  | Struct Entry Id
  deriving (Eq, Ord, Show, Read)

data Defn = Defn Expr Expr
  deriving (Eq, Ord, Show, Read)

data Expr
    = EAnd Expr Expr
    | EOr Expr Expr
    | EImpl Expr Expr
    | EEq Expr Expr
    | ENeq Expr Expr
    | ELe Expr Expr
    | ELt Expr Expr
    | EGe Expr Expr
    | EGt Expr Expr
    | ETrue
    | EFalse
    | EAdd Expr Expr
    | ESub Expr Expr
    | ECond Expr Expr Expr
    | EMul Expr Expr
    | EDiv Expr Expr
    | EMod Expr Expr
    | EExp Expr Expr
    | ECat Expr Expr
    | ESlice Id Expr Expr
    -- why are these names different?
    | Zoom Expr Expr
    | App Id [Expr]
    | Look Id Expr
    | Newaddr Expr Expr
    | Newaddr2 Expr Expr Expr
    | BYHash Expr
    | BYAbiE Expr
    | StringLit String
    | StorageEntry Entry
    | Var Id
    | IntLit Integer
  deriving (Eq, Ord, Show, Read)

data Decl = Decl Type Id
  deriving (Eq, Ord, Show, Read)

data Type
    = T_uint  Int
    | T_int   Int
    | T_bytes Int
    | T_bytes_dynamic
    | T_address
    | T_bool
    | T_string
    | T_array_static  Type Integer
    | T_array_dynamic Type
    | T_map Type Type
    | T_tuple [Type]
    | T_contract Id
  deriving (Eq, Ord, Show, Read)
