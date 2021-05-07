-- data types for the parsed syntax.
-- Has the correct basic structure, but doesn't necessarily type check
-- It is also equipped with position information for extra debugging xp
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax where
import Data.List (intercalate)
import Data.Map (Map,empty,insert,unionsWith)
import EVM.ABI (AbiType)
import EVM.Solidity (SlotType)
import Lex

type Pn = AlexPosn

type Id = String

newtype Act = Main [RawBehaviour]
  deriving (Eq, Show)

data RawBehaviour
    = Transition Id Id Interface [IffH] Cases Ensures
    | Definition Id Interface [IffH] Creates [ExtStorage] Ensures Invariants
  deriving (Eq, Show)

type Ensures = [Expr]

type Invariants = [Expr]

data Interface = Interface Id [Decl]
  deriving (Eq)

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

data Cases =
  Direct Post
  | Branches [Case]
  deriving (Eq, Show)

data Case = Case Pn Expr Post
  deriving (Eq, Show)

data Post
    = Post (Maybe [Storage]) [ExtStorage] (Maybe Expr)
  deriving (Eq, Show)

newtype Creates = Creates [Assign]
  deriving (Eq, Show)

data Storage = Rewrite Entry Expr
             | Constant Entry
  deriving (Eq, Show)

data ExtStorage
    = ExtStorage Id [Storage]
    | ExtCreates Id Expr [Assign]
    | WildStorage
  deriving (Eq, Show)

data Assign = AssignVal StorageVar Expr | AssignMany StorageVar [Defn] | AssignStruct StorageVar [Defn]
  deriving (Eq, Show)

data IffH = Iff Pn [Expr] | IffIn Pn AbiType [Expr]
  deriving (Eq, Show)

data Entry
  = Entry Pn Id [Expr]
  | Wild
  deriving (Eq, Show)

data Defn = Defn Expr Expr
  deriving (Eq, Show)

data Expr
    = EAnd Pn Expr Expr
    | EOr Pn Expr Expr
    | ENot Pn Expr
    | EImpl Pn Expr Expr
    | EEq Pn Expr Expr
    | ENeq Pn Expr Expr
    | ELEQ Pn Expr Expr
    | ELT Pn Expr Expr
    | EGEQ Pn Expr Expr
    | EGT Pn Expr Expr
    | EAdd Pn Expr Expr
    | ESub Pn Expr Expr
    | EITE Pn Expr Expr Expr
    | EMul Pn Expr Expr
    | EDiv Pn Expr Expr
    | EMod Pn Expr Expr
    | EExp Pn Expr Expr
    | Zoom Pn Expr Expr
    | EntryExp Pn Id [Expr]
--    | Look Pn Id [Expr]
    | Func Pn Id [Expr]
    | ListConst Expr
    | ECat Pn Expr Expr
    | ESlice Pn Expr Expr Expr
    | ENewaddr Pn Expr Expr
    | ENewaddr2 Pn Expr Expr Expr
    | BYHash Pn Expr
    | BYAbiE Pn Expr
    | StringLit Pn String
    | WildExp Pn
    | EnvExp Pn EthEnv
    | IntLit Pn Integer
    | BoolLit Pn Bool
  deriving (Eq, Show)

data EthEnv
   = Caller
   | Callvalue
   | Calldepth
   | Origin
   | Blockhash
   | Blocknumber
   | Difficulty
   | Chainid
   | Gaslimit
   | Coinbase
   | Timestamp
   | This
   | Nonce
  deriving (Show, Eq)

data StorageVar = StorageVar SlotType Id
  deriving (Eq, Show)

data Decl = Decl AbiType Id
  deriving (Eq)

instance Show Decl where
  show (Decl t a) = show t <> " " <> a

getPosn :: Expr -> Pn
getPosn expr = case expr of
    EAnd pn  _ _ -> pn
    EOr pn _ _ -> pn
    ENot pn _ -> pn
    EImpl pn _ _ -> pn
    EEq pn _ _ -> pn
    ENeq pn _ _ -> pn
    ELEQ pn _ _ -> pn
    ELT pn _ _ -> pn
    EGEQ pn _ _ -> pn
    EGT pn _ _ -> pn
    EAdd pn _ _ -> pn
    ESub pn _ _ -> pn
    EITE pn _ _ _ -> pn
    EMul pn _ _ -> pn
    EDiv pn _ _ -> pn
    EMod pn _ _ -> pn
    EExp pn _ _ -> pn
    Zoom pn _ _ -> pn
    EntryExp pn _ _ -> pn
    Func pn _ _ -> pn
    ListConst e -> getPosn e
    ECat pn _ _ -> pn
    ESlice pn _ _ _ -> pn
    ENewaddr pn _ _ -> pn
    ENewaddr2 pn _ _ _ -> pn
    BYHash pn _ -> pn
    BYAbiE pn _ -> pn
    StringLit pn _ -> pn
    WildExp pn -> pn
    EnvExp pn _ -> pn
    IntLit pn _ -> pn
    BoolLit pn _ -> pn

-- | Returns all the identifiers used in an expression,
-- as well all of the positions they're used in.
getIds :: Expr -> Map Id [Pn]
getIds e = case e of
  EAnd _ a b        -> getIds a <> getIds b
  EOr _ a b         -> getIds a <> getIds b
  ENot _ a          -> getIds a
  EImpl _ a b       -> getIds a <> getIds b
  EEq _ a b         -> getIds a <> getIds b
  ENeq _ a b        -> getIds a <> getIds b
  ELEQ _ a b        -> getIds a <> getIds b
  ELT _ a b         -> getIds a <> getIds b
  EGEQ _ a b        -> getIds a <> getIds b
  EGT _ a b         -> getIds a <> getIds b
  EAdd _ a b        -> getIds a <> getIds b
  ESub _ a b        -> getIds a <> getIds b
  EITE _ a b c      -> getIds a <> getIds b <> getIds c
  EMul _ a b        -> getIds a <> getIds b
  EDiv _ a b        -> getIds a <> getIds b
  EMod _ a b        -> getIds a <> getIds b
  EExp _ a b        -> getIds a <> getIds b
  Zoom _ a b        -> getIds a <> getIds b
  EntryExp p x es   -> insert x [p] . unionsWith (<>) $ getIds <$> es
  Func _ _ es       -> unionsWith (<>) $ getIds <$> es
  ListConst a       -> getIds a
  ECat _ a b        -> getIds a <> getIds b
  ESlice _ a b c    -> getIds a <> getIds b <> getIds c
  ENewaddr _ a b    -> getIds a <> getIds b
  ENewaddr2 _ a b c -> getIds a <> getIds b <> getIds c
  BYHash _ a        -> getIds a
  BYAbiE _ a        -> getIds a
  StringLit {}      -> empty
  WildExp {}        -> empty
  EnvExp {}         -> empty
  IntLit {}         -> empty
  BoolLit {}        -> empty