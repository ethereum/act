{-# LANGUAGE GADTs #-}

module Syntax where

class Coq a where
  coq :: a -> String

type Id = String
type Decl = (Type, Id)
type AST = [Behaviour]

data Type
  = UInt
  | Boole
  deriving (Show)

instance Coq Type where
  coq UInt = "uint"
  coq Boole = "boole"

data Expr
  -- numbers
  = EIntLit Integer
  | EAdd Expr Expr
  | EMul Expr Expr
  | ESub Expr Expr
  | EDiv Expr Expr

  -- booleans
  | EBooLit Bool
  | EEq Expr Expr
  | ENeq Expr Expr
  deriving (Show)

data Behaviour
  = Transition  Id Id Interface (Maybe Precondition) [Case]
  | Constructor Id Id Interface [Creation]
  deriving (Show)

data Interface
  = Interface Id [Decl]
  deriving (Show)

data Creation
  = Creation Decl Expr
  deriving (Show)

data Precondition
  = Precondition [Expr]
  deriving (Show)

data Case
  = Case Expr [Claim]
  deriving (Show)

data Claim
  = Storage [Write]
  | Returns Expr
  deriving (Show)

data Write
  = Write Address Expr
  deriving (Show)

data Address
  = Address Id
  deriving (Show)


