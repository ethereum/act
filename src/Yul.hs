{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Yul where

--import Data.Generic
import EVM.Types (ByteStringS(..))
import qualified Data.ByteString as BS
import Data.List.NonEmpty
import Test.Tasty.QuickCheck
import GHC.Generics
import Generic.Random

data Object = Object StringLiteral Code [Either Object Data]
  deriving (Eq) --, Generic)

instance Show Object where
  show (Object identifier code objectOrData) =
    "object " ++ show identifier ++ "{" ++ show code ++ unlines (either show show <$> objectOrData) ++ "}"

data Code = Code Block
  deriving (Eq)

instance Show Code where
  show (Code block) = "code " ++ show block

data Data = Data StringLiteral (Either HexLiteral StringLiteral)
  deriving (Eq)

instance Show Data where
  show (Data stringlit hexOrStringlit) =
    "data" ++ show stringlit ++ either show show hexOrStringlit

data HexLiteral = HexLiteral ByteStringS
  deriving (Eq)

instance Show HexLiteral where
  show (HexLiteral hex) = "hex" ++ show (show hex)

type StringLiteral = String

data Block = Block [Statement]
  deriving (Eq)

instance Show Block where
  show (Block statements) = "{" ++ unlines (show <$> statements) ++ "}"

data Statement =
    StmtBlock Block
  | StmtFuncDef FunctionDefinition
  | StmtVarDecl VariableDeclaration
  | StmtAssign Assignment
  | StmtIf If
  | StmtExpr Expression
  | StmtSwitch Switch
  | StmtFor ForLoop
  | StmtBrCont BreakContinue
  | StmtLeave Leave
  deriving (Eq, Show)

data FunctionDefinition =
  FunctionDefinition Identifier (Maybe TypedIdentifierList) (Maybe TypedIdentifierList) Block
  deriving (Eq)

instance Show FunctionDefinition where
  show (FunctionDefinition
        identifier
        maybeInputTypes
        maybeOutputTypes
        block) =
    "function "
    ++ show identifier
    ++ "(" ++ maybe "" show maybeInputTypes ++ ")"
    ++ "(" ++ maybe "" ((++) " -> " . show) maybeOutputTypes
    ++ show block

data VariableDeclaration =
  VariableDeclaration TypedIdentifierList (Maybe Expression)
  deriving (Eq)

instance Show VariableDeclaration where
  show (VariableDeclaration typedIdList maybeExpr) =
    "let " ++ show typedIdList ++ maybe "" ((++) " := " . show) maybeExpr

data Assignment = Assignment (NonEmpty Identifier) Expression
  deriving (Eq)

instance Show Assignment where
  show (Assignment ids expr) =
    show ids ++ " := " ++ show expr

type Expression = Either FunctionCall (Either Identifier Literal)

data If = If Expression Block
  deriving (Eq)

instance Show If where
  show (If expr block) = "if " ++ show expr ++ show block

data Switch = Switch Expression (Either (NonEmpty Case, Maybe Default) Default)
  deriving (Eq)

instance Show Switch where
  show (Switch expr cases) = "switch " ++ show expr ++ either show show cases

data Case = Case Literal Block deriving (Eq)

instance Show Case where
  show (Case literal block) = "case " ++ show literal ++ show block

data Default = Default Block
  deriving (Eq)

instance Show Default where
  show (Default block) = "default " ++ show block

data ForLoop = ForLoop Block Expression Block Block
  deriving (Eq)

instance Show ForLoop where
  show (ForLoop block expr block' block'') =
    "for " ++ show block ++ show expr ++ show block' ++ show block''

data BreakContinue = Break | Continue
  deriving (Show, Eq)

data Leave = Leave
  deriving (Eq)

instance Show Leave where
  show Leave = "leave"

data FunctionCall = FunctionCall Identifier [Expression]
  deriving (Eq, Generic)

instance Show FunctionCall where
  show (FunctionCall identifier exprs) =
    show identifier ++ "(" ++ show exprs ++ ")"

instance Arbitrary FunctionCall where
  arbitrary = genericArbitrary uniform

type Identifier = String

type TypeName = Identifier

type TypedIdentifierList = NonEmpty (Identifier, Maybe TypeName)

newtype TypedLiteral = TypedLiteral (Literal, TypeName) deriving (Eq, Generic)

instance Arbitrary TypedLiteral where
  arbitrary = genericArbitrary uniform

instance Show TypedLiteral where
  show (TypedLiteral (lit, typename)) =
    show lit ++ ":" ++ show typename

data Literal =
    LitInteger Integer
  | LitByteString ByteStringS
  | LitString StringLiteral
  | LitBool Bool
  deriving (Eq, Generic)

instance Show Literal where
  show (LitInteger s) = show s
  show (LitByteString s) = show s
  show (LitString s) = show s
  show (LitBool b) = if b then "true" else "false"

instance Arbitrary Literal where
  arbitrary = genericArbitrary uniform

instance Arbitrary ByteStringS where
  arbitrary = ByteStringS . BS.pack <$> arbitrary

data NumberLiteral = Either ByteStringS Integer
