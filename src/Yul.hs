{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Yul where

import EVM.Types (ByteStringS(..))
import qualified Data.ByteString as BS
import Data.List.NonEmpty
import Data.List
import Test.Tasty.QuickCheck
import GHC.Generics
import Generic.Random

data Object = Object StringLiteral Code [Either Object Data]
  deriving (Eq, Generic)

instance Show Object where
  show (Object identifier code objectOrData) =
    "object " ++ show identifier ++ "{" ++ show code ++ unlines (showEither <$> objectOrData) ++ "}"



instance Arbitrary Object where
  arbitrary = genericArbitrary' uniform

data Code = Code Block
  deriving (Eq, Generic)

instance Arbitrary Code where
  arbitrary = genericArbitrary' uniform

instance Show Code where
  show (Code block) = "code " ++ show block

data Data = Data StringLiteral (Either HexLiteral StringLiteral)
  deriving (Eq, Generic)

instance Arbitrary Data where
  arbitrary = genericArbitrary uniform

instance Show Data where
  show (Data stringlit hexOrStringlit) =
    "data" ++ show stringlit ++ showEither hexOrStringlit

newtype HexLiteral = HexLiteral ByteStringS
  deriving (Eq, Generic)

instance Show HexLiteral where
  show (HexLiteral hex) = "hex" ++ show (show hex)

instance Arbitrary HexLiteral where
  arbitrary = genericArbitrary uniform

type StringLiteral = Identifier

data Block = Block [Statement]
  deriving (Eq, Generic)

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
  deriving (Eq, Generic)

instance Show Statement where
  show (StmtBlock b) = show b
  show (StmtFuncDef b) = show b
  show (StmtVarDecl b) = show b
  show (StmtAssign b) = show b
  show (StmtIf b) = show b
  show (StmtExpr b) = show b
  show (StmtSwitch b) = show b
  show (StmtFor b) = show b
  show (StmtBrCont b) = show b
  show (StmtLeave b) = show b

instance Arbitrary Statement where
  arbitrary = genericArbitrary' uniform

data FunctionDefinition =
  FunctionDefinition Identifier (Maybe TypedIdentifierList) (Maybe TypedIdentifierList) Block
  deriving (Eq, Generic)

instance Arbitrary FunctionDefinition where
  arbitrary = genericArbitrary' uniform

instance Show FunctionDefinition where
  show (FunctionDefinition
        identifier
        maybeInputTypes
        maybeOutputTypes
        block) =
    "function "
    ++ show identifier
    ++ "(" ++ showMaybe maybeInputTypes ++ ")"
    ++ maybe "" ((++) " -> " . show) maybeOutputTypes
    ++ show block

data VariableDeclaration =
  VariableDeclaration TypedIdentifierList (Maybe Expression)
  deriving (Eq, Generic)

instance Arbitrary VariableDeclaration where
  arbitrary = genericArbitrary uniform

instance Show VariableDeclaration where
  show (VariableDeclaration typedIdList maybeExpr) =
    "let " ++ show typedIdList ++ maybe "" ((++) " := " . show) maybeExpr

data Assignment = Assignment (NEmpty Identifier) Expression
  deriving (Eq, Generic)

instance Arbitrary Assignment where
  arbitrary = genericArbitrary uniform

instance Show Assignment where
  show (Assignment ids expr) =
    show ids ++ " := " ++ show expr

data Expression =
    ExprFunCall FunctionCall
  | ExprIdent Identifier
  | ExprLit Literal
  deriving (Eq, Generic)

instance Show Expression where
  show (ExprFunCall func) = show func
  show (ExprIdent  ident) = show ident
  show (ExprLit    liter) = show liter

instance Arbitrary Expression where
  arbitrary = genericArbitrary uniform


data If = If Expression Block
  deriving (Eq, Generic)

instance Show If where
  show (If expr block) = "if " ++ show expr ++ "\n" ++ show block

instance Arbitrary If where
  arbitrary = genericArbitrary uniform

data Switch = Switch Expression (Either (NEmpty Case, Maybe Default) Default)
  deriving (Eq, Generic)

instance Arbitrary Switch where
  arbitrary = genericArbitrary uniform

instance Show Switch where
  show (Switch expr cases) = "switch " ++ show expr ++ "\n" ++
    either (\(c,d) -> show c ++ showMaybe d)  show cases

data Case = Case Literal Block deriving (Eq, Generic)

instance Arbitrary Case where
  arbitrary = genericArbitrary uniform

instance Show Case where
  show (Case literal block) = "case " ++ show literal ++ "\n" ++ show block

data Default = Default Block
  deriving (Eq, Generic)

instance Show Default where
  show (Default block) = "default " ++ show block

instance Arbitrary Default where
  arbitrary = genericArbitrary' uniform


instance Arbitrary Block where
  arbitrary = genericArbitrary' uniform

data ForLoop = ForLoop Block Expression Block Block
  deriving (Eq, Generic)

instance Arbitrary ForLoop where
  arbitrary = genericArbitrary uniform

instance Show ForLoop where
  show (ForLoop block expr block' block'') =
    "for " ++ show block ++ " " ++ show expr ++ "\n" ++ show block' ++ show block''

data BreakContinue = Break | Continue
  deriving (Eq, Generic)

instance Show BreakContinue where
  show Break = "break"
  show Continue = "continue"

instance Arbitrary BreakContinue where
  arbitrary = genericArbitrary' uniform

data Leave = Leave
  deriving (Eq, Generic)

instance Arbitrary Leave where
  arbitrary = genericArbitrary' uniform

instance Show Leave where
  show Leave = "leave"

data FunctionCall = FunctionCall Identifier [Expression]
  deriving (Eq, Generic)

instance Show FunctionCall where
  show (FunctionCall identifier exprs) =
    show identifier ++ "(" ++ intercalate ", " (show <$> exprs) ++ ")"

instance Arbitrary FunctionCall where
  arbitrary = genericArbitrary' uniform

type Identifier = String

type TypeName = Identifier

newtype TypedIdentifierList = TypedIdentifierList (NEmpty (Identifier, Maybe TypeName)) deriving (Eq, Generic)

instance Show TypedIdentifierList where
  show (TypedIdentifierList (NEmpty ids)) = intercalate ", " $ toList $ (\(i,t) -> (show i) ++ (maybe "" ((++) " : " . show) t)) <$> ids

instance Arbitrary TypedIdentifierList where
  arbitrary = genericArbitrary' uniform

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

newtype NEmpty a = NEmpty (NonEmpty a) deriving (Eq, Generic)

instance Show a => Show (NEmpty a) where
  show (NEmpty (a :| xs)) =
    show a ++
    if null xs then
      ""
    else ", " ++ intercalate ", " (show <$> xs)

instance (Arbitrary a) => Arbitrary (NEmpty a) where
  arbitrary = genericArbitrary uniform

instance (Arbitrary a) => Arbitrary (NonEmpty a) where
  arbitrary = genericArbitrary uniform


showEither :: (Show a, Show b) => Either a b -> String
showEither = either show show

showMaybe :: (Show a) => Maybe a -> String
showMaybe = maybe "" show
