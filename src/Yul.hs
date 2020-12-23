{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Yul where
import Prelude hiding (LT, GT, EQ)

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
    "object " ++ show identifier ++ "\n{" ++ show code ++ unlines (showEither <$> objectOrData) ++ "}"

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
  show (Block statements) = "{\n"++ unlines (indent 4 (show <$> statements)) ++ "}"

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
    ++ "\n" ++ show block

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

data FunctionCall =
  UserDefined Identifier [Expression]
  | BuiltIn Instruction
  deriving (Eq, Generic)

instance Show FunctionCall where
  show (UserDefined identifier exprs) =
    show identifier ++ "(" ++ intercalate ", " (show <$> exprs) ++ ")"
  show (BuiltIn instruction) = show instruction

instance Arbitrary FunctionCall where
  arbitrary = genericArbitrary' uniform

newtype Identifier = Id String
  deriving (Eq, Generic, Arbitrary)

instance Show Identifier where
  show (Id a) = a

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

data Instruction
-- control flow
  = STOP               	        -- ^ stop execution, identical to return(0, 0)
  | PC           	  	-- ^ CURRENT POSITION IN CODE
-- * arithmetic
  | ADD  Expression Expression 	-- ^ x + y
  | SUB  Expression Expression 	-- ^ X - Y
  | MUL  Expression Expression  -- ^ X * Y
  | DIV  Expression Expression  -- ^ X / Y OR 0 IF Y == 0
  | SDIV Expression Expression 	-- ^ X / Y, FOR SIGNED NUMBERS IN TWO’S COMPLEMENT, 0 IF Y == 0
  | MOD  Expression Expression 	-- ^ X % Y, 0 IF Y == 0
  | SMOD Expression Expression 	-- ^ X % Y, FOR SIGNED NUMBERS IN TWO’S COMPLEMENT, 0 IF Y == 0
  | EXP  Expression Expression 	-- ^ X TO THE POWER OF Y
  | NOT  Expression 	  	-- ^ BITWISE “NOT” OF X (EVERY BIT OF X IS NEGATED)
  | LT   Expression Expression 	-- ^ 1 IF X < Y, 0 OTHERWISE
  | GT   Expression Expression 	-- ^ 1 IF X > Y, 0 OTHERWISE
  | SLT  Expression Expression 	-- ^ 1 IF X < Y, 0 OTHERWISE, FOR SIGNED NUMBERS IN TWO’S COMPLEMENT
  | SGT  Expression Expression 	-- ^ 1 IF X > Y, 0 OTHERWISE, FOR SIGNED NUMBERS IN TWO’S COMPLEMENT
  | EQ   Expression Expression 	-- ^ 1 IF X == Y, 0 OTHERWISE
  | ISZERO Expression 	  	-- ^ 1 IF X == 0, 0 OTHERWISE
  | AND  Expression Expression  -- ^ BITWISE “AND” OF X AND Y
  | OR   Expression Expression  -- ^ BITWISE “OR” OF X AND Y
  | XOR  Expression Expression  -- ^ BITWISE “XOR” OF X AND Y
  | BYTE Expression Expression  -- ^ NTH BYTE OF X, WHERE THE MOST SIGNIFICANT BYTE IS THE 0TH BYTE
  | SHL  Expression Expression  -- ^ LOGICAL SHIFT LEFT Y BY X BITS
  | SHR  Expression Expression  -- ^ LOGICAL SHIFT RIGHT Y BY X BITS
  | SAR  Expression Expression  -- ^ SIGNED ARITHMETIC SHIFT RIGHT Y BY X BITS
  | ADDMOD Expression Expression Expression -- ^ (X + Y) % M WITH ARBITRARY PRECISION ARITHMETIC, 0 IF M == 0
  | MULMOD Expression Expression Expression -- ^ (X * Y) % M WITH ARBITRARY PRECISION ARITHMETIC, 0 IF M == 0
  | SIGNEXTEND Expression Expression        -- ^ SIGN EXTEND FROM (I*8+7)TH BIT COUNTING FROM LEAST SIGNIFICANT
   -- * hashing
  | KECCAK256  Expression Expression        -- ^ KECCAK(MEM[P…(P+N)))
  | POP Expression	-- ^ DISCARD VALUE X
   -- memory
  | MLOAD Expression            	-- ^ MEM[P…(P+32))
  | MSTORE  Expression Expression 	-- ^ MEM[P…(P+32)) := V
  | MSTORE8 Expression Expression 	-- ^ MEM[P] := V & 0XFF (ONLY MODIFIES A SINGLE BYTE)
  | MSIZE               	  	-- ^ SIZE OF MEMORY, I.E. LARGEST ACCESSED MEMORY INDEX
   -- storage
  | SLOAD Expression             -- ^ STORAGE[P]
  | SSTORE Expression Expression -- ^ STORAGE[P] := V
  -- environment
  | GAS	        	-- ^ GAS STILL AVAILABLE TO EXECUTION
  | ADDRESS 	  	-- ^ ADDRESS OF THE CURRENT CONTRACT / EXECUTION CONTEXT
  | BALANCE Expression 	-- ^ WEI BALANCE AT ADDRESS A
  | SELFBALANCE 	-- ^ EQUIVALENT TO BALANCE(ADDRESS()), BUT CHEAPER
  | CALLER 	  	-- ^ CALL SENDER (EXCLUDING DELEGATECALL)
  | CALLVALUE 	        -- ^ WEI SENT TOGETHER WITH THE CURRENT CALL
  | CHAINID      	-- ^ ID OF THE EXECUTING CHAIN (EIP 1344)
  | ORIGIN      	-- ^ TRANSACTION SENDER
  | GASPRICE      	-- ^ GAS PRICE OF THE TRANSACTION
  | BLOCKHASH Expression -- ^ HASH OF BLOCK NR B - ONLY FOR LAST 256 BLOCKS EXCLUDING CURRENT
  | COINBASE      	-- ^ CURRENT MINING BENEFICIARY
  | TIMESTAMP      	-- ^ TIMESTAMP OF THE CURRENT BLOCK IN SECONDS SINCE THE EPOCH
  | NUMBER      	-- ^ CURRENT BLOCK NUMBER
  | DIFFICULTY      	-- ^ DIFFICULTY OF THE CURRENT BLOCK
  | GASLIMIT      	-- ^ BLOCK GAS LIMIT OF THE CURRENT BLOCK

  -- CALLDATA
  | CALLDATALOAD Expression -- ^ CALL DATA STARTING FROM POSITION P (32 BYTES)
  | CALLDATASIZE            -- ^ SIZE OF CALL DATA IN BYTES
  | CALLDATACOPY Expression Expression Expression -- ^ COPY S BYTES FROM CALLDATA AT POSITION F TO MEM AT POSITION T
  -- CODE
  | CODESIZE  -- ^ SIZE OF THE CODE OF THE CURRENT CONTRACT / EXECUTION CONTEXT
  | CODECOPY Expression Expression Expression -- ^ COPY S BYTES FROM CODE AT POSITION F TO MEM AT POSITION T
  | EXTCODESIZE Expression  -- ^ SIZE OF THE CODE AT ADDRESS A
  | EXTCODECOPY Expression Expression Expression Expression -- ^ LIKE CODECOPY(T, F, S) BUT TAKE CODE AT ADDRESS A
  | EXTCODEHASH Expression -- ^ CODE HASH OF ADDRESS A
  -- RETURNDATA
  | RETURNDATASIZE 	  	 -- ^SIZE OF THE LAST RETURNDATA
  | RETURNDATACOPY Expression Expression Expression -- ^ COPY S BYTES FROM RETURNDATA AT POSITION F TO MEM AT POSITION T
  -- CREATION
  | CREATE Expression Expression Expression -- ^ CREATE NEW CONTRACT WITH CODE MEM[P…(P+N)) AND SEND V WEI AND RETURN THE NEW ADDRESS
  | CREATE2 Expression Expression Expression Expression -- ^ CREATE NEW CONTRACT WITH CODE MEM[P…(P+N)) AT ADDRESS KECCAK256(0XFF . THIS . S . KECCAK256(MEM[P…(P+N))) AND SEND V WEI AND RETURN THE NEW ADDRESS, WHERE 0XFF IS A 1 BYTE VALUE, THIS IS THE CURRENT CONTRACT’S ADDRESS AS A 20 BYTE VALUE AND S IS A BIG-ENDIAN 256-BIT VALUE
  -- CALLS
  | CALL Expression Expression Expression Expression Expression Expression Expression  -- ^ CALL CONTRACT AT ADDRESS A WITH INPUT MEM[IN…(IN+INSIZE)) PROVIDING G GAS AND V WEI AND OUTPUT AREA MEM[OUT…(OUT+OUTSIZE)) RETURNING 0 ON ERROR (EG. OUT OF GAS) AND 1 ON SUCCESS SEE MORE
  | CALLCODE     Expression Expression Expression Expression Expression Expression  -- ^ IDENTICAL TO CALL BUT ONLY USE THE CODE FROM A AND STAY IN THE CONTEXT OF THE CURRENT CONTRACT OTHERWISE SEE MORE
  | DELEGATECALL Expression Expression Expression Expression Expression Expression  -- ^ IDENTICAL TO CALLCODE BUT ALSO KEEP CALLER AND CALLVALUE SEE MORE
  | STATICCALL   Expression Expression Expression Expression Expression Expression  -- ^ IDENTICAL TO CALL(G, A, 0, IN, INSIZE, OUT, OUTSIZE) BUT DO NOT ALLOW STATE MODIFICATIONS SEE MORE
  -- MISC
  | RETURN Expression Expression -- ^ END EXECUTION, RETURN DATA MEM[P…(P+S))
  | REVERT Expression Expression  -- ^ END EXECUTION, REVERT STATE CHANGES, RETURN DATA MEM[P…(P+S))
  | SELFDESTRUCT Expression  -- ^ END EXECUTION, DESTROY CURRENT CONTRACT AND SEND FUNDS TO A
  | INVALID  -- ^ END EXECUTION WITH INVALID INSTRUCTION
-- LOGGING
  | LOG0 Expression Expression  -- ^ LOG WITHOUT TOPICS AND DATA MEM[P…(P+S))
  | LOG1 Expression Expression Expression -- ^ 	log with topic t1 and data mem[p…(p+s))
  | LOG2 Expression Expression Expression Expression -- ^ log with topics t1, t2 and data mem[p…(p+s))
  | LOG3 Expression Expression Expression Expression Expression  -- ^ log with topics t1, t2, t3 and data mem[p…(p+s))
  | LOG4 Expression Expression Expression Expression Expression Expression  -- ^ log with topics t1, t2, t3, t4 and data mem[p…(p+s))
  deriving (Eq, Generic, Arbitrary) -- show instance needs tweakin

instance Show Instruction where
  show i =
    let
      show' :: String -> [Expression] -> String
      show' s args = s ++ "(" ++ intercalate ", " (show <$> args) ++ ")"
    in case i of
      STOP -> show' "stop" []
      PC -> show' "pc" [] 
--     arithmetic
      ADD  x y -> show' "add" [x, y]
      SUB  x y -> show' "sub" [x, y]
      MUL  x y -> show' "mul" [x, y]
      DIV  x y -> show' "div" [x, y]
      SDIV x y -> show' "sdiv" [x, y]
      MOD  x y -> show' "mod" [x, y]
      SMOD x y -> show' "smod" [x, y]
      EXP  x y -> show' "exp" [x, y]
      NOT  x   -> show' "not" [x]
      LT   x y -> show' "lt" [x, y] 
      GT   x y -> show' "gt" [x, y] 
      SLT  x y -> show' "slt" [x, y] 
      SGT  x y -> show' "sgt" [x, y] 
      EQ   x y -> show' "eq" [x, y] 
      ISZERO x -> show' "iszero" [x]
      AND  x y -> show' "and" [x, y]
      OR   x y -> show' "or" [x, y]
      XOR  x y -> show' "xor" [x, y]
      BYTE x y -> show' "byte" [x, y]
      SHL  x y -> show' "shl" [x, y]
      SHR  x y -> show' "shr" [x, y]
      SAR  x y -> show' "sar" [x, y]
      REVERT x y -> show' "revert" [x, y]
      _ -> error "todo"
--   ADDMOD Expression Expression Expression -- ^ (X + Y) % M WITH ARBITRARY PRECISION ARITHMETIC, 0 IF M == 0
--   MULMOD Expression Expression Expression -- ^ (X * Y) % M WITH ARBITRARY PRECISION ARITHMETIC, 0 IF M == 0
--   SIGNEXTEND Expression Expression        -- ^ SIGN EXTEND FROM (I*8+7)TH BIT COUNTING FROM LEAST SIGNIFICANT
--   - * hashing
--   KECCAK256  Expression Expression        -- ^ KECCAK(MEM[P…(P+N)))
--   POP Expression	-- ^ DISCARD VALUE X
--   - memory
--   MLOAD Expression            	-- ^ MEM[P…(P+32))
--   MSTORE  Expression Expression 	-- ^ MEM[P…(P+32)) := V
--   | MSTORE8 Expression Expression 	-- ^ MEM[P] := V & 0XFF (ONLY MODIFIES A SINGLE BYTE)
--   | MSIZE               	  	-- ^ SIZE OF MEMORY, I.E. LARGEST ACCESSED MEMORY INDEX
--    -- storage
--   | SLOAD Expression             -- ^ STORAGE[P]
--   | SSTORE Expression Expression -- ^ STORAGE[P] := V
--   -- environment
--   | GAS	        	-- ^ GAS STILL AVAILABLE TO EXECUTION
--   | ADDRESS 	  	-- ^ ADDRESS OF THE CURRENT CONTRACT / EXECUTION CONTEXT
--   | BALANCE Expression 	-- ^ WEI BALANCE AT ADDRESS A
--   | SELFBALANCE 	-- ^ EQUIVALENT TO BALANCE(ADDRESS()), BUT CHEAPER
--   | CALLER 	  	-- ^ CALL SENDER (EXCLUDING DELEGATECALL)
--   | CALLVALUE 	        -- ^ WEI SENT TOGETHER WITH THE CURRENT CALL
--   | CHAINID      	-- ^ ID OF THE EXECUTING CHAIN (EIP 1344)
--   | ORIGIN      	-- ^ TRANSACTION SENDER
--   | GASPRICE      	-- ^ GAS PRICE OF THE TRANSACTION
--   | BLOCKHASH Expression -- ^ HASH OF BLOCK NR B - ONLY FOR LAST 256 BLOCKS EXCLUDING CURRENT
--   | COINBASE      	-- ^ CURRENT MINING BENEFICIARY
--   | TIMESTAMP      	-- ^ TIMESTAMP OF THE CURRENT BLOCK IN SECONDS SINCE THE EPOCH
--   | NUMBER      	-- ^ CURRENT BLOCK NUMBER
--   | DIFFICULTY      	-- ^ DIFFICULTY OF THE CURRENT BLOCK
--   | GASLIMIT      	-- ^ BLOCK GAS LIMIT OF THE CURRENT BLOCK

--   -- CALLDATA
--   | CALLDATALOAD Expression -- ^ CALL DATA STARTING FROM POSITION P (32 BYTES)
--   | CALLDATASIZE            -- ^ SIZE OF CALL DATA IN BYTES
--   | CALLDATACOPY Expression Expression Expression -- ^ COPY S BYTES FROM CALLDATA AT POSITION F TO MEM AT POSITION T
--   -- CODE
--   | CODESIZE  -- ^ SIZE OF THE CODE OF THE CURRENT CONTRACT / EXECUTION CONTEXT
--   | CODECOPY Expression Expression Expression -- ^ COPY S BYTES FROM CODE AT POSITION F TO MEM AT POSITION T
--   | EXTCODESIZE Expression  -- ^ SIZE OF THE CODE AT ADDRESS A
--   | EXTCODECOPY Expression Expression Expression Expression -- ^ LIKE CODECOPY(T, F, S) BUT TAKE CODE AT ADDRESS A
--   | EXTCODEHASH Expression -- ^ CODE HASH OF ADDRESS A
--   -- RETURNDATA
--   | RETURNDATASIZE 	  	 -- ^SIZE OF THE LAST RETURNDATA
--   | RETURNDATACOPY Expression Expression Expression -- ^ COPY S BYTES FROM RETURNDATA AT POSITION F TO MEM AT POSITION T
--   -- CREATION
--   | CREATE Expression Expression Expression -- ^ CREATE NEW CONTRACT WITH CODE MEM[P…(P+N)) AND SEND V WEI AND RETURN THE NEW ADDRESS
--   | CREATE2 Expression Expression Expression Expression -- ^ CREATE NEW CONTRACT WITH CODE MEM[P…(P+N)) AT ADDRESS KECCAK256(0XFF . THIS . S . KECCAK256(MEM[P…(P+N))) AND SEND V WEI AND RETURN THE NEW ADDRESS, WHERE 0XFF IS A 1 BYTE VALUE, THIS IS THE CURRENT CONTRACT’S ADDRESS AS A 20 BYTE VALUE AND S IS A BIG-ENDIAN 256-BIT VALUE
--   -- CALLS
--   | CALL Expression Expression Expression Expression Expression Expression Expression  -- ^ CALL CONTRACT AT ADDRESS A WITH INPUT MEM[IN…(IN+INSIZE)) PROVIDING G GAS AND V WEI AND OUTPUT AREA MEM[OUT…(OUT+OUTSIZE)) RETURNING 0 ON ERROR (EG. OUT OF GAS) AND 1 ON SUCCESS SEE MORE
--   | CALLCODE     Expression Expression Expression Expression Expression Expression  -- ^ IDENTICAL TO CALL BUT ONLY USE THE CODE FROM A AND STAY IN THE CONTEXT OF THE CURRENT CONTRACT OTHERWISE SEE MORE
--   | DELEGATECALL Expression Expression Expression Expression Expression Expression  -- ^ IDENTICAL TO CALLCODE BUT ALSO KEEP CALLER AND CALLVALUE SEE MORE
--   | STATICCALL   Expression Expression Expression Expression Expression Expression  -- ^ IDENTICAL TO CALL(G, A, 0, IN, INSIZE, OUT, OUTSIZE) BUT DO NOT ALLOW STATE MODIFICATIONS SEE MORE
--   -- MISC
--   | RETURN Expression Expression -- ^ END EXECUTION, RETURN DATA MEM[P…(P+S))

--   | SELFDESTRUCT Expression  -- ^ END EXECUTION, DESTROY CURRENT CONTRACT AND SEND FUNDS TO A
--   | INVALID  -- ^ END EXECUTION WITH INVALID INSTRUCTION
-- -- LOGGING
--   | LOG0 Expression Expression  -- ^ LOG WITHOUT TOPICS AND DATA MEM[P…(P+S))
--   | LOG1 Expression Expression Expression -- ^ 	log with topic t1 and data mem[p…(p+s))
--   | LOG2 Expression Expression Expression Expression -- ^ log with topics t1, t2 and data mem[p…(p+s))
--   | LOG3 Expression Expression Expression Expression Expression  -- ^ log with topics t1, t2, t3 and data mem[p…(p+s))
--   | LOG4 Expression Expression Expression Expression Expression Expression  -- ^ log with topics t

showEither :: (Show a, Show b) => Either a b -> String
showEither = either show show

showMaybe :: (Show a) => Maybe a -> String
showMaybe = maybe "" show

curly :: String -> String
curly s = "{" ++ s ++ "}"

indent :: Int -> [String] -> [String]
indent n = fmap (replicate n ' ' ++)
