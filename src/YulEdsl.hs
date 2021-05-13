{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RebindableSyntax #-}
-- {-# LANGUAGE OverloadedStrings #-}
module YulEdsl where

import Prelude hiding (Word, and, not, or, EQ, LT, GT, div) --, (>>), (>>=), return)

import Data.List.NonEmpty hiding (head, take)
import Data.List (elemIndex)
import Yul
import Data.Coerce (coerce)
import GHC.Base (Coercible, join)
import Data.Data (Proxy(..))
import Control.Monad.Trans.Writer
--import Control.Monad.State
import Data.Map (Map)
--import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Lazy (toStrict)
import Data.Text (Text, pack)
import Data.Aeson           (ToJSON(..), (.=), object, encode)
import Data.Text.Encoding   (decodeUtf8)
import qualified Data.Text as Text
import System.Process
import System.IO hiding     (readFile, writeFile)
import System.IO.Temp

--import Data.Primitive (MutVar(MutVar))
import EVM.Solidity
import EVM.Types hiding (Word)
import EVM.ABI
--import Control.Lens (Indexed(Indexed))

-- | Some classic ValueTypes
newtype Address = Address Expression
newtype Uint = Uint Expression -- safe arithmetic
newtype Word = Word Expression -- word arithmetic
newtype BExp = BExp Expression

op' :: Instruction -> Expression
op' = ExprFunCall . BuiltIn

class EEq a where
  (.==) :: a -> a -> BExp

infix 4 .==

class OOrd a where
  (.<)  :: a -> a -> BExp
  (.<=) :: a -> a -> BExp
  (.>)  :: a -> a -> BExp
  (.>=) :: a -> a -> BExp

instance Num Word where
  (Word a) + (Word b) = Word (op' (ADD a b))
  (Word a) - (Word b) = Word (op' (SUB a b))
  (Word a) * (Word b) = Word (op' (MUL a b))
  negate n = 0 - n
  abs = error "todo"
  signum = error "todo"
  fromInteger n = Word (ExprLit (LitInteger n))

-- instance Integral Word where
--   (Word a) + (Word b) = Word (op' (ADD a b))
--   (Word a) - (Word b) = Word (op' (SUB a b))
--   (Word a) * (Word b) = Word (op' (MUL a b))
--   negate n = 0 - n
--   abs = error "todo"
--   signum = error "todo"
--   fromInteger n = Word (ExprLit (LitInteger n))

div :: Word -> Word -> Word
div (Word a) (Word b) = Word $ op' $ DIV a b

instance Coercible a Expression => EEq a where
  a .== b = BExp $ op' $ EQ (coerce a) (coerce b)


not :: BExp -> BExp
not (BExp b) = BExp (op' (ISZERO b))

and :: BExp -> BExp -> BExp
and (BExp a) (BExp b) = BExp (op' (AND a b))

or :: BExp -> BExp -> BExp
or (BExp a) (BExp b) = BExp (op' (OR a b))

data Expr a where
  UINT :: Word -> Expr Word
  BEXP :: BExp -> Expr BExp

instance OOrd Word where
  (Word a) .<  (Word b) = BExp (op' (LT a b))
  (Word a) .>  (Word b) = BExp (op' (GT a b))
  a .<= b = not (a .> b)
  a .>= b = not (a .< b)

instance Fractional Word where
  (Word a) / (Word b) = Word (op' (DIV a b))
  fromRational _ = error "hmm"
instance Show Word where
  show (Word x) = show x

instance Show BExp where
  show (BExp x) = show x

class Stmt a where
  sdesugar :: a -> Statement
  ssugar   :: Statement -> a

instance Stmt Word where
  sdesugar (Word e) = StmtExpr e
  ssugar = error "gmmm"

(.:=) :: Identifier -> Expression -> Assignment
a .:= b = Assignment (NEmpty (a :| [])) b


class Internal a where
  internal :: String -> a -> FunctionDefinition

-- | deriving unnamed pure functions
instance (Coercible a Expression) => Internal a where
  internal name a = FunctionDefinition (Id name) Nothing
    (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [])))) (Block [StmtAssign ((Id "x") .:= (coerce a))])

instance {-# OVERLAPPING  #-} (Coercible (a -> b) (Expression -> Expression)) => Internal (a -> b) where
  internal name f = FunctionDefinition (Id name) (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
    (Just (TypedIdentifierList (NEmpty (((Id "y"), Nothing) :| [])))) (Block [StmtAssign ((Id "y") .:= (coerce f) (ExprIdent (Id "x")))])

instance {-# OVERLAPPING  #-} (Coercible (a -> b -> c) (Expression -> Expression -> Expression)) => Internal (a -> b -> c) where
  internal name f = FunctionDefinition (Id name) (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [(Id "y", Nothing)]))))
    (Just (TypedIdentifierList (NEmpty (((Id "z"), Nothing) :| [])))) (Block [StmtAssign ((Id "z") .:= (coerce f) (ExprIdent (Id "x")) (ExprIdent (Id "y")))])

instance {-# OVERLAPPING  #-} (Coercible (a -> b -> c -> d) (Expression -> Expression -> Expression -> Expression)) => Internal (a -> b -> c -> d) where
  internal name f = FunctionDefinition (Id name) (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [(Id "y", Nothing), (Id "z", Nothing)]))))
    (Just (TypedIdentifierList (NEmpty (((Id "w"), Nothing) :| [])))) (Block [StmtAssign ((Id "w") .:= (coerce f) (ExprIdent (Id "x")) (ExprIdent (Id "y")) (ExprIdent (Id "z")))])

-- | More generally, we can make effectful functions:
data MStatement a =
    MStmtBlock (MBlock a)
  | MStmtFuncDef FunctionDefinition
  | MStmtVarDecl VariableDeclaration
  | MStmtAssign Assignment
  | MStmtIf If
  | MStmtExpr a
  | MStmtSwitch Switch
  | MStmtFor ForLoop
  | MStmtBrCont BreakContinue
  | MStmtLeave Leave

data MBlock a = MBlock [MStatement a]

class BlockMonad m b where
  toBlock :: m b -> Block

-- this is pretty cool, one could also experiment with scoping though:

class (Monad m) => MFun m where
  declare :: Proxy m -> FunctionDefinition
  invoke :: m a -> FunctionCall
  
-- built in function:
pureIf :: FunctionDefinition
pureIf = FunctionDefinition (Id "pureIf")
    (Just (TypedIdentifierList (NEmpty (((Id "condition"), Nothing) :| [(Id "yes", Nothing), (Id "no", Nothing)]))))
    (Just (TypedIdentifierList (NEmpty (((Id "outcome"), Nothing) :| []))))
    (Block [yulIf (BExp . ExprIdent $ Id "condition")
             (Block
             [StmtAssign ((Id "outcome") .:= (ExprIdent $ Id "yes"))]),
           yulIf (not . BExp . ExprIdent $ Id "condition")
            (Block
             [StmtAssign ((Id "outcome") .:= (ExprIdent $ Id "no"))])])

-- -- | deriving unnamed pure functions
-- instance (Coercible a Expression) => NamedFun a where
--   name s a = FunctionDefinition s Nothing
--     (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [])))) (Block [StmtAssign ((Id "x") .:= (coerce a))])
--   call s = coerce (ExprFunCall (UserDefined s []))

-- instance {-# OVERLAPPING  #-} (Coercible (a -> b) (Expression -> Expression)) => NamedFun (a -> b) where
--   name s f = FunctionDefinition s (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
--     (Just (TypedIdentifierList (NEmpty (((Id "y"), Nothing) :| [])))) (Block [StmtAssign ((Id "y") .:= (coerce f) (ExprIdent (Id "x")))])
--   call s = \a -> coerce (ExprFunCall (UserDefined s [coerce a]))

-- instance {-# OVERLAPPING  #-} (Coercible (a -> b -> c) (Expression -> Expression -> Expression)) => NamedFun (a -> b -> c) where
--   name s f = FunctionDefinition s (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [(Id "y", Nothing)]))))
--     (Just (TypedIdentifierList (NEmpty (((Id "z"), Nothing) :| [])))) (Block [StmtAssign ((Id "z") .:= (coerce f) (ExprIdent (Id "x")) (ExprIdent (Id "y")))])
--   call s = \a b -> coerce (ExprFunCall (UserDefined s [coerce a, coerce b]))

-- class (Blck a) => InScope (tag :: k) a where
--   declare :: Proxy tag -> Statement


-- class Declared (tag :: k) a where
--   name :: Proxy tag -> a -> FunctionDefinition

-- class (Declared tag a) => (Callable tag a) where
--   call :: Proxy tag -> a

-- | TODO: `scoped` class which defines when things are in scope?
--class (Scoped

-- purely syntactic if
yulIf :: BExp -> Block -> Statement
yulIf b x = StmtIf (If (coerce b) x)

class Iffy a where
  if' :: BExp -> a -> a -> a

instance (Coercible a Expression) => Iffy a where
  if' c yes no = coerce ExprFunCall (UserDefined (Id "pureIf") [coerce c, coerce yes, coerce no])
    
one :: Word
one = 10000000000

double :: Word -> Word
double a = 2 * a

doubleplusone :: Word -> Word
doubleplusone x = (double x) + 1

-- | handling requires:
emptyRevert :: Expression
emptyRevert = op' $ REVERT (ExprLit (LitInteger 0)) (ExprLit (LitInteger 0))

newtype Requires a = Requires {runRequire :: Writer [Statement] a }
  deriving (Functor)

instance Applicative Requires where
  pure a = Requires $ pure a
  (Requires f) <*> (Requires v) = Requires (f <*> v)

instance Monad Requires where
  return = pure
  (Requires f) >>= v = Requires $ f >>= runRequire . v

require :: BExp -> Requires ()
require b = Requires $ tell [StmtIf $ If (coerce $ not b) $ Block [StmtExpr emptyRevert]]

instance {-# OVERLAPPING #-} Coercible a Expression => Internal (Requires a) where
  internal name m = let (a, stmts) = runWriter $ runRequire m
            in FunctionDefinition (Id name) Nothing
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
               (Block (stmts <> [StmtAssign ((Id "x") .:= (coerce a))]))

instance {-# OVERLAPPING #-} Coercible (a -> b) (Expression -> Expression) => Internal (a -> Requires b) where
  internal name m = let (a, stmts) = runWriter $ runRequire (m (coerce $ ExprIdent $ Id "x"))
            in FunctionDefinition (Id name)
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
               (Just (TypedIdentifierList (NEmpty (((Id "y"), Nothing) :| []))))
                 (Block (stmts <> [StmtAssign ((Id "y") .:= (coerce a))]))

instance {-# OVERLAPPING #-} Coercible (a -> b -> c) (Expression -> Expression -> Expression) => Internal (a -> b -> Requires c) where
  internal name m = let (a, stmts) = runWriter $ runRequire (m (coerce $ ExprIdent $ Id "x") (coerce $ ExprIdent $ Id "y"))
            in FunctionDefinition (Id name)
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [((Id "y"), Nothing)]))))
               (Just (TypedIdentifierList (NEmpty (((Id "z"), Nothing) :| []))))
                 (Block (stmts <> [StmtAssign ((Id "z") .:= (coerce a))]))

instance {-# OVERLAPPING #-} Coercible (a -> b -> c -> d) (Expression -> Expression -> Expression -> Expression) => Internal (a -> b -> c -> Requires d) where
  internal name m = let (a, stmts) = runWriter $ runRequire (m (coerce $ ExprIdent $ Id "x") (coerce $ ExprIdent $ Id "y") (coerce $ ExprIdent $ Id "z"))
            in FunctionDefinition (Id name)
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [((Id "y"), Nothing), ((Id "z"), Nothing)]))))
               (Just (TypedIdentifierList (NEmpty (((Id "w"), Nothing) :| []))))
                 (Block (stmts <> [StmtAssign ((Id "w") .:= (coerce a))]))

safeAdd :: Word -> Word -> Requires Word
safeAdd a b = do
  require (a .<= (a + b))
  return $ a + b

safeMul :: Word -> Word -> Requires Word
safeMul a b = do
  require ((b .== 0) `or` ((a * b `div` b) .== a))
  return $ a * b

safeSub :: Word -> Word -> Requires Word
safeSub a b = do
  require (b .<= a)
  return $ b - a

add :: Uint -> Uint -> Uint
add (Uint x) (Uint y) =
  Uint $
    ExprFunCall $ UserDefined (Id "safeAdd") [x, y]

mul :: Uint -> Uint -> Uint
mul (Uint x) (Uint y) =
  Uint $
    ExprFunCall $ UserDefined (Id "safeMul") [x, y]

sub :: Uint -> Uint -> Uint
sub (Uint x) (Uint y) =
  Uint $
    ExprFunCall $ UserDefined (Id "safeSub") [x, y]

instance Num Uint where
  (+) = add
  (*) = mul
  (-) = sub
  negate n = 0 - n
  abs = error "todo"
  signum = error "todo"
  fromInteger n = Uint (ExprLit (LitInteger n))

assert :: BExp -> Requires ()
assert cond = Requires $ tell [StmtIf $ If (coerce (not cond)) $ Block [StmtExpr $ op' INVALID]]

distributivity :: Uint -> Uint -> Uint -> Requires ()
distributivity x y z = assert $ x * (y + z) .== x * y + x * z

class External a where
  external :: String -> a -> FunctionDefinition

cdload :: Integer -> Expression
cdload n = op' $ CALLDATALOAD $ ExprLit $ LitInteger n

yulReturn :: Coercible a Expression => a -> [Statement]
yulReturn e = (StmtExpr . op') <$>
  [MSTORE noll (coerce e),
   RETURN noll (coerce (32 :: Word))
  ]

instance {-# OVERLAPPING #-} Coercible a Expression => External (Requires ()) where
  external name m = let (_, stmts) = runWriter $ runRequire m
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block stmts)

instance {-# OVERLAPPING #-} Coercible a Expression => External (Requires a) where
  external name m = let (a, stmts) = runWriter $ runRequire m
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block (stmts <> yulReturn a))

instance {-# OVERLAPPING #-} Coercible a Expression => External (a -> Requires ()) where
  external name m = let (_, stmts) = runWriter $ runRequire (m (coerce $ cdload 4))
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block stmts)

instance {-# OVERLAPPING #-} Coercible (a, b) (Expression, Expression) => External (a -> Requires b) where
  external name m = let (a, stmts) = runWriter $ runRequire (m (coerce $ cdload 4))
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block $ stmts <> yulReturn a)

instance {-# OVERLAPPING #-} Coercible (a, b) (Expression, Expression) => External (a -> b -> Requires ()) where
  external name m = let (_, stmts) = runWriter $ runRequire (m (coerce $ cdload 4) (coerce $ cdload 36))
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block stmts)

instance {-# OVERLAPPING #-} Coercible (a, b, c) (Expression, Expression, Expression) => External (a -> b -> Requires c) where
  external name m = let (a, stmts) = runWriter $ runRequire (m (coerce $ cdload 4) (coerce $ cdload 36))
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block $ stmts <> yulReturn a)

instance {-# OVERLAPPING #-} Coercible (a, b, c) (Expression, Expression, Expression) => External (a -> b -> c -> Requires ()) where
  external name m = let (_, stmts) = runWriter $ runRequire (m (coerce $ cdload 4) (coerce $ cdload 36) (coerce $ cdload 68))
                    in FunctionDefinition (Id name) Nothing Nothing
                       (Block stmts)


data Exported = forall a . External a => Export a

noll :: Expression
noll = (ExprLit (LitInteger 0))

builtins :: [FunctionDefinition]
builtins =
  [ internal "safeAdd" safeAdd
  , internal "safeMul" safeMul
  ]

-- | Standard contract structure like:
-- object "Initcode" {
--   code {
--     datacopy(0, dataoffset("Runtime"), datasize("Runtime"))
--     return(0, datasize("Runtime"))
--   }
-- object "Runtime" {
--   code {
--   ...
--   }
contract :: [(String, Exported)] -> Object
contract methods =
  let size' = op' $ DATASIZE (StringLiteral $ Id "Runtime")
      offset' = op' $ DATAOFFSET (StringLiteral $ Id "Runtime")
      
  in Object (StringLiteral $ Id "Initcode")
    (Code
      (Block
        [ StmtExpr $ op' $ DATACOPY noll offset' size',
          StmtExpr $ op' $ RETURN noll size'
        ]
      )
    )
     [Left $
        Object
         (StringLiteral $ Id "Runtime")
         (Code
           (Block $
             (dispatch <$> (fst <$> methods))
             <> [StmtExpr emptyRevert]
             <> fmap (\(name, Export a) -> StmtFuncDef $ external (namepart name) a) methods
             <> (StmtFuncDef <$> builtins)
           )
         )
       []
     ]

namepart :: String -> String
namepart s = case elemIndex '(' s of
  Nothing -> s
  Just i -> take i s

dispatch :: String -> Statement
dispatch name = yulIf
  (Uint (op' $ SHR (coerce (224 :: Uint)) (cdload 0)) .==
   fromIntegral (word (BS.take 4 (selector $ pack name))))
  (Block [StmtExpr $ ExprFunCall (UserDefined (Id $ namepart name) [])])
  

compile :: Object -> IO (Map Text SolcContract)
compile o = do
  Just (contracts, _, _) <- readJSON <$> solc Yul (pack $ show o) 
  return $! contracts
  

-- | THIS PART SHOULD LIVE IN SOLIDITY.HS IN HEVM
solc :: Language -> Text -> IO Text
solc lang src =
  withSystemTempFile "hevm.sol" $ \path handle -> do
    hClose handle
    writeFile path (stdjson lang src)
    Text.pack <$> readProcess
      "solc"
      ["--standard-json", path]
      ""

data Language = Solidity | Yul
  deriving (Show)
-- more options later perhaps

data StandardJSON = StandardJSON Language Text

instance ToJSON StandardJSON where
  toJSON (StandardJSON lang src) =
    object [ pack "language" .= show lang
           , pack "sources" .= object [pack "hevm.sol" .=
                                   object [pack "content" .= src]]
           , pack "settings" .=
             object [ pack "outputSelection" .=
                    object [pack "*" .= 
                      object [ pack "*" .= (toJSON
                              ["metadata" :: String,
                               "evm.bytecode",
                               "evm.deployedBytecode",
                               "abi",
                               "storageLayout",
                               "evm.bytecode.sourceMap",
                               "evm.bytecode.linkReferences",
                               "evm.bytecode.generatedSources",
                               "evm.deployedBytecode.sourceMap",
                               "evm.deployedBytecode.linkReferences",
                               "evm.deployedBytecode.generatedSources"
                              ]),
                              pack "" .= (toJSON ["ast" :: String])
                             ]
                            ]
                    ]
           ]
                               
stdjson :: Language -> Text -> String
stdjson lang src = Text.unpack $ decodeUtf8 $ toStrict $ encode $ StandardJSON lang src
--- END SOLIDITY.HS SNIPPED


-- | We follow the memory conventions of Solidity:
-- Solidity reserves four 32-byte slots, with specific byte ranges (inclusive of endpoints) being used as follows:
--     0x00 - 0x3f (64 bytes): scratch space for hashing methods
--     0x40 - 0x5f (32 bytes): currently allocated memory size (aka. free memory pointer)
--     0x60 - 0x7f (32 bytes): zero slot
-- This means that we can access storage without worrying about memory
-- (at least for `value types`)

-- ^ We can use storage in the Requires monad:
-- instance MonadState (Map Uint Uint) Requires where
--   put (Uint a) = Requires $ tell [StmtExpr $ op' $ SSTORE (ExprLit (LitInteger 0)) a]
--   get = pure $ Uint $ op' $ SLOAD $ ExprLit (LitInteger 0)
-- class (Coercible b Expression) => HasLocation b where
--   getLoc :: b -> StorageItem

newtype Storage a b = Storage {runStorage :: Requires b}
  deriving (Functor, Applicative, Monad) via Requires

put :: (Coercible b Expression, Coercible a Expression) => b -> a -> Storage b ()
put loc a = Storage $ Requires $ tell [StmtExpr $ op' $ SSTORE (coerce loc) (coerce a)]

get :: (Coercible b Expression) => b -> Storage b b
get a = Storage $ Requires $ do tell [StmtAssign $ (Id "g") .:= (op' $ SLOAD (coerce a))]
                                return $ coerce $ ExprIdent (Id "g") -- TODO: de bruijn

data Mapping x y = Mapping (Map x y)

increment :: Uint -> Storage Uint Uint
increment y = do
  x <- get y
--  Storage $ require (x .< (y - 1))
  put y (x + 1)
  return y

-- transfer :: Uint -> Storage Uint BExp
-- transfer amount = 

instance {-# OVERLAPPING #-} (Coercible a Expression, Coercible b Expression) => Internal (Storage a b) where
  internal name (Storage a) = internal name a

instance {-# OVERLAPPING #-} (Coercible a Expression, Coercible v1 Expression, Coercible b Expression) => Internal (v1 -> Storage a b) where
  internal name m = let (a, stmts) = runWriter $ runRequire $ runStorage $ (m (coerce $ ExprIdent $ Id "x"))
            in FunctionDefinition (Id name)
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
               (Just (TypedIdentifierList (NEmpty (((Id "y"), Nothing) :| []))))
                 (Block (stmts <> [StmtAssign ((Id "y") .:= (coerce a))]))

-- instance {-# OVERLAPPING #-} (Coercible a Expression, Coercible b Expression) => UnnamedFun (Storage a b) where
--   mkFun (Storage a) = mkFun a

-- instance (Expr b) => Fun (Expression -> b) where
--   mkFun f = FunctionDefinition "unary" Nothing
--     (Just (TypedIdentifierList (NEmpty (("x", Nothing) :| [("y", Nothing)])))) (Block _)

-- class Fun a where
--   mkFunc :: Identifier -> [(Indentifier, Expression)] -> 
-- instance Stmt (Revert Uint) where
--   mkStmt (Revert (Right (Uint e))) = StmtExpr e
--   mkStmt (Revert (Left ())) = StmtExpr emptyRevert

-- newtype Bytes32 = Bytes32 Expression
--   deriving (Eq, Ord, Num)
-- newtype Uint8   = Uint8 Expression
--   deriving (Eq, Ord, Num)

-- newtype Bytes = Bytes ByteString
--   deriving (Eq, Ord)


-- -- | We can express the execution environment of a contract
-- -- as a stack of monad transformers. Read from right to left:

-- -- ^ Except String -- We can revert with an error message at any time
-- -- ^ StateT a      -- The State a can be modified
-- -- ^ ReaderT Env   -- We have read access to the call and block environment
-- -- TODO: how to model external function calls to known / unknown calls? (mutvars?)
-- type Exe a b = ReaderT Env ((StateT a) (Except String)) b

-- data Msg = Msg {
--   _sender   :: Address,
--   _value    :: Uint,
--   _calldata :: Bytes
--   }


-- data Tx = Tx {
--   origin :: Address
-- }

-- data Block = Block {
--   hash :: Bytes32
-- }

-- data Env = Env {
--   _msg :: Msg,
--   _this :: Address,
--   _txorigin :: Tx,
--   _chainid :: Uint, -- does it live in block? idk.
--   _block :: Block
--   }

-- makeLenses ''Env
-- makeLenses ''Msg
-- makeLenses ''Tx

-- --helpful aliases:
-- -- | if {condition} revert(msg)
-- require :: (MonadError String m) => Bool -> String -> m ()
-- require condition errmsg = if condition then pure () else throwError errmsg

-- -- redefine `at` to treat missing values as 0s.
-- at :: (At m, Num (IxValue m), Eq (IxValue m), Functor f) => Index m -> (IxValue m -> f (IxValue m)) -> m -> f m
-- at x = Control.Lens.at x . non 0

-- -- | some blockchain and abi primitive operations
-- class ByteRep b where
--   toBytes :: b -> Bytes

-- instance ByteRep String where
--   toBytes = error ""

-- instance ByteRep Bytes where
--   toBytes = id

-- keccak256 :: (ByteRep b) => b -> Bytes32
-- keccak256 _ = error "todo"

-- ecrecover :: Bytes32 -> Uint8 -> Bytes32 -> Bytes32 -> Address
-- ecrecover hashmsg v r s = error "todo"

-- class Abi b where
--   abiencode :: b -> Bytes

-- instance Abi Bytes32 where
--   abiencode = error ""

-- instance Abi Address where
--   abiencode = error ""

-- instance Abi Uint where
--   abiencode = error ""

-- instance Abi Bytes where
--   abiencode = error ""

-- instance Abi String where
--   abiencode = error ""

-- instance Abi Bool where
--   abiencode = error ""

-- -- if one wants to be fancy, this can be done via generics instead of this boilerplate
-- instance (Abi a, Abi b) => Abi (a,b) where
--   abiencode = error ""

-- instance (Abi a, Abi b, Abi c) => Abi (a,b,c) where
--   abiencode = error ""

-- instance (Abi a, Abi b, Abi c, Abi d) => Abi (a,b,c,d) where
--   abiencode = error ""

-- instance (Abi a, Abi b, Abi c, Abi d, Abi e) => Abi (a,b,c,d,e) where
--   abiencode = error ""

-- instance (Abi a, Abi b, Abi c, Abi d, Abi e, Abi f) => Abi (a,b,c,d,e,f) where
--   abiencode = error ""

-- instance Num Bool where
--   fromInteger n = n /= 0
