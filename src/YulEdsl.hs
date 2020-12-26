{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
--{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
--{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

import Prelude hiding (and, not, or, EQ, LT, GT) --, (>>), (>>=), return)

import Data.List.NonEmpty hiding (head)
import Yul
import Data.Coerce (coerce)
import GHC.Base (Coercible)
import Data.Data (Proxy(..))
import Control.Monad.Trans.Writer

-- | Some classic ValueTypes
newtype Address = Address Expression
newtype Uint = Uint Expression
newtype BExp = BExp Expression

op' :: Instruction -> Expression
op' = ExprFunCall . BuiltIn

class EEq a where
  (.==) :: a -> a -> BExp

class OOrd a where
  (.<)  :: a -> a -> BExp
  (.<=) :: a -> a -> BExp
  (.>)  :: a -> a -> BExp
  (.>=) :: a -> a -> BExp

instance Num Uint where
  (Uint a) + (Uint b) = Uint (op' (ADD a b))
  (Uint a) - (Uint b) = Uint (op' (SUB a b))
  (Uint a) * (Uint b) = Uint (op' (MUL a b))
  negate n = 0 - n
  abs = error "todo"
  signum = error "todo"
  fromInteger n = Uint (ExprLit (LitInteger n))

instance EEq Uint where
  (Uint a) .== (Uint b) = BExp (op' (EQ a b))

not :: BExp -> BExp
not (BExp b) = BExp (op' (ISZERO b))

and :: BExp -> BExp -> BExp
and (BExp a) (BExp b) = BExp (op' (AND a b))

or :: BExp -> BExp -> BExp
or (BExp a) (BExp b) = BExp (op' (OR a b))

data Expr a where
  UINT :: Uint -> Expr Uint
  BEXP :: BExp -> Expr BExp

-- instance Functor Expr where
--   fmap f (UINT a) = (f a)

instance OOrd Uint where
  (Uint a) .<  (Uint b) = BExp (op' (LT a b))
  (Uint a) .>  (Uint b) = BExp (op' (GT a b))
  a .<= b = not (a .> b)
  a .>= b = not (a .< b)

instance Fractional Uint where
  (Uint a) / (Uint b) = Uint (op' (DIV a b))
  fromRational _ = error "hmm"
instance Show Uint where
  show (Uint x) = show x

instance Show BExp where
  show (BExp x) = show x

class Stmt a where
  sdesugar :: a -> Statement
  ssugar   :: Statement -> a

instance Stmt Uint where
  sdesugar (Uint e) = StmtExpr e
  ssugar = error "gmmm"

(.:=) :: Identifier -> Expression -> Assignment
a .:= b = Assignment (NEmpty (a :| [])) b


class UnnamedFun a where
  mkFun :: a -> FunctionDefinition

-- | deriving unnamed pure functions
instance (Coercible a Expression) => UnnamedFun a where
  mkFun a = FunctionDefinition (Id "f") Nothing
    (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [])))) (Block [StmtAssign ((Id "x") .:= (coerce a))])

instance {-# OVERLAPPING  #-} (Coercible (a -> b) (Expression -> Expression)) => UnnamedFun (a -> b) where
  mkFun f = FunctionDefinition (Id "unary") (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
    (Just (TypedIdentifierList (NEmpty (((Id "y"), Nothing) :| [])))) (Block [StmtAssign ((Id "y") .:= (coerce f) (ExprIdent (Id "x")))])

instance {-# OVERLAPPING  #-} (Coercible (a -> b -> c) (Expression -> Expression -> Expression)) => UnnamedFun (a -> b -> c) where
  mkFun f = FunctionDefinition (Id "binary") (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [(Id "y", Nothing)]))))
    (Just (TypedIdentifierList (NEmpty (((Id "z"), Nothing) :| [])))) (Block [StmtAssign ((Id "z") .:= (coerce f) (ExprIdent (Id "x")) (ExprIdent (Id "y")))])

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
    
one :: Uint
one = 10000000000

double :: Uint -> Uint
double a = 2 * a

doubleplusone :: Uint -> Uint
doubleplusone x = (double x) + 1

-- | handling requires:
emptyRevert :: Expression
emptyRevert = op' $ REVERT (ExprLit (LitInteger 0)) (ExprLit (LitInteger 0))

type Requires a = Writer [Statement] a


require :: BExp -> Requires ()
require (BExp b) = writer ((), [StmtIf (If b (Block [StmtExpr emptyRevert]))])


instance {-# OVERLAPPING #-} Coercible a Expression => UnnamedFun (Requires a) where
  mkFun m = let (a, stmts) = runWriter m
            in FunctionDefinition (Id "nullaryM") Nothing
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
               (Block (stmts <> [StmtAssign ((Id "x") .:= (coerce a))]))

instance {-# OVERLAPPING #-} Coercible (a -> b) (Expression -> Expression) => UnnamedFun (a -> Requires b) where
  mkFun m = let (a, stmts) = runWriter (m (coerce $ ExprIdent $ Id "x"))
            in FunctionDefinition (Id "unaryM")
               (Just (TypedIdentifierList (NEmpty (((Id "y"), Nothing) :| []))))
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| []))))
                 (Block (stmts <> [StmtAssign ((Id "x") .:= (coerce a))]))

instance {-# OVERLAPPING #-} Coercible (a -> b -> c) (Expression -> Expression -> Expression) => UnnamedFun (a -> b -> Requires c) where
  mkFun m = let (a, stmts) = runWriter (m (coerce $ ExprIdent $ Id "x") (coerce $ ExprIdent $ Id "y"))
            in FunctionDefinition (Id "binaryM")
               (Just (TypedIdentifierList (NEmpty (((Id "x"), Nothing) :| [((Id "y"), Nothing)]))))
               (Just (TypedIdentifierList (NEmpty (((Id "z"), Nothing) :| []))))
                 (Block (stmts <> [StmtAssign ((Id "z") .:= (coerce a))]))

safeAdd :: Uint -> Uint -> Requires Uint
safeAdd a b = do
  require (a .<= (a * b))
  return $ a + b


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
