{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RebindableSyntax #-}
module YulEdsl where

import Prelude hiding (EQ, LT, GT, (>>), (>>=), return)

import Control.Monad.Trans.Reader
import Control.Lens hiding (at)
-- import Control.Monad.State
-- import Control.Monad.Reader
-- import Control.Monad.Except
--import qualified Control.Lens
import Data.ByteString
import Yul

-- | Some classic ValueTypes
newtype Address = Address Expression
--  deriving (Eq, Ord, Num)

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

instance OOrd Uint where
  (Uint a) .<  (Uint b) = BExp (op' (LT a b))
  (Uint a) .<= (Uint b) = BExp (op' (ISZERO $ op' (GT a b)))
  (Uint a) .>  (Uint b) = BExp (op' (GT a b))
  (Uint a) .>= (Uint b) = BExp (op' (ISZERO $ op' (LT a b)))

instance Fractional Uint where
  (Uint a) / (Uint b) = Uint (op' (DIV a b))
  fromRational _ = error "hmm"

instance Show Uint where
  show (Uint e) = show e

instance Show BExp where
  show (BExp e) = show e

data Require a = Req BExp | Simply a

require :: BExp -> Requiring a
require a = Requiring [Req a]

class Stmt a where
  mkStmt :: a -> Statement

instance Stmt Uint where
  mkStmt (Uint a) = StmtExpr a

instance Stmt a => Stmt (Require a) where
  mkStmt (Req (BExp b)) = StmtIf (If b (Block [StmtExpr emptyRevert]))
  mkStmt (Simply a) = mkStmt a

newtype Requiring a = Requiring [Require a]

class Blck a where
  mkBlck :: a -> Block

instance Stmt a => Blck (Requiring a) where
  mkBlck (Requiring a) = Block (fmap mkStmt a)

(>>) :: Requiring a -> Requiring a -> Requiring a
(Requiring a) >> (Requiring b) = Requiring (a ++ b)

return :: a -> Requiring a
return a = Requiring [Simply a]

safeAdd :: Uint -> Uint -> Requiring Uint
safeAdd a b = do
  require (a .<= (a + b))
  return (a + b)

emptyRevert :: Expression
emptyRevert = op' $ REVERT (ExprLit (LitInteger 0)) (ExprLit (LitInteger 0)) 

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
