{-# LANGUAGE ScopedTypeVariables #-}
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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MagicHash #-}

module Dai where
import qualified Capability.State as Cap
import qualified Capability.Reader as Cap
import Control.Monad.Trans.Reader
import Control.Lens hiding (at)
import qualified Control.Lens
import Data.Map
import Control.Monad.State
--import Data.Primitive.MutVar
import Control.Monad.Reader
import Control.Monad.Except
import GHC.Exts (Proxy#)
import EVM.Types
import Data.ByteString (ByteString)

newtype Address = Address Addr
  deriving (Eq, Ord, Num)
newtype Bytes = Bytes ByteString
  deriving (Eq, Ord)
newtype Uint    = Uint Word
  deriving (Eq, Ord, Num)
newtype Bytes32 = Bytes32 Word
  deriving (Eq, Ord, Num)
newtype Uint8   = Uint8 Word
  deriving (Eq, Ord, Num)


-- GENERAL SMART CONTRACT STUFF --
-- read from inside out;
-- Except String : any computation can revert at any point
-- StateT a      : the compuation is stateful a (the contract state)
-- ReaderT Env   : the compuation has access to environment information
-- TODO: how do export functions to be called?
-- TODO: how are these constructed?
type Contract (name :: k) (a :: *) (b :: *) = ReaderT Env ((StateT a) (Except String)) b

data Msg = Msg {
  _sender :: Address,
  _value  :: Uint
  }


data Tx = Tx {
  origin :: Address
}

data Block = Block {
  hash :: Bytes32
}

data Env = Env {
  _msg :: Msg,
  _this :: Address,
  _txorigin :: Tx,
  _chainid :: Uint, -- does it live in block? idk.
  _block :: Block
  }

--helpful aliases:
-- | revert if now present
require :: (MonadError String m) => Bool -> String -> m ()
require condition msg = if condition then pure () else throwError msg

-- redefine `at` to treat missing values as 0s.
at :: (At m, Num (IxValue m), Eq (IxValue m), Functor f) => Index m -> (IxValue m -> f (IxValue m)) -> m -> f m
at x = Control.Lens.at x . non 0

class ByteRep b where
  toBytes :: b -> Bytes

instance ByteRep String where
  toBytes = error ""

instance ByteRep Bytes where
  toBytes = id

keccak256 :: (ByteRep b) => b -> Bytes32
keccak256 _ = 0

ecrecover :: Bytes32 -> Uint8 -> Bytes32 -> Bytes32 -> Address
ecrecover msg v r s = error ""

class Abi b where
  abiencode :: b -> Bytes

instance Abi Bytes32 where
  abiencode = error ""

instance Abi Address where
  abiencode = error ""

instance Abi Uint where
  abiencode = error ""

instance Abi Bytes where
  abiencode = error ""

instance Abi String where
  abiencode = error ""

instance Abi Bool where
  abiencode = error ""

-- instance Abi Bytes where
--   abiencode = error ""

-- if one wants to be fancy, this can be done via generics instead of this boilerplate
instance (Abi a, Abi b) => Abi (a,b) where
  abiencode = error ""

instance (Abi a, Abi b, Abi c) => Abi (a,b,c) where
  abiencode = error ""

instance (Abi a, Abi b, Abi c, Abi d) => Abi (a,b,c,d) where
  abiencode = error ""

instance (Abi a, Abi b, Abi c, Abi d, Abi e) => Abi (a,b,c,d,e) where
  abiencode = error ""

instance (Abi a, Abi b, Abi c, Abi d, Abi e, Abi f) => Abi (a,b,c,d,e,f) where
  abiencode = error ""

instance Num Bool where
  fromInteger n = n /= 0

-- dai specific:  

data DaiState = DaiState
  { _wards :: Map Address Bool,
    _balances :: Map Address Uint,
    _allowances :: Map (Address, Address) Uint,
    _nonces    :: Map Address Uint,
    _totalSupply :: Uint,
    _name :: String,
    _symbol :: String,
    _version :: String,
    _decimals :: Uint8,
    _DOMAIN_SEPARATOR :: Bytes32
  }

makeLenses ''DaiState
makeLenses ''Env
makeLenses ''Msg

newtype Dai a = Dai { runDai :: Contract "Dai" DaiState a }
  deriving (Functor,
            Applicative,
            Monad,
            MonadState DaiState,
            MonadError String,
            MonadReader Env)

-- class (Cap.HasState name Address m) => HasReference name m where
--   ref :: (IsContract m) => m

class Export (contract :: k) (function :: k) arg state out where
  call :: forall b (m :: * -> *). (Cap.HasState contract state m) => Proxy# contract -> Proxy# function -> arg -> Contract contract state out

instance Cap.HasState "wards" (Map Address Bool) Dai where
  state_ _ s =
    let
      a old = fst $ s old
      toNew old = snd $ s old
    in do w <- use wards
          assign wards (toNew w)
          return (a w)

-- wards are factored out so that they can be reused in other contracts,
-- -- because they only refer to the `wards` part of state.
auth :: (MonadError String a, Cap.HasState "wards" (Map Address Bool) a, MonadReader Env a) => a ()
auth = do
  wardz <- Cap.get @"wards"
  caller <- view (msg.sender)
  require (wardz ^. at caller) ""

rely :: (MonadError String a, Cap.HasState "wards" (Map Address Bool) a, MonadReader Env a) => Address -> a ()
rely guy = do
  auth
  wardz <- Cap.get @"wards"
  Cap.put @"wards" (wardz & at guy .~ True)

deny :: (MonadError String a, Cap.HasState "wards" (Map Address Bool) a, MonadReader Env a) => Address -> a ()
deny guy = do
  auth
  wardz <- Cap.get @"wards"
  Cap.put @"wards" (wardz & at guy .~ False)

constructor :: Cap.HasReader "env" Env a => String -> String -> String -> Uint -> a DaiState
constructor symbol_ name_ version_ chainid_ = do
  env' <- Cap.ask @"env"
  return $ DaiState {
   _wards = singleton (env' ^. msg.sender) True,
   _balances = empty,
   _allowances = empty,
   _nonces = empty,
   _totalSupply = 0,
   _name = name_,
   _symbol = symbol_,
   _version = version_,
   _decimals = 18,
   _DOMAIN_SEPARATOR =
       keccak256(abiencode
                 ( keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                   keccak256("Dai Semi-Automated Permit Office"),
                   keccak256(toBytes(version_)),
                   chainid_,
                   env' ^. this
                 ))
   }

-- constants are very simple
permit_TYPEHASH :: Bytes32
permit_TYPEHASH = keccak256
  "Permit(address holder,address spender,uint256 nonce,uint256 deadline,bool allowed)"

-- getters -- (probably through some fancy macros at some point)
balanceOf :: Address -> Dai Uint
balanceOf holder = use (balances . at holder)

allowance :: Address -> Address -> Dai Uint
allowance owner spender = use (allowances . at (owner, spender))

nonceOf :: Address -> Dai Uint
nonceOf who = use (nonces . at who)

-- internal functions are denoted by `Contract` instead of `Dai`.
transfer' :: Address -> Address -> Uint -> Dai ()
transfer' src dst wad = do
  srcBal <- use (balances . at src)
  require (srcBal >= wad) "insufficient balance"
  balances . at src -= wad
  balances . at dst += wad

-- ERC20 functions.
transferFrom :: Address -> Address -> Uint -> Dai Bool
transferFrom src dst wad = do
  caller <- view (msg.sender)
  allowed <- use (allowances . at (caller, src))
  require (allowed >= wad) "insufficient balance"
  when (allowed < (-1)) $
    allowances . at (caller, src) -= wad
  transfer' src dst wad
  return True

transfer :: Address -> Uint -> Dai Bool
transfer dst wad = do
  caller <- view (msg.sender)
  transfer' caller dst wad
  return True

approve :: Address -> Uint -> Dai Bool
approve usr wad = do
  caller <- view (msg.sender)
  allowances . at (caller, usr) .= wad
  return True

mint :: Address -> Uint -> Dai ()
mint usr wad = do
  auth
  balances . at usr += wad

permit :: Address -> Address -> Uint -> Uint -> Bool -> Uint8 -> Bytes32 -> Bytes32 -> Dai ()
permit holder spender nonce deadline allowed v r s = do
  domain_sep <- use dOMAIN_SEPARATOR
  let digest = keccak256 (
        abiencode ("\x19\x01",
                   domain_sep,
                   keccak256 (abiencode
                               ( permit_TYPEHASH,
                                 holder,
                                 spender,
                                 nonce,
                                 deadline,
                                 allowed
                             )
                  )))
  require (holder == ecrecover digest v r s) "invalid permit"
  require (deadline == 0) "permit expired"
  nonce' <- use (nonces . at holder)
  require (nonce == nonce') "invalid nonce"
  allowances . at (holder, spender) .= if allowed then -1 else 0
  nonces . at holder += 1

uncurry4 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry4 f (a,b,c) = f a b c

instance Export "Dai" "transferFrom"(Address,Address,Uint) DaiState Bool where
  call _ _ = (HasRefrunDai . (uncurry4 transferFrom) -> 


-- | let's see how calling semantics work. consider another simple contract, in Solidity:

{-
contract Bank {
   address Dai public constant = Dai(0xacab);
   mapping(address=>uint) public deposited;
   function deposit(uint amount) public {
      deposited[msg.sender] += amount;
      transferFrom(msg.sender, address(this), amount);
   }
   function withdraw(uint amount) public {
      require(amount <= deposited[msg.sender])
      deposited[msg.sender] -= amount;
      transfer(msg.sender, amount);
   }
}
-}

data BankState = BankState {
  _dai :: ---
  _deposits :: Map Address Uint
  }

makeLenses ''BankState

newtype Bank a = Bank (Contract "Bank" BankState a)
  deriving (Functor,
            Applicative,
            Monad,
            MonadState BankState,
            MonadError String,
            MonadReader Env
            )

deposit :: Uint -> Bank ()
deposit amount = do
  caller <- view (msg.sender)
  us <- view this
  deposits . at caller += amount
  _ <- call @"Dai" @"transferFrom"
  return ()

withdraw :: Uint -> Bank ()
withdraw amount = do
  caller <- view (msg.sender)
  available <- use (deposits . at caller)
  require (amount <= available) ""
  us <- view this
  deposits . at caller -= amount
  modifying dai (transfer caller amount)


class (MonadReader Env m, MonadState a m, MonadError String m, Abi cArg) => IsContract m name a b cArg where
  address :: Address
  new :: Env -> cArg -> a
  


