module Dai where

import qualified Capability.State as Cap
import qualified Capability.Reader as Cap
import Control.Monad.Trans.Reader
import Control.Lens hiding (at)
import qualified Control.Lens
import Data.Map
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import EVM.Types
import Data.ByteString (ByteString)

-- | As an experiment, let's model the Dai contract.
-- It is a state machine over the following state:

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

newtype Dai a = Dai { runDai :: Exe DaiState a }
  deriving (Functor,
            Applicative,
            Monad,
            MonadState DaiState,
            MonadError String,
            MonadReader Env)

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
