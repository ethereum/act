module Splitter where
  
import AbsAct
import EVM.Keccak (abiKeccak)

type StorageLayout = [TDecl]

data Obligation = Obligation
  { _name      :: Ident,
    _contract  :: Ident,
    _StatusCode :: String,
    _return     :: Exp,
    _env        :: [(String, Ident)],
    _calldata  :: BYExp,
    _variables :: [(Ident, Type)],
    _preStore  :: [(Entry, Exp)],
    _postStore :: [(Entry, Exp)],
    _preCondition :: [BExp],
    _postCondition :: [BExp]
  }


split :: Behaviour -> StorageLayout -> [Obligation]
split (Transition name contract methodName args [] post) storageVars =
  case post of
    ReturnH returnExp -> [Obligation
      {_name     = name,
       _contract = contract,
       _StatusCode = "EVMC_SUCCESS",
       _return     = returnExp,
       _env        = defaultEnv,
       _calldata   = symbolicSig methodName args,
       _variables  = [], --hmmm
       _preStore   = [], --TODO
       _postStore  = [], --TODO (should be same as prestore)
       _preCondition  = [],
       _postCondition = []
      }]
    Storage _ -> _
    _ -> _
split _ _ = error "The impossible has occurred"

--TODO: proper de Bruijn
defaultEnv :: [(String, Ident)]
defaultEnv = [("CALLER", Ident "CALLER_VAR")]

--passCase :: Ident -> Ident -> Ident -> [TDecl] -> Return

symbolicSig :: Ident -> [Decl] -> BYExp
symbolicSig _ _ = _

abiEncode :: [Type] -> [Exp] -> BYExp
abiEncode (t:tys) (e:exps) = _
abiEncode [] [] = BYLit ""

toTDecl :: Decl -> TDecl
toTDecl (Dec ty var) = TDec var ty

