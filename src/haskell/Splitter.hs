{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DeriveAnyClass #-}

import Data.Aeson
import Data.Aeson.Types
import GHC.Generics
import System.Environment ( getArgs )
import System.Exit ( exitFailure )

import AbsAct

instance Generic Ident
instance ToJSON Ident

type StorageLayout = [TDecl]

data Obligation = Obligation
  { _name      :: Ident,
    _contract  :: Ident,
    _StatusCode :: String
--    _return     :: Exp,
--    _env        :: [(String, Ident)],
--    _calldata  :: BYExp,
--    _variables :: [(Ident, Type)],
--    _preStore  :: [(Entry, Exp)],
--    _postStore :: [(Entry, Exp)],
--    _preCondition :: [BExp],
--    _postCondition :: [BExp]
  } deriving (Show, Generic, ToJSON)

split :: Behaviour -> StorageLayout -> [Obligation]
split (Transition name contract methodName args [] claim) storageVars =
  case claim of
    Direct post -> [Obligation
      {_name     = name,
       _contract = contract,
       _StatusCode = "EVMC_SUCCESS"
--       _return     = returnExp,
--       _env        = defaultEnv,
--       _calldata   = methodName args,
       -- _variables  = [], --hmmm
       -- _preStore   = [],
       -- _postStore  = [],
       -- _preCondition  = [],
       -- _postCondition = []
      }]
    Storage _ -> _
    _ -> _
split _ _ = error "The impossible has occurred"


usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (files)         Split files."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    _ -> _
    

defaultEnv :: [(String, Ident)]
defaultEnv = [("CALLER", Ident "CALLER_VAR")]

toTDecl :: Decl -> TDecl
toTDecl (Dec ty var) = TDec var ty

