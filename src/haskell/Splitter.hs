{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
import Data.Aeson
import Data.Aeson.Types
import GHC.Generics
import System.Environment ( getArgs )
import System.Exit ( exitFailure )
import Data.Text          (Text, pack, unpack)
import qualified Data.ByteString.Lazy.Char8 as B

import AbsAct
import LexAct
import ParAct
import ErrM

type StorageLayout = [TDecl]

data Obligation = Obligation
  { _name      :: String,
    _contract  :: String,
    _StatusCode :: String,
    _methodName :: String,
    _inputArgs  :: [(String, String)]
--    _return     :: Exp
--    _env        :: [(String, Ident)],
-- --    _variables :: [(Ident, Type)],
--     _preStore  :: [(Entry, Exp)],
--     _postStore :: [(Entry, Exp)],
--     _preCondition :: [BExp],
--     _postCondition :: [BExp]
  } deriving (Show)

instance ToJSON Obligation where
  toJSON (Obligation { .. }) =
    object [ "name" .= _name
           , "contract"  .= _contract
           , "statusCode"  .= _StatusCode
           , "methodName"  .= _methodName
           , "inputArgs"   .= array _inputArgs
--           , "return"  .= show _return
           -- , "calldata"  .= show _calldata
           -- , "preStore"  .= show _preStore
           -- , "postStore"  .= show _postStore
           -- , "preCondition"  .= show _preCondition
           -- , "postCondition"  .= show _postCondition
           ]


split :: Behaviour -> [Obligation]
split (Transition (Ident name) (Ident contract) (Ident methodName) args [] claim) =
  case claim of
    Direct post -> [Obligation
      {_name     = name,
       _contract = contract,
       _StatusCode = "EVMC_SUCCESS",
       _methodName = methodName,
       _inputArgs = fmap (\(Dec ty (Ident id)) -> (show ty, show id)) args
--       _return     = ""
--       _return     = returnExp,
--       _env        = defaultEnv,
--       _calldata   = methodName args,
       -- _variables  = [], --hmmm
       -- _preStore   = [],
       -- _postStore  = [],
       -- _preCondition  = [],
       -- _postCondition = []
      }]
    CaseSplit _ -> error "TODO"
split _ = error "The impossible has occurred"

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (files)         Split files."
    ]
  exitFailure

type ParseFun a = [Token] -> Err a

run :: ParseFun Act -> String -> IO (Act)
run p s = let ts = myLexer s in case p ts of
           Bad s    -> error "could not parse"
           Ok  (Main b) -> return (Main b)

runFile :: ParseFun Act -> FilePath -> IO (Act)
runFile p f = readFile f >>= run p

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    fs -> do
      (Main b):[] <- mapM (runFile pAct) fs
      mapM_ (B.putStrLn . encode . split ) b
    

defaultEnv :: [(String, Ident)]
defaultEnv = [("CALLER", Ident "CALLER_VAR")]

toTDecl :: Decl -> TDecl
toTDecl (Dec ty var) = TDec var ty

