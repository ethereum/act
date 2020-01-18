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
  { _name      :: Ident,
    _contract  :: Ident,
    _StatusCode :: String,
    _return     :: Exp,
--    _env        :: [(String, Ident)],
    _calldata  :: BYExp,
--    _variables :: [(Ident, Type)],
    _preStore  :: [(Entry, Exp)],
    _postStore :: [(Entry, Exp)],
    _preCondition :: [BExp],
    _postCondition :: [BExp]
  } deriving (Show)

instance ToJSON Obligation where
  toJSON (Obligation { .. }) = object [ "name" .= (show _name)
           , "contract"  .= (show _contract)
           , "statusCode"  .= (show _StatusCode)
           , "return"  .= show _return
           , "calldata"  .= show _calldata
           , "preStore"  .= show _preStore
           , "postStore"  .= show _postStore
           , "preCondition"  .= show _preCondition
           , "postCondition"  .= show _postCondition
           ]


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
    CaseSplit _ -> error "TODO"
split _ _ = error "The impossible has occurred"

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (files)         Split files."
    ]
  exitFailure

type ParseFun a = [Token] -> Err a

run :: (Show a) => ParseFun a -> String -> IO (Act)
run p s = let ts = myLexer s in case p ts of
           Bad s    -> do error "could not parse"
           Ok  (Main b) -> do
             putStrLn "\nParse Successful!"
             return (Main b)
           Ok _ -> error "not top level structure"

runFile :: (Show a) => ParseFun a -> FilePath -> IO ()
runFile p f = putStrLn f >> readFile f >>= run p

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    fs -> do
      tree <- mapM_ (runFile pAct) fs
      B.putStrLn $ encode tree
    

defaultEnv :: [(String, Ident)]
defaultEnv = [("CALLER", Ident "CALLER_VAR")]

toTDecl :: Decl -> TDecl
toTDecl (Dec ty var) = TDec var ty

