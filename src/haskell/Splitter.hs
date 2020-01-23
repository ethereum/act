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
import Data.Vector (fromList)
import qualified Data.ByteString.Lazy.Char8 as B

import AbsAct
import LexAct
import ParAct
import ErrM

data Obligation = Obligation
  { _name      :: String,
    _contract  :: String,
    _StatusCode :: String,
    _methodName :: String,
    _inputArgs  :: [Decl],
    _return     :: Exp,
    _preConditions :: [BExp]
--    _env        :: [(String, Ident)],
-- --    _variables :: [(Ident, Type)],
--     _preStore  :: [(Entry, Exp)],
--     _postStore :: [(Entry, Exp)],-
--     _postCondition :: [BExp]
  } deriving (Show)

instance ToJSON Obligation where
  toJSON (Obligation { .. }) =
    object [ "name" .= _name
           , "contract"  .= _contract
           , "statusCode"  .= _StatusCode
           , "methodName"  .= _methodName
           , "inputArgs"   .= (Array $ fromList (map
                                                (\(Dec abiType (Ident name)) ->
                                                  object [ pack name .= ppSolType abiType ])
                                                 _inputArgs))
           , "return"  .= kPrintBytes _return
           , "preConditions"  .= (Array $ fromList (fmap (String . pack . kPrintBool) _preConditions))
           -- , "calldata"  .= show _calldata
           -- , "preStore"  .= show _preStore
           -- , "postStore"  .= show _postStore
           -- , "postCondition"  .= show _postCondition
           ]


split :: Behaviour -> [Obligation]
split (Transition (Ident name) (Ident contract) (Ident methodName) args iffs claim) =
  case claim of
    Direct (ReturnP returnExpr)  ->
      --success case:
      [Obligation
      {_name     = name,
       _contract = contract,
       _StatusCode = "EVMC_SUCCESS",
       _methodName = methodName,
       _inputArgs  = args,
       _return     = returnExpr,
       _preConditions  = concat $ fmap iffHToBool iffs
--       _env        = defaultEnv,
--       _calldata   = methodName args,
       -- _variables  = [], --hmmm
       -- _preStore   = [],
       -- _postStore  = [],
       -- _postCondition = []
      }]
    CaseSplit _ -> error "TODO"

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
           Bad s    -> error "could not parse" -- TODO: how to get more information
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


ppSolType :: Type -> String
ppSolType Type_uint = "uint256"
ppSolType Type_int = "int256"
ppSolType Type_uint256 = "uint256"
ppSolType Type_int256 = "int256"
ppSolType Type_int126 = "int126"
ppSolType Type_uint126 = "uint126"
ppSolType Type_int8 = "int8"
ppSolType Type_uint8 = "uint8"
ppSolType Type_address = "address"
ppSolType Type_bytes32 = "bytes32"
ppSolType Type_bytes4 = "bytes4"
ppSolType Type_bool = "bool"

min :: Type -> IExp
min Type_uint = EInt 0
min _ = error "todo: min"

max :: Type -> IExp
max Type_uint = EInt 115792089237316195423570985008687907853269984665640564039
max _ = error "todo: max"
-- K specific printing
--Prints an act expression as a K ByteArray
kPrintBytes :: Exp -> String
kPrintBytes _ = "TODO: krpintBytes" --todo

kPrintInt :: IExp -> String
kPrintInt _ = "TODO: kprintInt"

iffHToBool :: IffH -> [BExp]
iffHToBool (Iff bexps) = bexps
iffHToBool (IffIn abitype exprs) =
  fmap
    (\exp -> BAnd (BGEQ (Main.min abitype) exp) (BGEQ exp (Main.max abitype)))
    exprs

kPrintBool :: BExp -> String
kPrintBool _ = "TODO: kPrintBool"
