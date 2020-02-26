{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
import Data.List
import Data.Aeson hiding (Bool)
import Data.Aeson.Types hiding (Bool)
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
import Options.Generic
--command line options
data Command w
  = Parse { file  :: w ::: String <?> "Path to file to parse"}
  | Compile { file :: w ::: String <?> "Path to file to parse"
            , k    :: w ::: Bool <?> "output k files"
            , ir   :: w ::: Bool <?> "output intermediate representation"
            , coq  :: w ::: Bool <?> "output coq files"
            , out  :: w ::: Maybe String <?> "output path"
            }
    deriving (Generic)

instance ParseRecord (Command Wrapped)
deriving instance Show (Command Unwrapped)

main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      (Parse f) -> do contents <- readFile f      
                      case pAct $ myLexer contents of
                        (Ok (Main a)) -> do print "success"
                                            print a
                        (Bad s) -> error s

      (Type f) -> do contents <- readFile f      
                      case pAct $ myLexer contents of --todo: proper monadic lifts
                        (Ok (Main a)) -> case typecheck a of
                          (Ok a)  -> print "success"
                          (Bad s) -> error s
                        (Bad s) -> error s
      (Compile f _ _ _ out) -> case (ir cmd) of
        True -> do contents <- readFile f
                   case pAct $ myLexer contents of
                     (Ok (Main behaviours)) -> mapM_ (B.putStrLn . encode . split) behaviours
                     (Bad errormsg)         -> error errormsg
        False -> error "TODO"

typecheck :: [Behaviour] -> Err Act
typecheck bs = 

--checks a transition given a typing of its storage variables
checkTransition :: Behaviour -> Map Var (Map Var Type) -> Err Act

  
--Intermediate format
data Obligation = Obligation
  { _name      :: String,
    _contract  :: String,
    _StatusCode :: String,
    _methodName :: String,
    _inputArgs  :: [Decl],
    _return     :: (Exp, Type),
    _preConditions :: [Exp]
--    _env        :: [(String, Var)],
-- --    _variables :: [(Var, Type)],
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
           , "inputArgs"   .= (Data.Aeson.Types.Array $ fromList (map
                                                (\(Dec abiType name) ->
                                                  object [ "name" .= pprint name, "type" .= pprint abiType ])
                                                 _inputArgs))
           , "return"  .= object [ "value" .= pprint (fst _return), "type" .= pprint (snd _return) ]
           , "preConditions"  .= (Data.Aeson.Types.Array $ fromList (fmap (String . pack . pprint) _preConditions))
           -- , "calldata"  .= show _calldata
           -- , "preStore"  .= show _preStore
           -- , "postStore"  .= show _postStore
           -- , "postCondition"  .= show _postCondition
           ]


split :: Behaviour -> [Obligation]
split (Transition (Var name) (Var contract) (Var methodName) args iffs claim) =
  case claim of
    Direct (ReturnP returnExpr)  ->
      --success case:
      [Obligation
      {_name     = name,
       _contract = contract,
       _StatusCode = "EVMC_SUCCESS",
       _methodName = methodName,
       _inputArgs  = args,
       _return     = (returnExpr, getExpType returnExpr),
       _preConditions  = concat $ fmap iffHToBool iffs
--       _env        = defaultEnv,
--       _calldata   = methodName args,
       -- _variables  = [], --hmmm
       -- _preStore   = [],
       -- _postStore  = [],
       -- _postCondition = []
      }]
    CaseSplit _ -> error "TODO"

getExpType :: Exp -> Type
getExpType (Int _) = Type_uint
getExpType (Bool _) = Type_bool
getExpType (Bytes _) = Type_bytes


defaultEnv :: [(String, Var)]
defaultEnv = [("CALLER", Var "CALLER_VAR")]
class Pretty a where
  pprint :: a -> String

instance Pretty Var where
  pprint (Var a) = a

instance Pretty Arg where
  pprint (Argm a) = pprint a


instance Pretty Exp where
  pprint (Int a) = pprint a
  pprint (Bool a) = pprint a
  pprint (Bytes a) = pprint a

instance Pretty Exp where
-- integers
  pprint (EAdd x y) = pprint x <> " + " <> pprint y
  pprint (ESub x y) = pprint x <> " - " <> pprint y
  pprint (EMul x y) = pprint x <> " * " <> pprint y
  pprint (EDiv x y) = pprint x <> " / " <> pprint y
  pprint (EMod x y) = pprint x <> " % " <> pprint y
  pprint (EExp x y) = pprint x <> " ^ " <> pprint y
  pprint (ITE b x y) = "if" <> pprint b <>
                     "then" <> pprint x <>
                     "else" <> pprint y
  pprint Wild = "_"
  pprint (IEntry a) = pprint a
  pprint (IVar a)   = pprint a
  pprint (EInt a)   = show a
  pprint (Func x y) = pprint x <> "(" <> intercalate "," (fmap pprint y) <> ")"
-- booleans
  pprint (BAnd x y)  = pprint x <> " and " <> pprint y
  pprint (BOr x y)   = pprint x <> " or "  <> pprint y
  pprint (BImpl x y) = pprint x <> " => "  <> pprint y
  pprint (BEq x y)   = pprint x <> " == "  <> pprint y
  pprint (BNeq x y)  = pprint x <> " =/= " <> pprint y
  pprint (BLEQ x y)  = pprint x <> " <= "  <> pprint y
  pprint (BLE x y)   = pprint x <> " < "   <> pprint y
  pprint (BGEQ x y)  = pprint x <> " >= "  <> pprint y
  pprint (BGE x y)   = pprint x <> " > "   <> pprint y
  pprint BTrue = "true"
  pprint BFalse = "false"
  pprint BWildcard = "_"
-- bytes
  pprint (BYAdd x y)  = pprint x <> "++" <> pprint y
  pprint (Slice byexp a b) = pprint byexp
    <> "[" <> show a <> ".." <> show b <> "]"
  pprint (BYHash x) = "keccak256" <> pprint x
  pprint (BYAbiE x) = "abiEncode" <> pprint x
  pprint (Newaddr x) = "newAddr"  <> map pprint x
  pprint (Newaddr2 x) = "newAddr" <> map pprint x


instance Pretty Type where
  pprint Type_uint = "uint256"
  pprint Type_int = "int256"
  pprint Type_bytes = "bytes"
  pprint Type_uint256 = "uint256"
  pprint Type_int256 = "int256"
  pprint Type_int126 = "int126"
  pprint Type_uint126 = "uint126"
  pprint Type_int8 = "int8"
  pprint Type_uint8 = "uint8"
  pprint Type_address = "address"
  pprint Type_bytes32 = "bytes32"
  pprint Type_bytes4 = "bytes4"
  pprint Type_bool = "bool"
  pprint Type_string = "string"

min :: Type -> Exp
min Type_uint = IntLit 0
min Type_uint256 = IntLit 0
min Type_uint126 = IntLit 0
min Type_uint8 = IntLit 0
--todo, the rest

max :: Type -> Exp
max Type_uint    = EInt 115792089237316195423570985008687907853269984665640564039
max Type_uint256 = EInt 115792089237316195423570985008687907853269984665640564039
max _ = error "todo: max"


--Prints an act expression as a K ByteArray
kPrintBytes :: Exp -> String
kPrintBytes _ = "TODO: krpintBytes" --todo

iffHToBool :: IffH -> [Exp]
iffHToBool (Iff bexps) = bexps
iffHToBool (IffIn abitype exprs) =
  fmap
    (\exp -> BAnd (BLEQ (Main.min abitype) exp) (BLEQ exp (Main.max abitype)))
    exprs
