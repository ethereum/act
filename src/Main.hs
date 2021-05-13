{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Data.Aeson hiding (Bool, Number)
import GHC.Generics
import System.Exit ( exitFailure )
import Data.SBV hiding (preprocess)
import Data.Text (pack)
import Data.List
import Data.Maybe
import qualified EVM.Solidity as Solidity
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as Map
import System.Environment (setEnv)
import System.IO (stdout)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.ByteString.Lazy.Char8 as B

import Control.Monad

import ErrM
import Lex (lexer)
import Options.Generic
import Parse
import RefinedAst
import Enrich
import K hiding (normalize, indent)
import SMT
import Syntax
import Type
import Coq hiding (indent)
import HEVM

--command line options
data Command w
  = Lex             { file       :: w ::: String               <?> "Path to file"}

  | Parse           { file       :: w ::: String               <?> "Path to file"}

  | Type            { file       :: w ::: String               <?> "Path to file"}

  | Prove           { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: z3 (default) or cvc4"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Coq             { file       :: w ::: String               <?> "Path to file"}

  | K               { spec       :: w ::: String               <?> "Path to spec"
                    , soljson    :: w ::: String               <?> "Path to .sol.json"
                    , gas        :: w ::: Maybe [(Id, String)] <?> "Gas usage per spec"
                    , storage    :: w ::: Maybe String         <?> "Path to storage definitions"
                    , extractbin :: w ::: Bool                 <?> "Put EVM bytecode in separate file"
                    , out        :: w ::: Maybe String         <?> "output directory"
                    }

  | HEVM            { spec       :: w ::: String               <?> "Path to spec"
                    , soljson    :: w ::: String               <?> "Path to .sol.json"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: z3 (default) or cvc4"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }
 deriving (Generic)

deriving instance ParseField [(Id, String)]
instance ParseRecord (Command Wrapped)
deriving instance Show (Command Unwrapped)

main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      (Lex f) -> do contents <- readFile f
                    print $ lexer contents

      (Parse f) -> do contents <- readFile f
                      case parse $ lexer contents of
                        Bad e -> prettyErr contents e
                        Ok x -> print x

      (Type f) -> do contents <- readFile f
                     case compile contents of
                       Ok a  -> B.putStrLn $ encode a
                       Bad e -> prettyErr contents e

      (Prove file' solver' smttimeout' debug') -> do
        let
          parsedSolver = case solver' of
            Just "z3" -> SMT.Z3
            Just "cvc4" -> SMT.CVC4
            Nothing -> SMT.Z3
            Just input -> error $ "unrecognized solver: " <> show input
          config = SMT.SMTConfig (parsedSolver) (fromMaybe 20000 smttimeout') debug'
        contents <- readFile file'
        proceed contents (compile contents >>= (analyze config)) $ \(ok, report) -> do
          render report
          unless ok exitFailure

      (Coq f) -> do
        contents <- readFile f
        proceed contents (compile contents) $ \claims ->
          TIO.putStr $ coq claims

      (K spec' soljson' gas' storage' extractbin' out') -> do
        specContents <- readFile spec'
        solContents  <- readFile soljson'
        let kOpts = KOptions (maybe mempty Map.fromList gas') storage' extractbin'
            errKSpecs = do refinedSpecs <- compile specContents
                           (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                             $ Solidity.readJSON $ pack solContents
                           forM [b | B b <- refinedSpecs]
                             $ makekSpec sources kOpts
        proceed specContents errKSpecs $ \kSpecs -> do
          let printFile (filename, content) = case out' of
                Nothing -> putStrLn (filename <> ".k") >> putStrLn content
                Just dir -> writeFile (dir <> "/" <> filename <> ".k") content
          forM_ kSpecs printFile

      (HEVM spec' soljson' solver' smttimeout' debug') -> do
        specContents <- readFile spec'
        solContents  <- readFile soljson'
        let preprocess = do refinedSpecs  <- compile specContents
                            (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                              $ Solidity.readJSON $ pack solContents
                            return ([b | B b <- refinedSpecs], sources)
        proceed specContents preprocess $ \(specs, sources) -> do
          -- TODO: prove constructor too
          passes <- forM specs $ \behv -> do
            res <- runSMTWithTimeOut solver' smttimeout' debug' $ proveBehaviour sources behv
            case res of
              Left (_, posts) -> do
                 putStrLn $ "Successfully proved " <> (_name behv) <> "(" <> show (_mode behv) <> ")"
                   <> ", " <> show (length posts) <> " cases."
                 return True
              Right _ -> do
                 putStrLn $ "Failed to prove " <> (_name behv) <> "(" <> show (_mode behv) <> ")"
--                 putStrLn $ "Counterexample: (TODO)"
--                 showCounterexample vm Nothing -- TODO: provide signature
                 return False
          unless (and passes) exitFailure

-- cvc4 sets timeout via a commandline option instead of smtlib `(set-option)`
runSMTWithTimeOut :: Maybe Text -> Maybe Integer -> Bool -> Symbolic a -> IO a
runSMTWithTimeOut solver' maybeTimeout debug' sym
  | solver' == Just "cvc4" = do
      setEnv "SBV_CVC4_OPTIONS" ("--lang=smt --incremental --interactive --no-interactive-prompt --model-witness-value --tlimit-per=" <> show timeout)
      res <- runSMTWith cvc4{verbose=debug'} sym
      setEnv "SBV_CVC4_OPTIONS" ""
      return res
  | solver' == Just "z3" = runwithz3
  | isNothing solver' = runwithz3
  | otherwise = error "Unknown solver. Currently supported solvers; z3, cvc4"
 where timeout = fromMaybe 20000 maybeTimeout
       runwithz3 = runSMTWith z3{verbose=debug'} $ (setTimeOut timeout) >> sym

-- | Fail on error, or proceed with continuation
proceed :: PrintableError a => String -> Err a b -> (b -> IO ()) -> IO ()
proceed contents (Bad e) _ = prettyErr contents e
proceed _ (Ok a) continue = continue a

compile :: String -> TypeErr [Claim]
compile contents = enrich <$> ((parse (lexer contents)) >>= typecheck)

prove :: SMT.SMTConfig -> String -> SMTErr (Bool, Doc)
prove config contents = do
  claims <- compile contents
  analyze config claims

-- | prints a Doc, with wider output than the built in `putDoc`
render :: Doc -> IO ()
render doc = displayIO stdout (renderPretty 0.9 120 doc)
