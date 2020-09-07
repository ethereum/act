{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Aeson hiding (Bool, Number)
import GHC.Generics
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr)
import Data.SBV
import Data.Text (pack, unpack)
import Data.Maybe
import qualified EVM.Solidity as Solidity
import qualified Data.Text as Text
import qualified Data.Map.Strict      as Map -- abandon in favor of [(a,b)]?
import System.Environment (setEnv)

import qualified Data.ByteString.Lazy.Char8 as B

import Control.Monad

import ErrM
import Lex (lexer, AlexPosn(..))
import Options.Generic
import Parse
import RefinedAst
import K hiding (normalize)
import Syntax
import Type
import Prove

--command line options
data Command w
  = Lex             { file       :: w ::: String               <?> "Path to file"}

  | Parse           { file       :: w ::: String               <?> "Path to file"}

  | Type            { file       :: w ::: String               <?> "Path to file"}

  | Prove           { file  :: w ::: String <?> "Path to file"
                    , solver :: w ::: Maybe Text <?> "Used SMT solver: z3 (default) or cvc4"
                    , smttimeout :: w ::: Maybe Integer
                        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    }

  | K               { spec       :: w ::: String               <?> "Path to spec"
                    , soljson    :: w ::: String               <?> "Path to .sol.json"
                    , gas        :: w ::: Maybe [(Id, String)] <?> "Gas usage per spec"
                    , storage    :: w ::: Maybe String         <?> "Path to storage definitions"
                    , extractbin :: w ::: Bool                 <?> "Put EVM bytecode in separate file"
                    , out        :: w ::: Maybe String         <?> "output directory"
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
                     case parse (lexer contents) >>= typecheck of
                       Ok a  -> B.putStrLn $ encode a
                       Bad e -> prettyErr contents e

      (Prove file solver smttimeout) -> do
        contents <- readFile file
        case parse (lexer contents) >>= typecheck of
          Bad e -> prettyErr contents e
          Ok claims -> do
            let
                handleResults ((Invariant c e), rs) = do
                  let msg = "Invariant " <> show e <> " of " <> show c <> ": "
                      results' = handleRes <$> rs
                      ok = foldl (||) False $ fst <$> results'
                  case ok of
                    False -> putStrLn $ msg <> "Q.E.D"
                    True -> putStrLn $ msg <> "\n" <> (concat $ snd <$> results')

                handleRes (SatResult res) = case res of
                  Unsatisfiable _ _ -> (False, "")
                  Satisfiable _ model -> (True, "Counter example found! " <> show model)
                  SatExtField _ model -> (True, "Counter example found! " <> show model)
                  Unknown _ reason -> (True, "Unknown! " <> show reason)
                  ProofError _ reasons _  -> (True, "Proof error! " <> show reasons)
                  DeltaSat _ _ _ -> error "Unexpected DeltaSat"

            results <- flip mapM (queries claims)
                          (\(i, qs) -> do
                            rs <- mapM (runSMTWithTimeOut solver smttimeout) qs
                            pure $ (i, rs)
                          )
            mapM_ handleResults results

      (K spec soljson gas storage extractbin out) -> do
        specContents <- readFile spec
        solContents  <- readFile soljson
        let kOpts = KOptions (maybe mempty Map.fromList gas) storage extractbin
        errKSpecs <- pure $ do refinedSpecs  <- parse (lexer specContents) >>= typecheck
                               (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                                 $ Solidity.readJSON $ pack solContents
                               forM (catBehvs refinedSpecs)
                                 $ makekSpec sources kOpts (catInvs refinedSpecs)
        case errKSpecs of
             Bad e -> prettyErr specContents e
             Ok kSpecs -> do
               let printFile (filename, content) = case out of
                     Nothing -> putStrLn (filename <> ".k") >> putStrLn content
                     Just dir -> writeFile (dir <> "/" <> filename <> ".k") content
               forM_ kSpecs printFile


-- cvc4 sets timeout via a commandline option instead of smtlib `(set-option)`
runSMTWithTimeOut :: Maybe Text -> Maybe Integer -> Symbolic () -> IO SatResult
runSMTWithTimeOut solver maybeTimeout sym
  | solver == Just "cvc4" = do
      setEnv "SBV_CVC4_OPTIONS" ("--lang=smt --incremental --interactive --no-interactive-prompt --model-witness-value --tlimit-per=" <> show timeout)
      res <- satWith cvc4{verbose=True} sym
      setEnv "SBV_CVC4_OPTIONS" ""
      return res
  | solver == Just "z3" = runwithz3
  | solver == Nothing = runwithz3
  | otherwise = error "Unknown solver. Currently supported solvers; z3, cvc4"
 where timeout = fromMaybe 20000 maybeTimeout
       runwithz3 = satWith z3{verbose=True} $ (setTimeOut timeout) >> sym


prettyErr :: String -> (Pn, String) -> IO ()
prettyErr contents pn@(AlexPn _ line col,msg) =
  if fst pn == nowhere then
    do hPutStrLn stderr "Internal error"
       hPutStrLn stderr msg
       exitFailure
  else
    do let cxt = safeDrop (line - 1) (lines contents)
       hPutStrLn stderr $ show line <> " | " <> head cxt
       hPutStrLn stderr $ unpack (Text.replicate (col + (length (show line <> " | ")) - 1) " " <> "^")
       hPutStrLn stderr $ msg
       exitFailure
  where
    safeDrop :: Int -> [a] -> [a]
    safeDrop 0 a = a
    safeDrop _ [] = []
    safeDrop _ [a] = [a]
    safeDrop n (_:xs) = safeDrop (n-1) xs
