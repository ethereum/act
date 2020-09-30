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
import System.IO (hPutStrLn, stderr)
import Data.SBV
import Data.SBV.Control hiding (timeout)
import Data.Text (pack, unpack)
import Data.Maybe
import Data.List
import qualified EVM.Solidity as Solidity
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict      as Map -- abandon in favor of [(a,b)]?
import System.Environment (setEnv)

import qualified Data.ByteString.Lazy.Char8 as B

import Control.Monad
import EVM.SymExec

import ErrM
import Lex (lexer, AlexPosn(..))
import Options.Generic
import Parse
import RefinedAst
import Enrich
import K hiding (normalize)
import Syntax
import Type
import Prove
import Coq
import HEVM

--command line options
data Command w
  = Lex             { file       :: w ::: String               <?> "Path to file"}

  | Parse           { file       :: w ::: String               <?> "Path to file"}

  | Type            { file       :: w ::: String               <?> "Path to file"}

  | Prove           { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: z3 (default) or cvc4"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose smt output (default: False)"
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
                    , debug      :: w ::: Bool           <?> "Print verbose smt output (default: False)"
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
        contents <- readFile file'
        proceed contents (compile contents) $ \claims -> do
            let
                handleResults ((Invariant c e), rs) = do
                  let msg = "\n============\n\nInvariant " <> show e <> " of " <> show c <> ": "
                      sep = "\n\n---\n\n"
                      results' = handleRes <$> rs
                      ok = not $ or $ fst <$> results'
                  if ok
                  then putStrLn $ msg <> "Q.E.D ✨"
                  else do
                      putStrLn $ msg <> "\n\n" <> intercalate sep (snd <$> results')
                      exitFailure

                handleRes (SatResult res) = case res of
                  Unsatisfiable _ _ -> (False, "")
                  Satisfiable _ model -> (True, "Counter example found!\n\n" <> show model)
                  Unknown _ reason -> (True, "Unknown! " <> show reason)
                  ProofError _ reasons _  -> (True, "Proof error! " <> show reasons)
                  SatExtField _ _ -> error "Extension field containing Infinite/epsilon"
                  DeltaSat {} -> error "Unexpected DeltaSat"

            results <- forM (queries claims)
                          (\(i, qs) -> do
                            rs <- mapM (satWithTimeOut solver' smttimeout' debug') qs
                            pure (i, rs)
                          )
            mapM_ handleResults results

      (Coq f) -> do
        contents <- readFile f
        proceed "" (parse (lexer contents)) $ \untyped ->
          proceed "" (enrich <$> (typecheck untyped)) $ \typed ->
            TIO.putStr $ coq (lookupVars untyped) typed

      (K spec' soljson' gas' storage' extractbin' out') -> do
        specContents <- readFile spec'
        solContents  <- readFile soljson'
        let kOpts = KOptions (maybe mempty Map.fromList gas') storage' extractbin'
            errKSpecs = do refinedSpecs <- compile specContents
                           (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                             $ Solidity.readJSON $ pack solContents
                           forM (catBehvs refinedSpecs)
                             $ makekSpec sources kOpts (catInvs refinedSpecs)
        proceed specContents errKSpecs $ \kSpecs -> do
          let printFile (filename, content) = case out' of
                Nothing -> putStrLn (filename <> ".k") >> putStrLn content
                Just dir -> writeFile (dir <> "/" <> filename <> ".k") content
          forM_ kSpecs printFile

      (HEVM spec soljson solver smttimeout debug) -> do
        specContents <- readFile spec
        solContents  <- readFile soljson
        let preprocess = do refinedSpecs  <- compile specContents
                            (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                              $ Solidity.readJSON $ pack solContents
                            return (catBehvs refinedSpecs, sources)
        proceed specContents preprocess $ \(specs, sources) ->
          runSMTWithTimeOut solver smttimeout debug $ do
            results <- forM specs $ \behv -> proveBehaviour sources behv >>= \case 
                Left (_, posts) -> query $ do
                  io $ putStrLn $ "Successfully proved " <> show (_name behv)
                     <> ", " <> show (length posts) <> " cases."
                  return True
                Right vm -> query $ do
                  io $ putStrLn $ "Failed to prove " <> show (_name behv)
                  io $ putStrLn $ "Counterexample: "
                  showCounterexample vm Nothing -- TODO: provide signature
                  return False
            query $ unless (and results) (io exitFailure)

-- cvc4 sets timeout via a commandline option instead of smtlib `(set-option)`
satWithTimeOut :: Maybe Text -> Maybe Integer -> Bool -> Symbolic () -> IO SatResult
satWithTimeOut solver' maybeTimeout debug' sym = case solver' of
  Just "cvc4" -> do
    setEnv "SBV_CVC4_OPTIONS" ("--lang=smt --interactive --incremental --no-interactive-prompt --model-witness-value --tlimit-per=" <> show timeout)
    res <- satWith cvc4{verbose=debug'} sym
    setEnv "SBV_CVC4_OPTIONS" ""
    return res
  Just "z3" -> runwithz3
  Nothing -> runwithz3
  _ -> error "Unknown solver. Currently supported solvers; z3, cvc4"
  where timeout = fromMaybe 20000 maybeTimeout
        runwithz3 = satWith z3{verbose=debug'} $ (setTimeOut timeout) >> sym

-- cvc4 sets timeout via a commandline option instead of smtlib `(set-option)`
runSMTWithTimeOut :: Maybe Text -> Maybe Integer -> Bool -> Symbolic a -> IO a
runSMTWithTimeOut solver maybeTimeout debug' sym
  | solver == Just "cvc4" = do
      setEnv "SBV_CVC4_OPTIONS" ("--lang=smt --incremental --interactive --no-interactive-prompt --model-witness-value --tlimit-per=" <> show timeout)
      res <- runSMTWith cvc4{verbose=debug'} sym
      setEnv "SBV_CVC4_OPTIONS" ""
      return res
  | solver == Just "z3" = runwithz3
  | solver == Nothing = runwithz3
  | otherwise = error "Unknown solver. Currently supported solvers; z3, cvc4"
 where timeout = fromMaybe 20000 maybeTimeout
       runwithz3 = runSMTWith z3{verbose=debug'} $ (setTimeOut timeout) >> sym

-- | Fail on error, or proceed to the continuation
proceed :: String -> Err a -> (a -> IO ()) -> IO ()
proceed contents (Bad e) _ = prettyErr contents e
proceed _ (Ok a) continue = continue a

compile :: String -> Err [Claim]
compile contents = enrich <$> ((parse (lexer contents)) >>= typecheck)

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
       hPutStrLn stderr msg
       exitFailure
  where
    safeDrop :: Int -> [a] -> [a]
    safeDrop 0 a = a
    safeDrop _ [] = []
    safeDrop _ [a] = [a]
    safeDrop n (_:xs) = safeDrop (n-1) xs
