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
import System.IO (hPutStrLn, stderr, stdout)
import Data.SBV hiding (preprocess)
import Data.Text (pack, unpack)
import Data.List
import Data.Maybe
import qualified EVM.Solidity as Solidity
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as Map
import System.Environment (setEnv)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.ByteString.Lazy.Char8 as B

import Control.Monad

import ErrM
import Lex (lexer, AlexPosn(..))
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
import Print

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
          parseSolver s = case s of
            Just "z3" -> SMT.Z3
            Just "cvc4" -> SMT.CVC4
            Nothing -> SMT.Z3
            Just _ -> error "unrecognized solver"
          config = SMT.SMTConfig (parseSolver solver') (fromMaybe 20000 smttimeout') debug'
        contents <- readFile file'
        proceed contents (compile contents) $ \claims -> do
          let
            catModels results = [m | Sat m <- results]
            catErrors results = [e | e@SMT.Error {} <- results]
            catUnknowns results = [u | u@SMT.Unknown {} <- results]

            getBehvName :: Query -> Doc
            getBehvName (Postcondition (C _) _ _) = (text "the") <+> (bold . text $ "constructor")
            getBehvName (Postcondition (B behv) _ _) = (text "behaviour") <+> (bold . text $ _name behv)
            getBehvName _ = error "Internal Error: invalid query"

            identifier :: Query -> Doc
            identifier (q@Inv {}) = (bold . text. prettyExp . getTarget $ q) <+> text "of" <+> (bold . text . getContract $ q)
            identifier (q@Postcondition {}) = (bold . text. prettyExp . getTarget $ q) <+> text "in" <+> getBehvName q <+> text "of" <+> (bold . text . getContract $ q)

            buildFailMsg :: Query -> [SMT.SMTResult] -> Doc
            buildFailMsg query results
              | not . null . catUnknowns $ results = identifier query <+> text "could not be proven due to a solver timeout"
              | not . null . catErrors $ results = identifier query <+> (red . text $ "failed") <+> "due to solver errors:"
                                                     <$$> line <> (indent 2 $ vsep (fmap (text . show) (catErrors results)))
              | otherwise = identifier query <+> ((red . text $ "violated") <> colon) <$$> line <> (indent 2 $ vsep (fmap pretty (catModels results)))

            handleResults :: (Query, [SMT.SMTResult]) -> (Bool, Doc, Doc)
            handleResults (query, results) =
              if or (fmap isFail results)
              then (False, buildFailMsg query results, getSMT query)
              else (True, (identifier query) <+> ((green . text $ "holds") <+> (bold . text $ "∎")), getSMT query)

            accumulateResults :: (Bool, Doc) -> (Bool, Doc, Doc) -> (Bool, Doc)
            accumulateResults acc (r, msg, smt) = (fst acc && r, doc)
              where doc = snd acc <$$> if debug'
                                          then msg <$$> line <> "with the following smt:" <$$> line <> smt <> line
                                          else msg <> line

            getSMT :: Query -> Doc
            getSMT (Postcondition _ _ smt) = pretty smt
            getSMT (Inv _ (_, csmt) behvs) = text "; constructor" <$$> sep' <$$> line <> pretty csmt <$$> vsep (fmap formatBehv behvs)
              where
                formatBehv (b, smt) = line <> text "; behaviour: " <> (text . _name $ b) <$$> sep' <$$> line <> pretty smt
                sep' = text "; -------------------------------"

            render :: Doc -> IO ()
            render doc = displayIO stdout (renderPretty 0.9 120 doc)


          solverInstance <- spawnSolver config
          pcResults <- (fmap handleResults) <$> mapM (runQuery solverInstance) (concatMap mkPostconditionQueries claims)
          invResults <- (fmap handleResults) <$> mapM (runQuery solverInstance) (mkInvariantQueries claims)
          stopSolver solverInstance

          let
            invTitle = if not . null $ invResults then (line <> (underline . bold . text $ "Invariants:") <> line) else empty
            invOutput = foldl' accumulateResults (True, empty) invResults

            pcTitle = if not . null $ pcResults then (line <> (underline . bold . text $ "Postconditions:") <> line) else empty
            pcOutput = foldl' accumulateResults (True, empty) pcResults

          render $ vsep [invTitle, indent 2 $ snd invOutput, pcTitle, indent 2 $ snd pcOutput]
          unless (fst invOutput && fst pcOutput) exitFailure

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
proceed :: String -> Err a -> (a -> IO ()) -> IO ()
proceed contents (Bad e) _ = prettyErr contents e
proceed _ (Ok a) continue = continue a

compile :: String -> Err [Claim]
compile contents = enrich <$> ((parse (lexer contents)) >>= typecheck)

prettyErr :: String -> (Pn, String) -> IO ()
prettyErr _ (pn, msg) | pn == nowhere = do
  hPutStrLn stderr "Internal error:"
  hPutStrLn stderr msg
  exitFailure
prettyErr contents (pn, msg) | pn == lastPos = do
  let culprit = last $ lines contents
      line' = length (lines contents) - 1
      col  = length culprit
  hPutStrLn stderr $ show line' <> " | " <> culprit
  hPutStrLn stderr $ unpack (Text.replicate (col + (length (show line' <> " | ")) - 1) " " <> "^")
  hPutStrLn stderr msg
  exitFailure
prettyErr contents (AlexPn _ line' col, msg) = do
  let cxt = safeDrop (line' - 1) (lines contents)
  hPutStrLn stderr $ show line' <> " | " <> head cxt
  hPutStrLn stderr $ unpack (Text.replicate (col + (length (show line' <> " | ")) - 1) " " <> "^")
  hPutStrLn stderr msg
  exitFailure
  where
    safeDrop :: Int -> [a] -> [a]
    safeDrop 0 a = a
    safeDrop _ [] = []
    safeDrop _ [a] = [a]
    safeDrop n (_:xs) = safeDrop (n-1) xs
