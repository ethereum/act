{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}

module Main where

import Data.Aeson hiding (Bool, Number)
import EVM.SymExec (ProofResult(..))
import GHC.Generics
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr, stdout)
import Data.SBV hiding (preprocess, sym, prove)
import Data.Text (pack, unpack)
import Data.List
import Data.Either (lefts)
import Data.Maybe
import Data.Tree
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
import Syntax.Annotated
import Syntax.Untyped
import Enrich
import K hiding (normalize, indent)
import SMT
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


-----------------------
-- *** Dispatch *** ---
-----------------------


main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      Lex f -> lex' f
      Parse f -> parse' f
      Type f -> type' f
      Prove file' solver' smttimeout' debug' -> prove file' solver' smttimeout' debug'
      Coq f -> coq' f
      K spec' soljson' gas' storage' extractbin' out' -> k spec' soljson' gas' storage' extractbin' out'
      HEVM spec' soljson' solver' smttimeout' debug' -> hevm spec' soljson' solver' smttimeout' debug'


---------------------------------
-- *** CLI implementation *** ---
---------------------------------


lex' :: FilePath -> IO ()
lex' f = do
  contents <- readFile f
  print $ lexer contents

parse' :: FilePath -> IO ()
parse' f = do
  contents <- readFile f
  case parse $ lexer contents of
    Bad e -> prettyErr contents e
    Ok x -> print x

type' :: FilePath -> IO ()
type' f = do
  contents <- readFile f
  case compile contents of
    Ok a  -> B.putStrLn $ encode a
    Bad e -> prettyErr contents e

prove :: FilePath -> Maybe Text -> Maybe Integer -> Bool -> IO ()
prove file' solver' smttimeout' debug' = do
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

      (<->) :: Doc -> [Doc] -> Doc
      x <-> y = x <$$> line <> (indent 2 . vsep $ y)

      failMsg :: [SMT.SMTResult] -> Doc
      failMsg results
        | not . null . catUnknowns $ results
            = text "could not be proven due to a" <+> (yellow . text $ "solver timeout")
        | not . null . catErrors $ results
            = (red . text $ "failed") <+> "due to solver errors:" <-> ((fmap (text . show)) . catErrors $ results)
        | otherwise
            = (red . text $ "violated") <> colon <-> (fmap pretty . catModels $ results)

      passMsg :: Doc
      passMsg = (green . text $ "holds") <+> (bold . text $ "∎")

      accumulateResults :: (Bool, Doc) -> (Query, [SMT.SMTResult]) -> (Bool, Doc)
      accumulateResults (status, report) (query, results) = (status && holds, report <$$> msg <$$> smt)
        where
          holds = all isPass results
          msg = identifier query <+> if holds then passMsg else failMsg results
          smt = if debug' then line <> getSMT query else empty

    solverInstance <- spawnSolver config
    pcResults <- mapM (runQuery solverInstance) (concatMap mkPostconditionQueries claims)
    invResults <- mapM (runQuery solverInstance) (mkInvariantQueries claims)
    stopSolver solverInstance

    let
      invTitle = line <> (underline . bold . text $ "Invariants:") <> line
      invOutput = foldl' accumulateResults (True, empty) invResults

      pcTitle = line <> (underline . bold . text $ "Postconditions:") <> line
      pcOutput = foldl' accumulateResults (True, empty) pcResults

    render $ vsep
      [ ifExists invResults invTitle
      , indent 2 $ snd invOutput
      , ifExists pcResults pcTitle
      , indent 2 $ snd pcOutput
      ]

    unless (fst invOutput && fst pcOutput) exitFailure


coq' :: FilePath -> IO()
coq' f = do
  contents <- readFile f
  proceed contents (compile contents) $ \claims ->
    TIO.putStr $ coq claims

k :: FilePath -> FilePath -> Maybe [(Id, String)] -> Maybe String -> Bool -> Maybe String -> IO ()
k spec' soljson' gas' storage' extractbin' out' = do
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

hevm :: FilePath -> FilePath -> Maybe Text -> Maybe Integer -> Bool -> IO ()
hevm spec' soljson' solver' smttimeout' smtdebug' = do
  specContents <- readFile spec'
  solContents  <- readFile soljson'
  let preprocess = do refinedSpecs  <- compile specContents
                      (sources, _, _) <- errMessage (nowhere, "Could not read sol.json")
                        $ Solidity.readJSON $ pack solContents
                      return ([b | B b <- refinedSpecs], sources)
  proceed specContents preprocess $ \(specs, sources) -> do
    -- TODO: prove constructor too
    passes <- forM specs $ \behv -> do
      res <- runSMTWithTimeOut solver' smttimeout' smtdebug' $ proveBehaviour sources behv
      case res of
        Qed posts -> let msg = "Successfully proved " <> showBehv behv <> ", "
                            <> show (length $ last $ levels posts) <> " cases."
                      in putStrLn msg >> return (Right msg)
        Cex _     -> let msg = "Failed to prove " <> showBehv behv
                      in putStrLn msg >> return (Left msg)
        Timeout _ -> let msg = "Solver timeout when attempting to prove " <> showBehv behv
                      in putStrLn msg >> return (Left msg)
    let failures = lefts passes

    putStrLn . unlines $
      if null failures
        then [ "==== SUCCESS ===="
             , ""
             , soljson' <> " fully satisfies " <> spec' <> "."
             ]
        else [ "==== FAILURE ===="
             , ""
             , show (length failures) <> " out of " <> show (length passes) <> " claims unproven:"
             ]
          <> zipWith (\i msg -> show (i::Int) <> "\t" <> msg) [1..] failures
    unless (null failures) exitFailure
  where
    showBehv behv = _name behv <> "(" <> show (_mode behv) <> ")"

-------------------
-- *** Util *** ---
-------------------


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
compile = pure . fmap annotate . enrich <=< typecheck <=< parse . lexer

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
  hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
  hPutStrLn stderr msg
  exitFailure
prettyErr contents (AlexPn _ line' col, msg) = do
  let cxt = safeDrop (line' - 1) (lines contents)
  hPutStrLn stderr $ show line' <> " | " <> head cxt
  hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
  hPutStrLn stderr msg
  exitFailure
  where
    safeDrop :: Int -> [a] -> [a]
    safeDrop 0 a = a
    safeDrop _ [] = []
    safeDrop _ [a] = [a]
    safeDrop n (_:xs) = safeDrop (n-1) xs

-- | prints a Doc, with wider output than the built in `putDoc`
render :: Doc -> IO ()
render doc = displayIO stdout (renderPretty 0.9 120 doc)
