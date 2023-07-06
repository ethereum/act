{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedRecordDot #-}

module CLI (main, compile, proceed) where

import Data.Aeson hiding (Bool, Number)
import GHC.Generics
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr, stdout)
import Data.Text (pack, unpack)
import Data.List
import Data.Maybe
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import GHC.Natural

import qualified Data.ByteString.Lazy.Char8 as B

import Control.Monad
import Control.Lens.Getter

import Error
import Lex (lexer, AlexPosn(..))
import Options.Generic
import Parse
import Syntax.Annotated
import Enrich
import SMT
import Type
import Coq hiding (indent)
import HEVM

import EVM.SymExec
import qualified EVM.Solvers as Solvers
import EVM.Solidity
import qualified EVM.Format as Format
import qualified EVM.Types as EVM

import Debug.Trace
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

  | HEVM            { spec       :: w ::: String               <?> "Path to spec"
                    , sol        :: w ::: Maybe String         <?> "Path to .sol"
                    , code       :: w ::: Maybe ByteString     <?> "Program bytecode"
                    , contract   :: w ::: String               <?> "Contract name"
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
      Prove file' solver' smttimeout' debug' -> prove file' (parseSolver solver') smttimeout' debug'
      Coq f -> coq' f
      HEVM spec' sol' soljson' contract' solver' smttimeout' debug' -> hevm spec' (Text.pack contract') sol' soljson' (parseSolver solver') smttimeout' debug'


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
  validation (prettyErrs contents) print (parse $ lexer contents)

type' :: FilePath -> IO ()
type' f = do
  contents <- readFile f
  validation (prettyErrs contents) (B.putStrLn . encode) (enrich <$> compile contents)

parseSolver :: Maybe Text -> Solvers.Solver
parseSolver s = case s of
                  Nothing -> Solvers.Z3
                  Just s' -> case Text.unpack s' of
                              "z3" -> Solvers.Z3
                              "cvc5" -> Solvers.CVC5
                              input -> error $ "unrecognised solver: " <> input

prove :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
prove file' solver' smttimeout' debug' = do
  let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout') debug'
  contents <- readFile file'
  proceed contents (enrich <$> compile contents) $ \claims -> do
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
    pcResults <- mapM (runQuery solverInstance) (mkPostconditionQueries claims)
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


coq' :: FilePath -> IO ()
coq' f = do
  contents <- readFile f
  proceed contents (enrich <$> compile contents) $ \claims ->
    TIO.putStr $ coq claims


hevm :: FilePath -> Text -> Maybe FilePath -> Maybe ByteString -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
hevm actspec cid sol' code' solver' timeout _ = do
  specContents <- readFile actspec
  bytecode <- getBytecode
  let act = validation (\_ -> error "Too bad") id (enrich <$> compile specContents)
  let actbehvs = translateAct act
  sequence_ $ flip fmap actbehvs $ \(name,behvs,calldata) ->
    Solvers.withSolvers solver' 1 (naturalFromInteger <$> timeout) $ \solvers -> do
      solbehvs <- removeFails <$> getBranches solvers bytecode calldata
      putStrLn $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
      -- equivalence check
      putStrLn "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
      checkResult =<< checkEquiv solvers debugVeriOpts solbehvs behvs
      -- input space exhaustiveness check
      putStrLn "\x1b[1mChecking if the input spaces are the same\x1b[m"
      checkResult =<< checkInputSpaces solvers debugVeriOpts solbehvs behvs

  -- ABI exhaustiveness sheck
  Solvers.withSolvers solver' 1 (naturalFromInteger <$> timeout) $ \solvers -> do
    putStrLn "\x1b[1mChecking if the ABI of the contract matches the specification\x1b[m"
    checkResult =<< checkAbi solvers debugVeriOpts act bytecode

  where
    removeFails branches = filter isSuccess $ branches

    isSuccess (EVM.Success _ _ _ _) = True
    isSuccess _ = False

    getBytecode =
      case (sol', code') of
        (Just f, Nothing) -> do
          solContents  <- TIO.readFile f
          bin <- solcRuntime cid solContents
          fmap fromJust $ solcRuntime cid solContents
        (Nothing, Just c) -> pure $ Format.hexByteString "" c
        (Nothing, Nothing) -> error "No EVM input is given. Please provide a Solidity file or EVM bytecode"
        (Just _, Just _) -> error "Both Solidity file and bytecode are given. Please specify only one."

-------------------
-- *** Util *** ---
-------------------

-- | Fail on error, or proceed with continuation
proceed :: Validate err => String -> err (NonEmpty (Pn, String)) a -> (a -> IO ()) -> IO ()
proceed contents comp continue = validation (prettyErrs contents) continue (comp ^. revalidate)

compile :: String -> Error String Act
compile = pure . annotate <==< typecheck <==< parse . lexer

prettyErrs :: Traversable t => String -> t (Pn, String) -> IO ()
prettyErrs contents errs = mapM_ prettyErr errs >> exitFailure
  where
  prettyErr (pn, msg) | pn == nowhere = do
    hPutStrLn stderr "Internal error:"
    hPutStrLn stderr msg
  prettyErr (pn, msg) | pn == lastPos = do
    let culprit = last $ lines contents
        line' = length (lines contents) - 1
        col  = length culprit
    hPutStrLn stderr $ show line' <> " | " <> culprit
    hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    hPutStrLn stderr msg
  prettyErr (AlexPn _ line' col, msg) = do
    let cxt = safeDrop (line' - 1) (lines contents)
    hPutStrLn stderr $ msg <> ":"
    hPutStrLn stderr $ show line' <> " | " <> head cxt
    hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    where
      safeDrop :: Int -> [a] -> [a]
      safeDrop 0 a = a
      safeDrop _ [] = []
      safeDrop _ [a] = [a]
      safeDrop n (_:xs) = safeDrop (n-1) xs

-- | prints a Doc, with wider output than the built in `putDoc`
render :: Doc -> IO ()
render doc = displayIO stdout (renderPretty 0.9 120 doc)
