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

import Data.Aeson hiding (Bool, Number, json)
import GHC.Generics
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr, stdout)
import Data.Text (unpack)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import GHC.Natural


import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.ByteString as BS

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
import Consistency

import EVM.SymExec
import qualified EVM.Solvers as Solvers
import EVM.Solidity

--command line options
data Command w
  = Lex             { file       :: w ::: String               <?> "Path to file"}

  | Parse           { file       :: w ::: String               <?> "Path to file"}

  | Type            { file       :: w ::: String               <?> "Path to file"}

  | Prove           { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Coq             { file       :: w ::: String               <?> "Path to file"}

  | HEVM            { spec       :: w ::: String               <?> "Path to spec"
                    , sol        :: w ::: Maybe String         <?> "Path to .sol"
                    , code       :: w ::: Maybe ByteString     <?> "Runtime code"
                    , initcode   :: w ::: Maybe ByteString     <?> "Initial code"
                    , contract   :: w ::: String               <?> "Contract name"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
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
      Prove file' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        prove file' solver'' smttimeout' debug'
      Coq f -> coq' f
      HEVM spec' sol' code' initcode' contract' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        hevm spec' (Text.pack contract') sol' code' initcode' solver'' smttimeout' debug'


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

parseSolver :: Maybe Text -> IO Solvers.Solver
parseSolver s = case s of
                  Nothing -> pure Solvers.CVC5
                  Just s' -> case Text.unpack s' of
                              "z3" -> pure Solvers.Z3
                              "cvc5" -> pure Solvers.CVC5
                              input -> render (text $ "unrecognised solver: " <> input) >> exitFailure

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

checkOverlaps :: Act -> IO ()
checkOverlaps act = do
  res <- checkCases act
  mapM_ checkRes res
  where
    checkRes :: (Id, SMT.SMTResult) -> IO ()
    checkRes (name, res) =
      case res of
        Sat model -> failMsg ("Cases overlapping for behavior " <> name <> ".") (pretty model)
        Unsat -> passMsg $ "Cases nonoverlapping for behavior" <> name <> "."
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that cases are nonoverlapping for behavior " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that cases are nonoverlapping for behavior " <> name <> "."

    passMsg str = render (green $ text str)
    failMsg str model = render (red (text str) <> line <> model <> line) >> exitFailure
    errorMsg str = render (text str <> line) >> exitFailure

hevm :: FilePath -> Text -> Maybe FilePath -> Maybe ByteString -> Maybe ByteString -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
hevm actspec cid sol' code' initcode' solver' timeout debug' = do
  let opts = if debug' then debugVeriOpts else defaultVeriOpts
  (initcode'', bytecode) <- getBytecode
  specContents <- readFile actspec
  proceed specContents (enrich <$> compile specContents) $ \act -> do
    checkOverlaps act
    Solvers.withSolvers solver' 1 (naturalFromInteger <$> timeout) $ \solvers -> do
      -- Constructor check
      checkConstructors solvers opts initcode'' bytecode act
      -- Behavours check
      checkBehaviours solvers opts bytecode act
      -- ABI exhaustiveness sheck
      checkAbi solvers opts act bytecode

  where
    getBytecode :: IO (BS.ByteString, BS.ByteString)
    getBytecode =
      case (sol', code', initcode') of
        (Just f, Nothing, Nothing) -> do
          solContents  <- TIO.readFile f
          bytecodes cid solContents
        (Nothing, Just c, Just i) -> pure (i, c)
        (Nothing, Nothing, _) -> render (text "No runtime code is given") >> exitFailure
        (Nothing, _, Nothing) -> render (text "No initial code is given") >> exitFailure
        (Just _, Just _, _) -> render (text "Both Solidity file and runtime code are given. Please specify only one.") >> exitFailure
        (Just _, _, Just _) -> render (text "Both Solidity file and initial code are given. Please specify only one.") >> exitFailure


bytecodes :: Text -> Text -> IO (BS.ByteString, BS.ByteString)
bytecodes cid src = do
  (json, path) <- solidity' src
  let (Contracts sol', _, _) = fromJust $ readStdJSON json
  pure $ ((fromJust . Map.lookup (path <> ":" <> cid) $ sol').creationCode,
          (fromJust . Map.lookup (path <> ":" <> cid) $ sol').runtimeCode)



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
