module Dev where


import CLI
import Coq (coq)
import Enrich
import Consistency
import qualified EVM.Solvers as Solvers

import qualified Data.Text as T

writeCoqFile :: FilePath -> FilePath -> IO ()
writeCoqFile src trg = do
    contents <- readFile src
    proceed contents (enrich <$> compile contents) $ \claims ->
      writeFile trg . T.unpack $ coq claims


checkCaseConsistency :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkCaseConsistency actspec solver' smttimeout' debug' = do
  specContents <- readFile actspec
  proceed specContents (enrich <$> compile specContents) $ \act -> do
    checkCases act solver' smttimeout' debug'
