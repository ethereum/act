module Dev where


import CLI
import Coq (coq)
import Enrich 
import qualified Data.Text as T

writeCoqFile :: FilePath -> FilePath -> IO ()
writeCoqFile src trg = do
    contents <- readFile src
    proceed contents (enrich <$> compile contents) $ \claims ->
      writeFile trg . T.unpack $ coq claims

