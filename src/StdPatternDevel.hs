module StdPatternDevel(
    runTheoremM, runTmSilentM, runProofByAsmM, runProofBySubArgM, runProofByUGM, runProofOpen
) where

import Internal.StdPattern
    ( runTheoremM,
      runTmSilentM,
      runProofByAsmM,
      runProofBySubArgM,
      runProofByUGM )

import Kernel(runProofOpen)