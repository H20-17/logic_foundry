module RuleSets.PredLogic
(
    uiM, eiM, LogicError(..), PredLogicRule(..),
    runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM, fakeConstM
) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRule(..),  fakeConstM, PredLogicRule(..),
    runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM, uiM, eiM)