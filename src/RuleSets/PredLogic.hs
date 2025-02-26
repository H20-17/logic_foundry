module RuleSets.PredLogic
(
    simpL, adj, uiM, eiM, LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM
) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    simpL, adj, uiM, eiM,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM)