module RuleSets.PredLogic
(
    uiM, eiM, LogicError(..), PredLogicRule(..), PredLogSchemaRule(..),
    ProofByUGSchema(..), ProofByUGError,
    PredLogicSent(..), 
    checkTheoremM, establishTmSilentM, expandTheoremM, proofByUG,
    runTheoremM,
    runTmSilentM, runProofByUGM, EstTmMError, ExpTmMError,
    TheoremSchemaMT(..)


) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRule(..), PredLogicRule(..), PredLogSchemaRule(..),
    uiM, eiM,     ProofByUGSchema(..), ProofByUGError,
    PredLogicSent(..), 
    checkTheoremM, establishTmSilentM, expandTheoremM, proofByUG,
    runTheoremM,
    runTmSilentM, runProofByUGM, EstTmMError, ExpTmMError, TheoremSchemaMT(..))