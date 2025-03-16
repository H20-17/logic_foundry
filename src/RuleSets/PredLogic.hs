module RuleSets.PredLogic
(
    uiM, eiM, LogicError(..), LogicRuleClass(..), PredLogSchemaRule(..),
    ProofByUGSchema(..),
    PredLogicSent(..), 
    checkTheoremM,  expandTheoremM,
    runTheoremM,
    runTmSilentM, runProofByUGM, SubproofError(..),
    TheoremSchemaMT(..),SubproofMException(..)


) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRuleClass(..), PredLogSchemaRule(..),
    uiM, eiM,     ProofByUGSchema(..),
    PredLogicSent(..), 
    checkTheoremM, expandTheoremM, 
    runTheoremM,
    runTmSilentM, runProofByUGM, SubproofError(..), TheoremSchemaMT(..)
    ,SubproofMException(..)
    )