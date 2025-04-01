module RuleSets.PredLogic
(
    uiM, eiM, LogicError(..), LogicRuleClass(..), SubproofRule(..),
    ProofByUGSchema(..),
    LogicSent(..), 
    checkTheoremM,  expandTheoremM,
    runTheoremM,
    runTmSilentM, runProofByUGM, SubproofError(..),
    TheoremSchemaMT(..),SubproofMException(..),
    TheoremAlgSchema,
    TheoremSchema,
    reverseANegIntroM, reverseENegIntroM,eNegIntroM, aNegIntroM,
    eiHilbertM,
    ChkTheoremError(..),
    MetaRuleError(..)


) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRuleClass(..), SubproofRule(..),
    uiM, eiM,     ProofByUGSchema(..),
    LogicSent(..), 
    checkTheoremM, expandTheoremM, 
    runTheoremM,
    runTmSilentM, runProofByUGM, SubproofError(..), TheoremSchemaMT(..)
    ,SubproofMException(..),
    TheoremAlgSchema,
    TheoremSchema,
    reverseANegIntroM, reverseENegIntroM,eNegIntroM, aNegIntroM,
    eiHilbertM,
    ChkTheoremError(..),
    MetaRuleError(..)
    )