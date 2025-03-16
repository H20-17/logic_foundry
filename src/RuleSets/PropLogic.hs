module RuleSets.PropLogic
(LogicError, mpM, simpLM, adjM,
    LogicRuleClass(..),PropLogSchemaRule(.. ),
    ProofByAsmSchema(..), SubproofError, runProofByAsmM,  PropLogicSent(..)
) where

import RuleSets.Internal.PropLogic(mpM, simpLM, adjM,
              LogicError, LogicRuleClass(..), PropLogSchemaRule(..),
              
              ProofByAsmSchema(..), SubproofError, runProofByAsmM,  PropLogicSent(..),
              SubproofMException(..)
              )