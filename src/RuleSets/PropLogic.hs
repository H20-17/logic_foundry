module RuleSets.PropLogic
(LogicError, mpM, simpLM, adjM,
    PropLogicRule(..),PropLogSchemaRule(.. ),
    ProofByAsmSchema(..), ProofByAsmError, runProofByAsmM,  proofByAsm, PropLogicSent(..)
) where

import RuleSets.Internal.PropLogic(mpM, simpLM, adjM,
              LogicError, LogicRule(..), PropLogicRule(..), PropLogSchemaRule(..),
              
              ProofByAsmSchema(..), ProofByAsmError, runProofByAsmM,  proofByAsm, PropLogicSent(..)
              )