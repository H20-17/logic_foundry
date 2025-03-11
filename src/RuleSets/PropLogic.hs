module RuleSets.PropLogic
(LogicError, mpM, fakePropM, simpLM, adjM,
    runProofByAsmM, runProofBySubArgM, PropLogicRule(..)
) where

import RuleSets.Internal.PropLogic(mpM, fakePropM, simpLM, adjM,
             runProofByAsmM, runProofBySubArgM, LogicError, LogicRule(..), PropLogicRule(..))