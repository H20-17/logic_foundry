module RuleSets.BaseLogic
(
    remarkM, LogicRuleClass (..), LogicError(..), fakePropM, fakeConstM, SubproofError(..),
    ProofBySubArgSchema(..), runProofBySubArgM, SubproofRule(..)
) where

import RuleSets.Internal.BaseLogic(remarkM, LogicError(..), LogicRuleClass (..),fakePropM,fakeConstM,
          SubproofError(..), ProofBySubArgSchema(..), 
          runProofBySubArgM, SubproofRule(..))