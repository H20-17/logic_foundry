module RuleSets.BaseLogic
(
    remarkM, LogicRuleClass (..), LogicError(..), fakePropM, fakeConstM, SubproofError(..),
    ProofBySubArgSchema(..), runProofBySubArgM, BaseLogSchemaRule(..)
) where

import RuleSets.Internal.BaseLogic(remarkM, LogicError(..), LogicRuleClass (..),fakePropM,fakeConstM,
          SubproofError(..), ProofBySubArgSchema(..), 
          runProofBySubArgM, BaseLogSchemaRule(..))