module RuleSets.BaseLogic
(
    remarkM, BaseLogRule (..), LogicError(..), fakePropM, fakeConstM, ProofBySubArgError(..),
    ProofBySubArgSchema(..), proofBySubArg, runProofBySubArgM
) where

import RuleSets.Internal.BaseLogic(remarkM, LogicError(..), BaseLogRule (..),fakePropM,fakeConstM,
          ProofBySubArgError(..), ProofBySubArgSchema(..), proofBySubArg,
          runProofBySubArgM)