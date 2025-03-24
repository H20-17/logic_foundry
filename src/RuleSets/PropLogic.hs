module RuleSets.PropLogic
(LogicError, mpM, simpLM, adjM,
    LogicRuleClass(..),SubproofRule(.. ),
    ProofByAsmSchema(..), SubproofError(..), runProofByAsmM,  LogicSent(..),
    contraFM, absurdM,
    MetaRuleError(..), disjIntroLM, disjIntroRM, disjElimM, doubleNegElimM,
    deMorganConjM, deMorganDisjM, bicondIntroM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM,
    peircesLawM, modusTollensM, imp2ConjM
) where

import RuleSets.Internal.PropLogic(mpM, simpLM, adjM,
              LogicError, LogicRuleClass(..), SubproofRule(..),
              
              ProofByAsmSchema(..), SubproofError(..), runProofByAsmM,  LogicSent(..),
              SubproofMException(..), contraFM, absurdM,
               MetaRuleError(..), disjIntroLM, disjIntroRM, disjElimM, doubleNegElimM,
              deMorganConjM, deMorganDisjM, bicondIntroM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM,
              peircesLawM, modusTollensM, imp2ConjM
              )