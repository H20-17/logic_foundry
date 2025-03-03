module RuleSets.PredLogicUntyped
(
    simpL, adj, uiM, eiM, LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM
) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    simpL, adj, uiM, eiM,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM)


import qualified RuleSets.Internal.PredLogic as PLI (runProofByUGM)

import StdPattern
import Data.Data (Typeable)
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )

runProofByUGM :: (ProofStd s (LogicError s sE o t () lType) [LogicRule s sE o t () lType] o (), Monad m,
                       PredLogicSent s t () lType, MonadThrow m,
                       Show s, Typeable s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o () m, Show o, Typeable o,
                       Show lType, Typeable lType, Typeable t, Show t, TypedSent o () sE s)
                 =>   ProofGenTStd () [LogicRule s sE o t () lType] s o m x
                            -> ProofGenTStd () [LogicRule s sE o t () lType] s o m (s, [Int], x)
runProofByUGM = PLI.runProofByUGM ()
