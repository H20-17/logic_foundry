module RuleSets.PredLogicUntyped
(
    simpL, adj, uiM, eiM, LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM,
    remarkM
) where

import RuleSets.Internal.PredLogic(LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    simpL, adj, uiM, eiM,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, remarkM)


import qualified RuleSets.Internal.PredLogic as PLI (runProofByUGM)

import StdPattern
import Data.Data (Typeable)
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )

runProofByUGM :: (ProofStd s (LogicError s sE o t ()) [LogicRule s sE o t ()] o (), Monad m,
                       PredLogicSent s t (), MonadThrow m,
                       Show s, Typeable s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o () m, Show o, Typeable o,
                       Typeable t, Show t, TypedSent o () sE s)
                 =>   ProofGenTStd () [LogicRule s sE o t ()] s o m x
                            -> ProofGenTStd () [LogicRule s sE o t ()] s o m (s, [Int], x)
runProofByUGM = PLI.runProofByUGM ()
