{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}


module RuleSets.BaseLogic.Helpers
(
    remarkM, 
    fakePropM, fakeConstM, repM,
    runProofBySubArgM
) where

import RuleSets.BaseLogic.Core
import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless,forM )
import Data.Text (Text, unpack)
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import Data.Data (Typeable)
import Data.Map(lookup,insert)

import Control.Monad.RWS (MonadReader(ask))
import Data.Maybe ( isNothing )
import Control.Arrow (left)
import Control.Monad.Trans ( MonadTrans(lift) )
import Data.Map (Map,lookup)
import Internal.StdPattern
import Kernel




runProofBySubArgM :: HelperConstraints r1 s o tType sE eL m
                 =>   ProofGenTStd tType r1 s o m x
                            -> ProofGenTStd tType r1 s o m (s, [Int],x)
runProofBySubArgM prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let constdict = fmap fst (consts state)
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContextFrames = contextFrames context <> [False]
        let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState mempty mempty 0 0
        let preambleSteps = []
        (extraData,consequent,subproof,newSteps) 
            <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) prog
        mayMonadifyRes <- monadifyProofStd $ proofBySubArg consequent subproof
        idx <- maybe (error "No theorem returned by monadifyProofStd on subarg schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (consequent, idx, extraData)


remarkM :: HelperConstraints r s o tType sE eL m
          => Text -> ProofGenTStd tType r s o m [Int]
          
remarkM txt = do
    monadifyProofStd (remark txt)
    -- The index will be that of the last step generated.
    state <- getProofState
    context <- ask
    let stepCnt = stepCount state
    let idxPrefix = stepIdxPrefix context
    let finalIdx = idxPrefix <> [stepCnt-1]
    return finalIdx  


standardRuleM :: HelperConstraints r s o tType sE eL m
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex






repM :: HelperConstraints r s o tType sE eL m
          => s -> ProofGenTStd tType r s o m (s,[Int])
repM s = standardRuleM (rep s)

fakePropM :: HelperConstraints r s o tType sE eL m
          => [s] -> s -> ProofGenTStd tType r s o m (s,[Int])
fakePropM deps s = standardRuleM (fakeProp deps s)


fakeConstM :: HelperConstraints r s o tType sE eL m
          => o -> tType -> ProofGenTStd tType  r s o m ()
fakeConstM name tType = do
     monadifyProofStd (fakeConst name tType)
     return ()