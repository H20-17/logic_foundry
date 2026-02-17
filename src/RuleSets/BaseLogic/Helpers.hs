{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}


module RuleSets.BaseLogic.Helpers
(
    remarkM, 
    fakePropM, fakeConstM, repM,
    runProofBySubArgM, tagSentM, tagTermM,
    tagRawTextM
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

import Control.Monad.RWS (MonadReader(ask),MonadState(get))
import Data.Maybe ( isNothing )
import Control.Arrow (left)
import Control.Monad.Trans ( MonadTrans(lift) )
import Data.Map (Map,lookup)
import Internal.StdPattern
import Kernel
-- import qualified IndexTracker as sentence




runProofBySubArgM :: HelperConstraints r1 s o tType sE eL q t m
                 =>   ProofGenTStd tType r1 s o q t m x
                            -> ProofGenTStd tType r1 s o q t m (s,x)
runProofBySubArgM prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let constdict = fmap fst (consts state)
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContextFrames = contextFrames context <> [False]
        let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames (Just state)
        let newState = mempty

        let preambleSteps = []
        vIdx <- get
        (extraData,consequent,subproof,newSteps) 
            <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) prog vIdx
        mayMonadifyRes <- monadifyProofStd $ proofBySubArg consequent subproof
        maybe (error "No theorem returned by monadifyProofStd on subarg schema. This shouldn't happen") return mayMonadifyRes
        return (consequent, extraData)


remarkM :: HelperConstraints r s o tType sE eL q t m
          => Text -> Maybe Text -> ProofGenTStd tType r s o q t m [Int]
          
remarkM txt mayTag = do
    monadifyProofStd (remark txt mayTag)
    -- The index will be that of the last step generated.
    state <- getProofState
    context <- ask
    let stepCnt = stepCount state
    let idxPrefix = stepIdxPrefix context
    let finalIdx = idxPrefix <> [stepCnt-1]
    return finalIdx  


standardRuleM :: HelperConstraints r s o tType sE eL q t m
       => r -> ProofGenTStd tType r s o q t m s
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex






repM :: HelperConstraints r s o tType sE eL q t m
          => s -> ProofGenTStd tType r s o q t m s
repM s = standardRuleM (rep s)

fakePropM :: HelperConstraints r s o tType sE eL q t m
          => [s] -> s -> ProofGenTStd tType r s o q t m s
fakePropM deps s = standardRuleM (fakeProp deps s)


fakeConstM :: (HelperConstraints r s o tType sE eL q t m, TypeableTerm t o tType sE q)
          => o -> tType -> ProofGenTStd tType  r s o q t m t
fakeConstM name tType = do
     monadifyProofStd (fakeConst name tType)
     -- we aren't using standardRuleM, because that returns the last sentence generated, and fakeConst doesn't generate a sentence.
     -- We really should look up the index of the generated constant and return it, but for now, we'll just forget it because
     -- that methodology is going to be abandoned in favor of a more robust system of tracking generated sentences and constants.
     return (const2Term name) 

tagSentM :: HelperConstraints r s o tType sE eL q t m
          => Text -> s -> ProofGenTStd tType  r s o q t m ()
tagSentM tag sent = do
    monadifyProofStd (tagSent tag sent)
    -- There is essentially nothing to return. A tag step in a proof is a virtual step that doesn't generate or sentence
    -- or have an index for that matter. It's just a way to attach a tag to a sentence for later use in a remark. 
    --So we return unit, and the caller can choose to ignore it or return something else if they want.
    return ()

tagTermM :: HelperConstraints r s o tType sE eL q t m
          => Text -> t -> ProofGenTStd tType  r s o q t m ()
tagTermM tag term = do
    monadifyProofStd (tagTerm tag term)
    -- Similar to tagSentM, there is essentially nothing to return. A tag step in a proof is a virtual step that doesn't generate or sentence
    -- or have an index for that matter. It's just a way to attach a tag to a term for later
    -- use in a remark. So we return unit, and the caller can choose to ignore it or return something else if they want.
    return ()

tagRawTextM :: HelperConstraints r s o tType sE eL q t m
          => Text -> Text -> ProofGenTStd tType  r s o q t m ()
tagRawTextM tag text = do
    monadifyProofStd (tagRawText tag text)
    -- Similar to tagSentM, there is essentially nothing to return. A tag step in a proof is a virtual step that doesn't generate or sentence
    -- or have an index for that matter. It's just a way to attach a tag to a piece of raw text for later reference.
    -- It's a method of attaching arbitrary text to a proof that can be referred to in a remark, without having to attach it to a specific sentence or term.
    -- It serves as one method of escaping patterns (within remarks) like {%tagname%} or {@tagname@}.
    return ()