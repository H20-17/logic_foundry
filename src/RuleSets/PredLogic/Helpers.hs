{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module RuleSets.PredLogic.Helpers
(
    uiM, eiM, reverseANegIntroM, reverseENegIntroM,eNegIntroM, aNegIntroM,
    eiHilbertM, egM,
    MetaRuleError(..),
    eqReflM, eqSymM, eqTransM, eqSubstM,
    extractConstsSentM,
    runTheoremM, runTmSilentM,multiUIM,
    eqSubstMultiM,
    getXVar, getXVars,
    aXM, multiAXM, eXM, multiEXM, hXM,
    runProofByUGM, multiUGM,
    createTermTmplt,
    lambdaTerm,
    lambdaSent,
    lambdaTermMulti,
    lambdaSentMulti,
    lambdaTermMultiM,
    testTheoremM,
    checkTheoremM,
    checkSilentTheoremM,
    testSilentTheoremM,
    testTheoremMBasic,
    testSilentTheoremMBasic
) where


import Data.Monoid ( Last(..) ,Sum (..))

import Control.Monad ( foldM, unless )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse,find)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import qualified Data.Text as T
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map,restrictKeys )
import Control.Applicative ( Alternative((<|>)) )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import GHC.Stack.Types ( HasCallStack )
import Data.Data (Typeable, Proxy (Proxy))
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Control.Arrow ( left )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Reader ( MonadReader(ask) )
import Control.Monad.State ( MonadState(get),gets )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.Maybe ( isNothing, mapMaybe )
import qualified Data.Vector.Fixed as V
import Control.Monad.IO.Class(MonadIO,liftIO)
import Control.Monad.Trans.Maybe ( MaybeT(MaybeT, runMaybeT) )
import Kernel
import Internal.StdPattern

import RuleSets.BaseLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   HelperConstraints(..))
import qualified RuleSets.BaseLogic.Core as REM

import RuleSets.PropLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   LogicSent,
   SubproofMException(..),
   MetaRuleError(..),
   HelperConstraints())
import qualified RuleSets.PropLogic.Core as PL
import qualified RuleSets.BaseLogic.Core as BASE
import RuleSets.BaseLogic.Helpers
import RuleSets.PropLogic.Helpers hiding
   (MetaRuleError(..))
import RuleSets.PredLogic.Core
import IndexTracker
import qualified Data.Text.Read as TR
import Data.Char (isDigit)





standardRuleM :: HelperConstraints m s tType o t sE eL r q
       => r -> ProofGenTStd tType r s o q t m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex




uiM, egM :: HelperConstraints m s tType o t sE eL r q
                   => t -> s -> ProofGenTStd tType r s o q t m (s,[Int])
uiM term sent = standardRuleM (ui term sent)
egM term sent = standardRuleM (eg term sent)



eiM :: HelperConstraints m s tType o t sE eL r q
                   => s -> o -> ProofGenTStd tType r s o q t m (s,[Int],t)
eiM sent const = do
                   (instantiated, idx) <- standardRuleM (ei sent const)
                   return (instantiated,idx,const2Term const)



eNegIntroM, aNegIntroM, eqSymM :: HelperConstraints m s tType o t sE eL r q
                   => s -> ProofGenTStd tType r s o q t m (s,[Int])
eNegIntroM sent = standardRuleM (eNegIntro sent)

aNegIntroM sent = standardRuleM (aNegIntro sent)

eqSymM eqSent = standardRuleM (eqSym eqSent)


eiHilbertM :: HelperConstraints m s tType o t sE eL r q
                   => s -> ProofGenTStd tType r s o q t m (s,[Int],t)

eiHilbertM sent = do
         (instantiated, idx) <- standardRuleM (eiHilbert sent)
         let mayParse = parseExists sent
         (f,tType) <- maybe (error "parse exists failed when it should not have") return mayParse
         let hilbertObj = reverseParseQuantToHilbert f tType
         return (instantiated,idx,hilbertObj)


eqTransM :: HelperConstraints m s tType o t sE eL r q
           => s -> s -> ProofGenTStd tType r s o q t m (s,[Int])
eqTransM eqSent1 eqSent2 = standardRuleM (eqTrans eqSent1 eqSent2)

-- | Given a template sentence and a list of equalities, this function iteratively
-- | applies equality substitution for each template variable. It assumes that the
-- | template, when fully substituted with the LEFT-hand side of each equality,
-- | is already a proven proposition in the context.
-- |
-- | The function works by folding over the list of substitutions. In each step,
-- | it constructs a new template where variables before the current one are
-- | substituted with their RIGHT-hand sides, and variables after are substituted
-- | with their LEFT-hand sides. It then uses `eqSubstM` to perform the substitution
-- | for the current variable.
eqSubstMultiM :: HelperConstraints m s tType o t sE eL r q
              => [(Int, s)]  -- ^ List of (index, equality) pairs for substitution.
              -> s           -- ^ The template sentence.
              -> ProofGenTStd tType r s o q t m (s, [Int])
eqSubstMultiM substitutions templateSent = do
    -- This function requires parsers for the left and right sides of an equality.
    -- We'll assume a `parseEq :: s -> Maybe (t, t)` function exists in the environment.
    let parseEqLS s = fst <$> parseEq s
    let parseEqRS s = snd <$> parseEq s

    -- Helper to parse a list of sentences and throw a specific error on failure.
    let parseAllOrThrow parser sentences =
            let parsed_results = zip sentences (Prelude.map parser sentences)
            in case find (isNothing . snd) parsed_results of
                Just (failed_s, Nothing) -> throwM (EqSubstMultiNotEquality failed_s)
                Nothing -> return $ mapMaybe snd parsed_results

    -- Extract all the left-hand-side terms from the equalities.
    lhs_terms <- parseAllOrThrow parseEqLS (Prelude.map snd substitutions)

    -- The initial premise that must be proven is the template with all variables
    -- substituted by the left-hand side of their respective equalities.
    let initial_premise = sentSubXs (zip (Prelude.map fst substitutions) lhs_terms) templateSent

    -- Wrap the argument in a subproof

    (substituted,idx,_) <- runProofBySubArgM $ do
        -- We use `repM` to assert that this initial premise is already proven in the context.
        -- This is the starting point for our chain of substitutions.
        initial_proof_data <- repM initial_premise

        -- We will now iteratively substitute each variable. We use a fold, where the
        -- accumulator is the proof data of the increasingly-substituted proposition.
        let indexed_substitutions = zip [0..] substitutions

        foldM
            (\proven_prop_acc (i, (idx_to_subst, eq_to_use)) -> do
                -- For the i-th substitution, construct a new template where variables
                -- before index `i` are substituted with their RIGHT-hand sides, and
                -- variables after index `i` are substituted with their LEFT-hand sides.
                let subs_before = take i substitutions
                let subs_after = drop (i + 1) substitutions

                rhs_before <- parseAllOrThrow parseEqRS (Prelude.map snd subs_before)
                lhs_after  <- parseAllOrThrow parseEqLS (Prelude.map snd subs_after)
            
                -- Create the substitution list for building the partial template.
                let partial_subs = zip (Prelude.map fst subs_before) rhs_before ++ zip (Prelude.map fst subs_after) lhs_after

                -- Construct the partial template for this step.
                let partial_template = sentSubXs partial_subs templateSent

                -- Apply the core eqSubstM rule. The `proven_prop_acc` from the previous
                -- step of the fold serves as the required premise for this rule.
                eqSubstM idx_to_subst partial_template eq_to_use
            ) 
            initial_proof_data
            indexed_substitutions
    return (substituted,idx)



eqSubstM :: HelperConstraints m s tType o t sE eL r q
           => Int -> s -> s -> ProofGenTStd tType r s o q t m (s,[Int])
eqSubstM idx templateSent eqSent = standardRuleM (eqSubst idx templateSent eqSent)

eqReflM :: HelperConstraints m s tType o t sE eL r q
          => t -> ProofGenTStd tType r s o q t m (s,[Int])
eqReflM term = standardRuleM (eqRefl term)


reverseANegIntroM, reverseENegIntroM :: HelperConstraints m s tType o t sE eL r q
                   => s -> ProofGenTStd tType r s o q t m (s,[Int])





data MetaRuleError s where
   ReverseANegIntroMNotExistsNot :: s -> MetaRuleError s
   ReverseENegIntroMNotForallNot :: s -> MetaRuleError s
   EqSubstMultiNotEquality :: s -> MetaRuleError s
   TheoremTargetMismatch :: s -> s -> MetaRuleError s
   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)




reverseANegIntroM existsXNotPx = do
      let mayExistsNot = parseExistsNot existsXNotPx
      (f,tType) <- maybe (throwM $ ReverseANegIntroMNotExistsNot existsXNotPx) return mayExistsNot
      
      (result_prop,idx,extra_data) <- runProofBySubArgM $ do
         (notPc,_, hObj) <- eiHilbertM existsXNotPx
         let forallXPx = reverseParseQuantToForall f tType
         (absurdity,_,_) <- runProofByAsmM forallXPx $ do         
            (pc,_) <- uiM hObj forallXPx
            contraFM pc
         absurdM absurdity
      return (result_prop, idx)

reverseENegIntroM forallXNotPx = do
      let mayForallNot = parseForallNot forallXNotPx
      (f,tType) <- maybe (throwM $ ReverseENegIntroMNotForallNot forallXNotPx) return mayForallNot
      
      (result_prop,idx,extra_data) <- runProofBySubArgM $ do
         let existsXPx = reverseParseQuantToExists f tType
         (absurdity,_,_) <- runProofByAsmM existsXPx $ do
            (pc,_,obj)<- eiHilbertM existsXPx
            (notPc,_) <- uiM obj forallXNotPx        
            contraFM pc
         absurdM absurdity
      return (result_prop, idx)










extractConstsSentM :: HelperConstraints m  s tType o t sE eL r1 q
                 =>   s
                            -> ProofGenTStd tType r1 s o q t m (Map o tType)

extractConstsSentM sentence = do
    state <- getProofState
    let constdict = fmap fst (consts state)
    let sentConsts = extractConstsSent sentence     
    return $ Data.Map.restrictKeys constdict sentConsts










constDictTest :: (Ord o, Eq tType) => Map o tType -> Map o tType ->  Maybe (o, Maybe (tType,tType))
constDictTest envDict = Data.Map.foldrWithKey f Nothing
     where         
         f k aVal Nothing = case Data.Map.lookup k envDict of
                                              Just bVal -> if 
                                                              aVal /= bVal 
                                                           then
                                                              Just (k,Just (aVal,bVal))
                                                           else
                                                               Nothing -- we good
                                              Nothing -> Just (k,Nothing)
         f k aVal (Just x) = Just x



runTheoremM :: HelperConstraints m s tType o t sE eL r1 q
                 =>   TheoremSchemaMT tType r1 s o q t m x ->
                               ProofGenTStd tType r1 s o q t m (s, [Int], x)
runTheoremM (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes) =  do
        state <- getProofState
        context <- ask
        (tm, extra, other,_) <- lift $ checkTheoremMOpen (Just (state,context)) True (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes)
        case other of
            Left (proof,newSteps) -> do
                mayMonadifyRes <- monadifyProofStd (theoremSchema $ TheoremSchema constDict lemmas tm proof)
                idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
                return (tm, idx, extra)
            Right idxs -> do
                (_,idx) <- repM tm
                return (tm,idx,extra)


checkTheoremM :: (HelperConstraints m s tType o t sE eL r1 q)
                 =>  TheoremSchemaMT tType r1 s o q t m x
                              -> m (s, r1, x, [PrfStdStep s o tType t],Maybe (s,x))
checkTheoremM (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes) = do
                    (provenSent, extraData, other,mayTargetTmData) <- checkTheoremMOpen Nothing False (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes)
                    (prf,steps) <- either return (error "checkTHeoremMOpen produced unexpected Right value in checkTheoremM function") other

                    return (provenSent, prf, extraData, steps, mayTargetTmData)



checkSilentTheoremM :: (HelperConstraints (Either SomeException) s tType o t sE eL r1 q, Monad m, MonadThrow m)
                 =>  TheoremAlgSchema tType r1 s o q t x
                              -> m (s, x, Maybe (s,x) )
checkSilentTheoremM (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes) = do
        let eitherResult = checkTheoremMOpen Nothing False (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes)     
        (tm,extra,other,mayTargetTmData) <- either throwM return eitherResult
        either return (error "checkTHeoremMOpen produced unexpected Right value in checkSilentTheoremM function") other
        return (tm, extra, mayTargetTmData)



runTmSilentM :: HelperConstraints m s tType o t sE eL r1 q
                 =>   TheoremAlgSchema tType r1 s o q t x ->
                               ProofGenTStd tType r1 s o q t m (s, [Int], x)
-- runTmSilentM f (TheoremSchemaMT constDict lemmas prog) =  do
runTmSilentM (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes) =  do
        state <- getProofState
        context <- ask
        let eitherResult = checkTheoremMOpen (Just (state,context)) True (TheoremSchemaMT mayTargetM constDict lemmas prog idxs qTypes)
        (tm,extra,other,_) <- either throwM return eitherResult
        case other of
            Left (proof,newSteps) -> do
                mayMonadifyRes <- monadifyProofStd (theoremSchema $ TheoremSchema constDict lemmas tm proof)
                idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
                return (tm, idx, extra)
            Right idxs -> do
                (_,idx) <- repM tm
                return (tm,idx,extra)

                   
-- | Applies Universal Instantiation (UI) multiple times to a given proposition.
-- | Returns the final instantiated proposition and its proof index.
-- | - Case 0: No instantiation terms -> re-proves the initial proposition.
-- | - Case 1: One instantiation term -> applies PREDL.uiM directly.
-- | - Case >1: Multiple terms -> creates a sub-argument for the sequen
multiUIM ::  HelperConstraints m s tType o t sE eL r1 q =>
    s ->      -- initialProposition: The proposition to start with.
    [t] ->    -- instantiationTerms: List of terms to instantiate with, in order.
    ProofGenTStd tType r1 s o q t m (s,[Int])
multiUIM initialProposition instantiationTerms =
    case instantiationTerms of
        [] ->
            -- Case 0: No terms to instantiate with.
            -- Re-prove the initial proposition to ensure it's the active "last proven statement"
            -- and to get its index in the current context.
            repM initialProposition

        [singleTerm] ->
            -- Case 1: Exactly one term to instantiate with.
            -- Apply PREDL.uiM directly. No need for a sub-argument wrapper.
            uiM singleTerm initialProposition

        _ -> -- More than one term (list has at least two elements here)
            -- Case 2: Multiple instantiation terms.
            -- Create a sub-argument whose internal proof is the sequence of UI steps.
            do
                (result_prop, idx, extra_data) <- runProofBySubArgM (
                    -- Use foldM to iteratively apply PREDL.uiM.
                    -- The accumulator for foldM is (current_proposition_term, its_index).
                    foldM
                        (\(currentProp_term, _currentProp_idx) term_to_instantiate ->
                            -- PREDL.uiM applies UI, proves the new proposition, adds it to proof steps,
                            -- updates the Last s writer state, and returns (new_proposition_term, new_index).
                            -- This (new_prop, new_idx) becomes the new accumulator.
                            uiM term_to_instantiate currentProp_term
                        )
                        (initialProposition, []) -- Start fold with initialProposition and a dummy index.
                        instantiationTerms
                    -- The result of this foldM is a monadic action of type m (PropDeBr, [Int]).
                    -- This is the 'prog' for runProofBySubArgM.
                    -- Its 'Last s' writer state (set by the last PREDL.uiM) will be used
                    -- by runProofBySubArgM as the 'consequent' of the sub-argument.
                    )
                return (result_prop, idx)


getXVar :: MonadSent s t tType o q sE m => m t
getXVar = do
    topIdx <- getSum <$> get
    return $ x (topIdx - 1)
    --       gets (x . (\x -> x - 1) . getSum)

getXVars :: MonadSent s t tType o q sE m => Int -> m [t]
getXVars n = do
    topIdx <- getSum <$> get
    return [x (topIdx - i - 1) | i <- [0..(n-1)]]

-- n starts out as 2 and ..... we have added to things to the stack... stack started out as 0, now is 2....
-- i draws frp, [0..1].......... sp we get x (2-0-1) which is x 1, and we get x (2-1-1) which is x 0


aXM :: MonadSent s t tType o q sE m => q -> m s -> m s
aXM quantType inner = do
    x_idx <- newIndex
    innerSent <-inner
    let returnSent = aX quantType x_idx innerSent
    dropIndices 1
    return returnSent

multiAXM :: MonadSent s t tType o q sE m => [q] -> m s -> m s
-- | Applies the universal quantifier ('∀') `quantDepth` times to the result
-- | of the inner monadic action.
multiAXM quantTypes inner =
    case quantTypes of
        [] -> inner
        [singleType] -> aXM singleType inner
        (firstType:restTypes) -> aXM firstType (multiAXM restTypes inner)

eXM :: MonadSent s t tType o q sE m => q -> m s -> m s
eXM quantType inner = do
    x_idx <- newIndex
    innerSent <-inner
    let returnSent = eX quantType x_idx innerSent
    dropIndices 1
    return returnSent


hXM :: MonadSent s t tType o q sE m => q -> m s -> m t
hXM quantType inner = do
    x_idx <- newIndex
    innerSent <-inner
    let returnTerm = hX quantType x_idx innerSent
    dropIndices 1
    return returnTerm



-- | Applies the existential quantifier ('∃') `quantDepth` times to the result
-- | of the inner monadic action.
multiEXM :: MonadSent s t tType o q sE m => [q] -> m s -> m s
multiEXM quantTypes inner = case quantTypes of
    [] -> inner
    [singleType] -> eXM singleType inner
    (firstType:restTypes) -> eXM firstType (multiEXM restTypes inner)



--runProofByUGM :: HelperConstraints m s tType o t sE eL r1 q
--                 =>  q -> ProofGenTStd tType r1 s o q m x
--                            -> ProofGenTStd tType r1 s o q m (s, [Int])
--runProofByUGM tt prog =  do
--   (result_prop, idx, _) <- runProofByUGMWorker tt prog
--   return (result_prop, idx)


-- multiUGM :: HelperConstraints m s tType o t sE eL r1 q =>
--    [q] ->                             -- ^ List of types for UG variables (outermost first).
--    ProofGenTStd tType r1 s o q m x ->       -- ^ The core program. Its monadic return 'x' is discarded.
--                                           --   It must set 'Last s' with the prop to be generalized.
--    ProofGenTStd tType r1 s o q m (s, [Int])  -- ^ Returns (final_generalized_prop, its_index).
--multiUGM typeList programCore = do
--      (result_prop, idx, _) <- multiUGMWorker typeList programCore
--      return (result_prop, idx)





runProofByUGM :: HelperConstraints m s tType o t sE eL r1 q
                 =>  q -> ProofGenTStd tType r1 s o q t m t
                            -> ProofGenTStd tType r1 s o q t m (s, [Int], t-> t)
runProofByUGM tt prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let newFrVarTypStack = tt : frVarTypeStack
        let newContextFrames = contextFrames context <> [False]
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContext = PrfStdContext newFrVarTypStack newStepIdxPrefix newContextFrames (Just state)
        let newState = PrfStdState {
            provenSents = mempty,
            consts = mempty,
            stepCount = 1,
            tagData = mempty,
            remarkTagIdxs = mempty
        }
        let preambleSteps = [PrfStdStepFreevar (length frVarTypeStack) (qTypeToTType tt)]
        let modifiedProg = do
            progData <- prog
            -- txt <- showTermM progData
            -- remarkM $ "Data returned from program: " <> txt
            topFreeVar <- getTopFreeVar
            newIdx <- newIndex
            -- remarkM $ "new index for ug variable: " <> pack (show newIdx)
            let dataFuncTmplt = createTermTmplt [(topFreeVar, newIdx)] progData
            
            -- txt <- showTermM dataFuncTmplt
            -- remarkM $ "Creating universal generalization function: " <> txt
            let returnFunc = lambdaTerm newIdx dataFuncTmplt
            dropIndices 1
            return returnFunc
        vIdx <- get
        (extraData,generalizable,subproof, newSteps) 
                 <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) modifiedProg vIdx
        let resultSent = createForall tt (Prelude.length frVarTypeStack) generalizable
        mayMonadifyRes <- monadifyProofStd $ proofByUG resultSent subproof
        idx <- maybe (error "No theorem returned by monadifyProofStd on ug schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (resultSent,idx, extraData)






multiUGM :: HelperConstraints m s tType o t sE eL r1 q =>
    [q] ->                             -- ^ List of types for UG variables (outermost first).
    ProofGenTStd tType r1 s o q t m t ->       -- ^ The core program. Its monadic return 'x' is discarded.
                                           --   It must set 'Last s' with the prop to be generalized.
    ProofGenTStd tType r1 s o q t m (s, [Int],[t]->t)  -- ^ Returns (final_generalized_prop, its_index).
multiUGM typeList programCore =
    case typeList of
        [] ->
            -- Edge case: No UGs to apply.
            -- Run 'programCore'. 'REM.runProofBySubArgM' will execute it,
            -- take its 'Last s' (the proposition proven by programCore) as the consequent,
            -- wrap it in a PRF_BY_SUBARG step, and return (consequent, index_of_that_step).
            do 
               (arg_result_prop, idx, extraData) <- runProofBySubArgM programCore
               return (arg_result_prop, idx,const extraData)
        [single_ug_var_type] -> -- Base case: RunproofbyUG<.
            -- Run 'programCore'. 'REM.runProofBySubArgM' will execute it,
            -- take its 'Last s' (the proposition proven by programCore) as the consequent,
            -- wrap it in a PRF_BY_SUBARG step, and return (consequent, index_of_that_step).
            do 
               (arg_result_prop, idx, dataFunc) <- runProofByUGM single_ug_var_type programCore
               let returnFunc args = dataFunc (head args)
               return (arg_result_prop, idx,returnFunc)
        (outermost_ug_var_type : penultimate_ug_var_type : remaining_ug_types) ->
            do
                newIdxs <- newIndices (length typeList)
                (s,idx,template_f) <- runProofByUGM outermost_ug_var_type $ do
                    (_,_,dataFunc) <- multiUGM (penultimate_ug_var_type : remaining_ug_types) programCore
                    let newXs = Prelude.map x newIdxs
                    let dataFuncTmplt = dataFunc newXs
                    return dataFuncTmplt
                newIndex <- newIndex
                let newTmplt = template_f (x newIndex)
                let returnFunc = lambdaTermMultiNew (newIndex:newIdxs) newTmplt
                dropIndices 1
                dropIndices (length typeList -1)
                return (s,idx,returnFunc)


createTermTmplt :: SentConstraints s t tType o q sE => 
        [(t,Int)] -> t -> t
createTermTmplt subs originTerm = 
    let
        accumFunc (targetTerm,idx) accumTerm =
            termSwapForX targetTerm idx accumTerm
    in foldr accumFunc originTerm subs
               

lambdaTermMulti :: (SentConstraints s t tType o q sE, V.Vector v Int,  V.Vector v t) => 
    v Int -> t -> v t -> t
lambdaTermMulti target_idxs template replacements = 
    let
        subs = zip (V.toList target_idxs) (V.toList replacements)
    in
        termSubXs subs template


lambdaTermMultiNew :: (SentConstraints s t tType o q sE) => 
    [Int] -> t -> [t] -> t
lambdaTermMultiNew target_idxs template replacements = 
    let
        subs = zip target_idxs replacements
    in
        termSubXs subs template



lambdaTerm :: SentConstraints s t tType o q sE => 
    Int -> t -> t -> t
lambdaTerm target_idx template replacement = 
    termSubX target_idx replacement template


lambdaTermMultiM :: (MonadSent s t tType o q sE m, V.Vector v t) =>
    v t -> t ->  m (v t -> t)
lambdaTermMultiM (targetTerms::v t) sourceTerm = do
    let param_n = V.length (undefined :: v t)
    templateIdxs <- newIndices param_n
    let subs = zip (V.toList targetTerms) templateIdxs
    let lambdaTemplate = createTermTmplt subs sourceTerm
    let returnFunc argVec =
          let
              args = V.toList argVec
              subs = zip templateIdxs args
          in
              termSubXs subs lambdaTemplate
    dropIndices param_n
    return returnFunc 






lambdaSentMulti :: (SentConstraints s t tType o q sE,V.Vector v Int,  V.Vector v t) => 
    v Int -> s -> v t -> s
lambdaSentMulti target_idxs template replacements = 
    let
        subs = zip (V.toList target_idxs) (V.toList replacements)
    in
        sentSubXs subs template


lambdaSentMultiNew :: (SentConstraints s t tType o q sE,V.Vector v t) => 
    [Int] -> s -> v t -> s
lambdaSentMultiNew target_idxs template replacements = 
    let
        subs = zip target_idxs (V.toList replacements)
    in
        sentSubXs subs template


lambdaSent :: SentConstraints s t tType o q sE => 
    Int -> s -> t -> s
lambdaSent target_idx template replacement = 
    sentSubX target_idx replacement template





extractConstsFromLambdaTerm :: (SentConstraints s t tType o q sE,V.Vector v t) =>
    (v t -> t) -> Set o
extractConstsFromLambdaTerm (term_f::v t -> t) = 
    runIndexTracker $ do
        let paramCount = V.length (undefined :: v t)
        indices <- newIndices paramCount
        let paramVars = V.fromList $ Prelude.map x indices
        let term_tmplt = term_f paramVars
        dropIndices paramCount
        return $ extractConstsTerm term_tmplt

extractConstsFromLambdaSent :: (SentConstraints s t tType o q sE, V.Vector v t) =>
    (v t -> s) -> Set o
extractConstsFromLambdaSent (term_f::v t -> s) = 
    runIndexTracker $ do
        let paramCount = V.length (undefined :: v t)
        indices <- newIndices paramCount
        let paramVars = V.fromList $ Prelude.map x indices
        let term_tmplt = term_f paramVars
        let result = extractConstsSent term_tmplt
        dropIndices paramCount
        return result


testTheoremM :: (HelperConstraints m s tType o t sE eL r1 q, MonadIO m)
                 =>  TheoremSchemaMT tType r1 s o q t m x
                              -> (x -> m ())
                              -> (x -> x -> m ())
                              -> m ()
testTheoremM schema dataShow dataCompare = do
    liftIO $ putStrLn "LIVE THEOREM GENENERATOR OUTPUT"
    liftIO $ putStrLn "-------------------"
    (provenSent, proof, returnData, proofSteps, mayTargetTmData) <- checkTheoremM schema
    liftIO $ putStrLn ""
    liftIO $ putStrLn "POST HOC THEOREM GENERATOR OUTPUT"
    liftIO $ putStrLn "-----------------------"
    printStepsFull proofSteps
    liftIO $ putStrLn ""
    case mayTargetTmData of
        Nothing -> do
            liftIO $ putStrLn $ "Proven theorem: " <> show provenSent
            dataShow returnData
            -- Sometimes the data can take the form of function, so we can't just show it here directly.
            -- If the data is an unshowable function,
            -- then the dataShow function should probably show an example or two of the function in action.
        Just (targetSent,targetData) -> do
            liftIO $ putStrLn "THEOREM TARGET MATCH CHECK"
            liftIO $ putStrLn "-------------------"
            liftIO $ putStrLn $ "Proven theorem: " <> show provenSent
            liftIO $ putStrLn $ "Target theorem: " <> show targetSent
            let sentTestResult = if targetSent == provenSent then "PASSED" else "FAILED"
            liftIO $ putStrLn $ "Target theorem matches proven theorem: " <> sentTestResult
            liftIO $ putStrLn ""
            liftIO $ putStrLn "THEOREM DATA TARGET MATCH CHECK(S)"
            liftIO $ putStrLn "-------------------"
            dataCompare returnData targetData
            -- This test should print whatever info it wants about the data test,
            -- The output should include PASS/FAIL info.
            -- The test could incorporate multiple checks if needed.
            -- Sometimes that data can take the form of functions, so we can't just do an equality check here.
            liftIO $ putStrLn ""
    return ()   


testTheoremMBasic :: (HelperConstraints m s tType o t sE eL r1 q, MonadIO m, Show x, Eq x)
                 =>  TheoremSchemaMT tType r1 s o q t m x
                              -> m ()
testTheoremMBasic schema = do
    let dataShow d = liftIO $ putStrLn $ "Returned data: " <> show d
    let dataCompare d1 d2 = do
            liftIO $ putStrLn $ "Returned data: " <> show d1
            liftIO $ putStrLn $ "Target data: " <> show d2
            let dataCompareResult = if d1 == d2 
                                  then "PASSED"
                                  else "FAILED"
            liftIO $ putStrLn $ "Target data matches returned data: " <> dataCompareResult
    testTheoremM schema dataShow dataCompare





 




testSilentTheoremM :: (HelperConstraints (Either SomeException) s tType o t sE eL r1 q, MonadIO m, MonadThrow m)
                 =>  TheoremAlgSchema tType r1 s o q t x -> 
                            (x -> m ()) -> 
                            (x -> x -> m ()) ->
                              m ()
testSilentTheoremM schema dataShow dataCompare = do
    (provenSent, returnData, mayTargetTmData) <- checkSilentTheoremM schema
    case mayTargetTmData of
        Nothing -> do
            liftIO $ putStrLn $ "Proven theorem: " <> show provenSent
            dataShow returnData
            -- Sometimes the data can take the form of functions, so we can't just show it here directly.
            -- If the data is an unshowable function,
            -- then the dataShow function should probably show an example or two of the function in action.
        Just (targetSent,targetData) -> do
            liftIO $ putStrLn "THEOREM TARGET MATCH CHECK"
            liftIO $ putStrLn "-------------------"
            liftIO $ putStrLn $ "Proven theorem: " <> show provenSent
            liftIO $ putStrLn $ "Target theorem: " <> show targetSent
            let sentTestResult = if targetSent == provenSent then "PASSED" else "FAILED"
            liftIO $ putStrLn $ "Target theorem matches proven theorem: " <> sentTestResult
            liftIO $ putStrLn ""
            liftIO $ putStrLn "THEOREM DATA TARGET MATCH CHECK(S)"
            liftIO $ putStrLn "-------------------"
            dataCompare returnData targetData
            -- This test should print whatever info it wants about the data test,
            -- The output should include PASS/FAIL info.
            -- The test could incorporate multiple checks if needed.
            -- Sometimes that data can take the form of functions, so we can't just do an equality check here.
            liftIO $ putStrLn ""
    return ()

testSilentTheoremMBasic :: (HelperConstraints (Either SomeException) s tType o t sE eL r1 q, MonadIO m, MonadThrow m, Show x, Eq x)
                 =>  TheoremAlgSchema tType r1 s o q t x 
                              -> m ()
testSilentTheoremMBasic schema = do
    let dataShow d = liftIO $ putStrLn $ "Returned data: " <> show d
    let dataCompare d1 d2 = do
            liftIO $ putStrLn $ "Returned data: " <> show d1
            liftIO $ putStrLn $ "Target data: " <> show d2
            let dataCompareResult = if d1 == d2 
                                  then "PASSED"
                                  else "FAILED"
            liftIO $ putStrLn $ "Target data matches returned data: " <> dataCompareResult
    testSilentTheoremM schema dataShow dataCompare

    return ()