{-# LANGUAGE ConstraintKinds #-}

module RuleSets.PredLogic.Helpers
(
    uiM, eiM, reverseANegIntroM, reverseENegIntroM,eNegIntroM, aNegIntroM,
    eiHilbertM, egM,
    runProofByUGM,
    MetaRuleError(..),
    eqReflM, eqSymM, eqTransM, eqSubstM,
    extractConstsSentM,
    multiUGM, runTheoremM, runTmSilentM,multiUIM,
    eqSubstMultiM
) where


import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse,find)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map,restrictKeys )
import Control.Applicative ( Alternative((<|>)) )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import GHC.Stack.Types ( HasCallStack )
import Data.Data (Typeable)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Control.Arrow ( left )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Reader ( MonadReader(ask) )
import Control.Monad.State ( MonadState(get) )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.Maybe ( isNothing, mapMaybe )

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






standardRuleM :: HelperConstraints m s tType o t sE eL r
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex




uiM, egM :: HelperConstraints m s tType o t sE eL r
                   => t -> s -> ProofGenTStd tType r s o m (s,[Int])
uiM term sent = standardRuleM (ui term sent)
egM term sent = standardRuleM (eg term sent)



eiM :: HelperConstraints m s tType o t sE eL r
                   => s -> o -> ProofGenTStd tType r s o m (s,[Int],t)
eiM sent const = do
                   (instantiated, idx) <- standardRuleM (ei sent const)
                   return (instantiated,idx,const2Term const)



eNegIntroM, aNegIntroM, eqSymM :: HelperConstraints m s tType o t sE eL r
                   => s -> ProofGenTStd tType r s o m (s,[Int])
eNegIntroM sent = standardRuleM (eNegIntro sent)

aNegIntroM sent = standardRuleM (aNegIntro sent)

eqSymM eqSent = standardRuleM (eqSym eqSent)


eiHilbertM :: HelperConstraints m s tType o t sE eL r
                   => s -> ProofGenTStd tType r s o m (s,[Int],t)

eiHilbertM sent = do
         (instantiated, idx) <- standardRuleM (eiHilbert sent)
         let mayParse = parseExists sent
         (f,tType) <- maybe (error "parse exists failed when it should not have") return mayParse
         let hilbertObj = reverseParseQuantToHilbert f tType
         return (instantiated,idx,hilbertObj)


eqTransM :: HelperConstraints m s tType o t sE eL r
           => s -> s -> ProofGenTStd tType r s o m (s,[Int])
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
eqSubstMultiM :: HelperConstraints m s tType o t sE eL r
              => [(Int, s)]  -- ^ List of (index, equality) pairs for substitution.
              -> s           -- ^ The template sentence.
              -> ProofGenTStd tType r s o m (s, [Int])
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



eqSubstM :: HelperConstraints m s tType o t sE eL r
           => Int -> s -> s -> ProofGenTStd tType r s o m (s,[Int])
eqSubstM idx templateSent eqSent = standardRuleM (eqSubst idx templateSent eqSent)

eqReflM :: HelperConstraints m s tType o t sE eL r
          => t -> ProofGenTStd tType r s o m (s,[Int])
eqReflM term = standardRuleM (eqRefl term)


reverseANegIntroM, reverseENegIntroM :: HelperConstraints m s tType o t sE eL r
                   => s -> ProofGenTStd tType r s o m (s,[Int])





data MetaRuleError s where
   ReverseANegIntroMNotExistsNot :: s -> MetaRuleError s
   ReverseENegIntroMNotForallNot :: s -> MetaRuleError s
   EqSubstMultiNotEquality :: s -> MetaRuleError s
   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)




reverseANegIntroM existsXNotPx = do
      let mayExistsNot = parseExistsNot existsXNotPx
      (f,tType) <- maybe (throwM $ ReverseANegIntroMNotExistsNot existsXNotPx) return mayExistsNot
      
      (result_prop,idx,extra_data) <- runProofBySubArgM $ do
         (notPc,_, hObj) <- eiHilbertM existsXNotPx
         let forallXPx = reverseParseQuantToForall f tType
         (absurdity,_) <- runProofByAsmM forallXPx $ do         
            (pc,_) <- uiM hObj forallXPx
            contraFM pc
         absurdM absurdity
      return (result_prop, idx)

reverseENegIntroM forallXNotPx = do
      let mayForallNot = parseForallNot forallXNotPx
      (f,tType) <- maybe (throwM $ ReverseENegIntroMNotForallNot forallXNotPx) return mayForallNot
      
      (result_prop,idx,extra_data) <- runProofBySubArgM $ do
         let existsXPx = reverseParseQuantToExists f tType
         (absurdity,_) <- runProofByAsmM existsXPx $ do
            (pc,_,obj)<- eiHilbertM existsXPx
            (notPc,_) <- uiM obj forallXNotPx        
            contraFM pc
         absurdM absurdity
      return (result_prop, idx)






runProofByUGM :: HelperConstraints m s tType o t sE eL r1
                 =>  tType -> ProofGenTStd tType r1 s o m x
                            -> ProofGenTStd tType r1 s o m (s, [Int])
runProofByUGM tt prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let newFrVarTypStack = tt : frVarTypeStack
        let newContextFrames = contextFrames context <> [False]
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContext = PrfStdContext newFrVarTypStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState mempty mempty 1
        let preambleSteps = [PrfStdStepFreevar (length frVarTypeStack) tt]
        (extraData,generalizable,subproof, newSteps) 
                 <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) prog
        let resultSent = createForall generalizable tt (Prelude.length frVarTypeStack)
        mayMonadifyRes <- monadifyProofStd $ proofByUG resultSent subproof
        idx <- maybe (error "No theorem returned by monadifyProofStd on ug schema. This shouldn't happen") (return . snd) mayMonadifyRes       
        return (resultSent,idx)

multiUGM :: HelperConstraints m s tType o t sE eL r1 =>
    [tType] ->                             -- ^ List of types for UG variables (outermost first).
    ProofGenTStd tType r1 s o m x ->       -- ^ The core program. Its monadic return 'x' is discarded.
                                           --   It must set 'Last s' with the prop to be generalized.
    ProofGenTStd tType r1 s o m (s, [Int])  -- ^ Returns (final_generalized_prop, its_index).
multiUGM typeList programCore =
    case typeList of
        [] ->
            -- Base case: No UGs to apply.
            -- Run 'programCore'. 'REM.runProofBySubArgM' will execute it,
            -- take its 'Last s' (the proposition proven by programCore) as the consequent,
            -- wrap it in a PRF_BY_SUBARG step, and return (consequent, index_of_that_step).
            do 
               (arg_result_prop, idx, extraData) <- runProofBySubArgM programCore
               return (arg_result_prop, idx)

        (outermost_ug_var_type : remaining_ug_types) ->
            -- Recursive step:
            -- 1. Define the inner program that needs to be wrapped by the current UG.
            --    This inner program is 'multiUGM' applied to the rest of the types and the original core program.
            --    Its result will be (partially_generalized_prop, its_index_from_inner_multiUGM).
            let 
                inner_action_yielding_proven_s_idx = multiUGM remaining_ug_types programCore
            in
            -- 2. 'runProofByUGM' expects its 'prog' argument to be of type '... m x_prog'.
            --    Here, 'inner_action_yielding_proven_s_idx' is our 'prog', and its 'x_prog' is '(s, [Int])'.
            --    This is fine; 'runProofByUGM' will execute it. The 'Last s' writer state will be
            --    set to the 's' part of the result of 'inner_action_yielding_proven_s_idx'.
            --    This 's' (the partially generalized proposition) is what 'runProofByUGM' will then generalize.
            --    'runProofByUGM' itself returns (final_ug_prop, final_ug_idx), matching our required type.
            runProofByUGM outermost_ug_var_type inner_action_yielding_proven_s_idx


extractConstsSentM :: HelperConstraints m  s tType o t sE eL r1
                 =>   s
                            -> ProofGenTStd tType r1 s o m (Map o tType)

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



runTheoremM :: HelperConstraints m s tType o t sE eL r1
                 =>   TheoremSchemaMT tType r1 s o m x ->
                               ProofGenTStd tType r1 s o m (s, [Int], x)
runTheoremM (TheoremSchemaMT constDict lemmas prog) =  do
        state <- getProofState
        context <- ask
        (tm, proof, extra, newSteps) <- lift $ checkTheoremMOpen (Just (state,context)) (TheoremSchemaMT constDict lemmas prog)
        mayMonadifyRes <- monadifyProofStd (theoremSchema $ TheoremSchema constDict lemmas tm proof)
        idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (tm, idx, extra)


runTmSilentM :: HelperConstraints m s tType o t sE eL r1
                 =>   TheoremAlgSchema tType r1 s o x ->
                               ProofGenTStd tType r1 s o m (s, [Int], x)
-- runTmSilentM f (TheoremSchemaMT constDict lemmas prog) =  do
runTmSilentM (TheoremSchemaMT constDict lemmas prog) =  do
        state <- getProofState
        context <- ask
        let eitherResult = checkTheoremMOpen 
                     (Just (state,context)) 
                     (TheoremSchemaMT constDict lemmas prog)
        (tm, proof, extra, newSteps) <- either throwM return eitherResult
        mayMonadifyRes <- monadifyProofStd (theoremAlgSchema $ TheoremSchemaMT constDict lemmas newProg)
        idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (tm, idx, extra)
    where
        newProg = do
             prog
             return ()

-- | Applies Universal Instantiation (UI) multiple times to a given proposition.
-- | Returns the final instantiated proposition and its proof index.
-- | - Case 0: No instantiation terms -> re-proves the initial proposition.
-- | - Case 1: One instantiation term -> applies PREDL.uiM directly.
-- | - Case >1: Multiple terms -> creates a sub-argument for the sequen
multiUIM ::  HelperConstraints m s tType o t sE eL r1 =>
    s ->      -- initialProposition: The proposition to start with.
    [t] ->    -- instantiationTerms: List of terms to instantiate with, in order.
    ProofGenTStd tType r1 s o m (s,[Int])
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