{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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
    lambdaSentMulti
) where


import Data.Monoid ( Last(..) ,Sum (..))

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
import Control.Monad.State ( MonadState(get),gets )
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
import IndexTracker







standardRuleM :: HelperConstraints m s tType o t sE eL r q
       => r -> ProofGenTStd tType r s o q m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex




uiM, egM :: HelperConstraints m s tType o t sE eL r q
                   => t -> s -> ProofGenTStd tType r s o q m (s,[Int])
uiM term sent = standardRuleM (ui term sent)
egM term sent = standardRuleM (eg term sent)



eiM :: HelperConstraints m s tType o t sE eL r q
                   => s -> o -> ProofGenTStd tType r s o q m (s,[Int],t)
eiM sent const = do
                   (instantiated, idx) <- standardRuleM (ei sent const)
                   return (instantiated,idx,const2Term const)



eNegIntroM, aNegIntroM, eqSymM :: HelperConstraints m s tType o t sE eL r q
                   => s -> ProofGenTStd tType r s o q m (s,[Int])
eNegIntroM sent = standardRuleM (eNegIntro sent)

aNegIntroM sent = standardRuleM (aNegIntro sent)

eqSymM eqSent = standardRuleM (eqSym eqSent)


eiHilbertM :: HelperConstraints m s tType o t sE eL r q
                   => s -> ProofGenTStd tType r s o q m (s,[Int],t)

eiHilbertM sent = do
         (instantiated, idx) <- standardRuleM (eiHilbert sent)
         let mayParse = parseExists sent
         (f,tType) <- maybe (error "parse exists failed when it should not have") return mayParse
         let hilbertObj = reverseParseQuantToHilbert f tType
         return (instantiated,idx,hilbertObj)


eqTransM :: HelperConstraints m s tType o t sE eL r q
           => s -> s -> ProofGenTStd tType r s o q m (s,[Int])
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
              -> ProofGenTStd tType r s o q m (s, [Int])
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
           => Int -> s -> s -> ProofGenTStd tType r s o q m (s,[Int])
eqSubstM idx templateSent eqSent = standardRuleM (eqSubst idx templateSent eqSent)

eqReflM :: HelperConstraints m s tType o t sE eL r q
          => t -> ProofGenTStd tType r s o q m (s,[Int])
eqReflM term = standardRuleM (eqRefl term)


reverseANegIntroM, reverseENegIntroM :: HelperConstraints m s tType o t sE eL r q
                   => s -> ProofGenTStd tType r s o q m (s,[Int])





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









extractConstsSentM :: HelperConstraints m  s tType o t sE eL r1 q
                 =>   s
                            -> ProofGenTStd tType r1 s o q m (Map o tType)

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
                 =>   TheoremSchemaMT tType r1 s o q m x ->
                               ProofGenTStd tType r1 s o q m (s, [Int], x)
runTheoremM (TheoremSchemaMT constDict lemmas prog idxs qTypes) =  do
        state <- getProofState
        context <- ask
        (tm, proof, extra, newSteps) <- lift $ checkTheoremMOpen (Just (state,context)) (TheoremSchemaMT constDict lemmas prog idxs qTypes)
        mayMonadifyRes <- monadifyProofStd (theoremSchema $ TheoremSchema constDict lemmas tm proof)
        idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (tm, idx, extra)


runTmSilentM :: HelperConstraints m s tType o t sE eL r1 q
                 =>   TheoremAlgSchema tType r1 s o q x ->
                               ProofGenTStd tType r1 s o q m (s, [Int], x)
-- runTmSilentM f (TheoremSchemaMT constDict lemmas prog) =  do
runTmSilentM (TheoremSchemaMT constDict lemmas prog idxs qTypes) =  do
        state <- getProofState
        context <- ask
        let eitherResult = checkTheoremMOpen 
                     (Just (state,context)) 
                     (TheoremSchemaMT constDict lemmas prog idxs qTypes)
        (tm, proof, extra, newSteps) <- either throwM return eitherResult
        mayMonadifyRes <- monadifyProofStd (theoremAlgSchema $ TheoremSchemaMT constDict lemmas newProg idxs qTypes)
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
multiUIM ::  HelperConstraints m s tType o t sE eL r1 q =>
    s ->      -- initialProposition: The proposition to start with.
    [t] ->    -- instantiationTerms: List of terms to instantiate with, in order.
    ProofGenTStd tType r1 s o q m (s,[Int])
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


getXVar :: MonadSent s t tType o q m => m t
getXVar = do
    topIdx <- getSum <$> get
    return $ x (topIdx - 1)
    --       gets (x . (\x -> x - 1) . getSum)

getXVars :: MonadSent s t tType o q m => Int -> m [t]
getXVars n = do
    topIdx <- getSum <$> get
    return [x (topIdx - i - 1) | i <- [0..(n-1)]]

-- n starts out as 2 and ..... we have added to things to the stack... stack started out as 0, now is 2....
-- i draws frp, [0..1].......... sp we get x (2-0-1) which is x 1, and we get x (2-1-1) which is x 0


aXM :: MonadSent s t tType o q m => q -> m s -> m s
aXM quantType inner = do
    x_idx <- newIndex
    innerSent <-inner
    let returnSent = aX quantType x_idx innerSent
    dropIndices 1
    return returnSent

multiAXM :: MonadSent s t tType o q m => [q] -> m s -> m s
-- | Applies the universal quantifier ('∀') `quantDepth` times to the result
-- | of the inner monadic action.
multiAXM quantTypes inner =
    case quantTypes of
        [] -> inner
        [singleType] -> aXM singleType inner
        (firstType:restTypes) -> aXM firstType (multiAXM restTypes inner)

eXM :: MonadSent s t tType o q m => q -> m s -> m s
eXM quantType inner = do
    x_idx <- newIndex
    innerSent <-inner
    let returnSent = eX quantType x_idx innerSent
    dropIndices 1
    return returnSent


hXM :: MonadSent s t tType o q m => q -> m s -> m t
hXM quantType inner = do
    x_idx <- newIndex
    innerSent <-inner
    let returnTerm = hX quantType x_idx innerSent
    dropIndices 1
    return returnTerm



-- | Applies the existential quantifier ('∃') `quantDepth` times to the result
-- | of the inner monadic action.
multiEXM :: MonadSent s t tType o q m => [q] -> m s -> m s
multiEXM quantTypes inner = case quantTypes of
    [] -> inner
    [singleType] -> eXM singleType inner
    (firstType:restTypes) -> eXM firstType (multiEXM restTypes inner)



runProofByUGM :: HelperConstraints m s tType o t sE eL r1 q
                 =>  q -> ProofGenTStd tType r1 s o q m x
                            -> ProofGenTStd tType r1 s o q m (s, [Int])
runProofByUGM tt prog =  do
   (result_prop, idx, _) <- runProofByUGMWorker tt prog
   return (result_prop, idx)


multiUGM :: HelperConstraints m s tType o t sE eL r1 q =>
    [q] ->                             -- ^ List of types for UG variables (outermost first).
    ProofGenTStd tType r1 s o q m x ->       -- ^ The core program. Its monadic return 'x' is discarded.
                                           --   It must set 'Last s' with the prop to be generalized.
    ProofGenTStd tType r1 s o q m (s, [Int])  -- ^ Returns (final_generalized_prop, its_index).
multiUGM typeList programCore = do
      (result_prop, idx, _) <- multiUGMWorker typeList programCore
      return (result_prop, idx)


createTermTmplt :: SentConstraints s t tType o q => 
        [(t,Int)] -> t -> t
createTermTmplt subs originTerm = 
    let
        accumFunc (targetTerm,idx) accumTerm =
            termSwapForX targetTerm idx originTerm
    in foldr accumFunc originTerm subs
               

lambdaTermMulti :: SentConstraints s t tType o q => 
    [Int] -> t -> [t] -> t
lambdaTermMulti target_idxs template replacements = 
    let
        subs = zip target_idxs replacements
    in
        termSubXs subs template

lambdaTerm :: SentConstraints s t tType o q => 
    Int -> t -> t -> t
lambdaTerm target_idx template replacement = 
    termSubX target_idx replacement template


lambdaSentMulti :: SentConstraints s t tType o q => 
    [Int] -> s -> [t] -> s
lambdaSentMulti target_idxs template replacements = 
    let
        subs = zip target_idxs replacements
    in
        sentSubXs subs template

lambdaSent :: SentConstraints s t tType o q => 
    Int -> s -> t -> s
lambdaSent target_idx template replacement = 
    sentSubX target_idx replacement template


