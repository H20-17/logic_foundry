module RuleSets.PredLogic.Helpers
(
    uiM, eiM, reverseANegIntroM, reverseENegIntroM,eNegIntroM, aNegIntroM,
    eiHilbertM, egM,
    runProofByUGM,
    MetaRuleError(..),
    eqReflM, eqSymM, eqTransM, eqSubstM,
    extractConstsSentM,
    multiUGM
) where


import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
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
import Data.Maybe ( isNothing )

import Kernel
import Internal.StdPattern

import RuleSets.BaseLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic)
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
   MetaRuleError(..))
import qualified RuleSets.PropLogic.Core as PL
import qualified RuleSets.BaseLogic.Core as BASE
import RuleSets.BaseLogic.Helpers
import RuleSets.PropLogic.Helpers hiding
   (MetaRuleError(..))
import RuleSets.PredLogic.Core



standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex




uiM, egM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
               StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException),
                Monoid (PrfStdContext tType), LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL,
                Typeable eL, Monoid r)
                   => t -> s -> ProofGenTStd tType r s o m (s,[Int])
uiM term sent = standardRuleM (ui term sent)
egM term sent = standardRuleM (eg term sent)



eiM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m,
                StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
                LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL, Typeable eL, Monoid r)
                   => s -> o -> ProofGenTStd tType r s o m (s,[Int],t)
eiM sent const = do
                   (instantiated, idx) <- standardRuleM (ei sent const)
                   return (instantiated,idx,const2Term const)



eNegIntroM, aNegIntroM, eqSymM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m,
                StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
                LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL, Typeable eL, Monoid r)
                   => s -> ProofGenTStd tType r s o m (s,[Int])
eNegIntroM sent = standardRuleM (eNegIntro sent)

aNegIntroM sent = standardRuleM (aNegIntro sent)

eqSymM eqSent = standardRuleM (eqSym eqSent)


eiHilbertM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m,
                StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
                LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL, Typeable eL, Monoid r)
                   => s -> ProofGenTStd tType r s o m (s,[Int],t)

eiHilbertM sent = do
         (instantiated, idx) <- standardRuleM (eiHilbert sent)
         let mayParse = parseExists sent
         (f,tType) <- maybe (error "parse exists failed when it should not have") return mayParse
         let hilbertObj = reverseParseQuantToHilbert f tType
         return (instantiated,idx,hilbertObj)


eqTransM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
             Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
             Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
             StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException),
             Monoid (PrfStdContext tType), LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL,
             Typeable eL, Monoid r)
           => s -> s -> ProofGenTStd tType r s o m (s,[Int])
eqTransM eqSent1 eqSent2 = standardRuleM (eqTrans eqSent1 eqSent2)



eqSubstM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
             Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
             Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
             StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException),
             Monoid (PrfStdContext tType), LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL,
             Typeable eL, Monoid r)
           => Int -> s -> s -> ProofGenTStd tType r s o m (s,[Int])
eqSubstM idx templateSent eqSent = standardRuleM (eqSubst idx templateSent eqSent)

eqReflM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
            Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
            Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
            StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException),
            Monoid (PrfStdContext tType), LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL,
            Typeable eL, Monoid r)
          => t -> ProofGenTStd tType r s o m (s,[Int])
eqReflM term = standardRuleM (eqRefl term)


reverseANegIntroM, reverseENegIntroM :: (Monad m, LogicSent s t tType o, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m,
                StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
                LogicRuleClass r s t tType sE o, ProofStd s eL r o tType, Show eL, Typeable eL, Monoid r,
                REM.SubproofRule r s, LogicConst o,
                PL.SubproofRule r s,
                PL.LogicRuleClass r s tType sE o, BASE.LogicRuleClass r s o tType sE, ShowableSent s)
                   => s -> ProofGenTStd tType r s o m (s,[Int])





data MetaRuleError s where
   ReverseANegIntroMNotExistsNot :: s -> MetaRuleError s
   ReverseENegIntroMNotForallNot :: s -> MetaRuleError s
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










runProofByUGM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       LogicSent s t tType o, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m,SubproofRule r1 s o tType, BASE.LogicRuleClass r1 s o tType sE)
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

multiUGM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       LogicSent s t tType o, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m,SubproofRule r1 s o tType, 
                       BASE.SubproofRule r1 s, BASE.LogicRuleClass r1 s o tType sE,  StdPrfPrintMonad
                          s o tType (Either SomeException), Show o, Show tType, Typeable o, Typeable tType   ) =>
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


extractConstsSentM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       LogicSent s t tType o, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m,SubproofRule r1 s o tType, 
                       BASE.SubproofRule r1 s    )  
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