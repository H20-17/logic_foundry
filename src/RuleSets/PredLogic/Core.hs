{-# LANGUAGE UndecidableInstances #-}
module RuleSets.PredLogic.Core
(
    LogicError(..), LogicRule(..), 
    runProofAtomic, 
    LogicRuleClass(..), SubproofRule(..),establishTmSilentM, expandTheoremM,
    SubproofMException(..),
    SubproofError(..),
    ProofByUGSchema(..),
    LogicSent(..), 
    LogicTerm(..),
    TheoremSchemaMT(..),
    TheoremAlgSchema,
    TheoremSchema(..),
    ChkTheoremError(..),
    establishTheorem,
    runProofByUG,
    checkTheoremMOpen,
    HelperConstraints(..),
    SentConstraints,
    MonadSent
) where


import Data.Monoid ( Last(..), Sum(..) )

import Control.Monad ( foldM, unless, when )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
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
import Data.Data (Typeable)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Control.Arrow ( left )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Trans.Maybe ( MaybeT(MaybeT, runMaybeT) )
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
   runProofAtomic,
   HelperConstraints)
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
   HelperConstraints(..))
import qualified RuleSets.PropLogic.Core as PL
import qualified RuleSets.BaseLogic.Core as BASE
import RuleSets.BaseLogic.Helpers
import RuleSets.PropLogic.Helpers hiding
   (MetaRuleError(..))
import qualified Data.Text.Read as TR
import Data.Char (isDigit, digitToInt)



data LogicError s sE o t tType where
    LogicErrPrfByAsm :: PL.SubproofError s sE (LogicError s sE o t tType) -> LogicError s sE o t tType
    LogicErrPrfBySubArg :: REM.SubproofError s sE (LogicError s sE o t tType ) -> LogicError s sE o t tType 
    LogicErrTheorem :: ChkTheoremError s sE (LogicError s sE o t tType ) o tType -> LogicError s sE o t tType 
    LogicErrTheoremM :: SomeException -> LogicError s sE o t tType 
    LogicErrPL ::  PL.LogicError s sE o tType -> LogicError s sE o t tType 
    LogicErrUG :: SubproofError s sE  (LogicError s sE o t tType ) -> LogicError s sE o t tType 
    LogicErrEINotProven :: s -> LogicError s sE o t tType 
    LogicErrUINotProven :: s -> LogicError s sE o t tType 
    LogicErrEINotExists :: s -> LogicError s sE o t tType 
    LogicErrAddConstErr :: o -> LogicError s sE o t tType 
    LogicErrEIConstDefined :: o -> LogicError s sE o t tType 
    LogicErrEGNotExists :: s -> LogicError s sE o t tType 
    LogicErrUINotForall :: s -> LogicError s sE o t tType 
    LogicErrEGNotGeneralization :: t -> s -> LogicError s sE o t tType 
    LogicErrEGTermTypeMismatch :: t -> tType -> s -> LogicError s sE o t tType 
    LogicErrUITermTypeMismatch :: t -> tType -> s -> tType -> LogicError s sE o t tType 
    PredProofTermSanity :: sE ->  LogicError s sE o t tType
    LogicErrENegNotExists :: s -> LogicError s sE o t tType
    LogicErrENegNotProven :: s -> LogicError s sE o t tType
    LogicErrANegNotForall :: s -> LogicError s sE o t tType
    LogicErrANegNotProven :: s -> LogicError s sE o t tType

    -- Equality Errors
    LogicErrSentenceNotEq :: s -> LogicError s sE o t tType       
    -- Error when expecting an equality sentence (e.g., for EqSym, EqTrans)
    LogicErrEqNotProven :: s -> LogicError s sE o t tType         
    -- Error when a required equality premise is not proven (e.g., for EqSym, EqTrans)
    LogicErrEqTransMismatch :: t -> t -> LogicError s sE o t tType 
    -- Error when the middle terms in EqTrans don't match (e.g., a=b and c=d)

    LogicErrEqSubstSourceNotProven :: s -> LogicError s sE o t tType -- New
    LogicErrEqSubstEqNotProven :: s -> LogicError s sE o t tType
    LogicErrEqSubstTemplateSanityA :: s -> tType -> sE -> LogicError s sE o t tType     -- New
    LogicErrEqSubstTemplateSanityB :: s -> tType -> sE -> LogicError s sE o t tType


   deriving (Show)

data LogicRule s sE o t tType q  where
   -- t is a term
    PropRule :: PL.LogicRule tType s sE o q -> LogicRule s sE o t tType q
    ProofByAsm :: ProofByAsmSchema s [LogicRule s sE o t tType q] -> LogicRule s sE o t tType q
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule s sE o t tType q] -> LogicRule s sE o t tType q
    ProofByUG :: ProofByUGSchema s [LogicRule s sE o t tType q] -> LogicRule s sE o t tType q
    EI :: s -> o -> LogicRule s sE o t tType q
       -- sentence of form E x . P, and a constant
    EIHilbert :: s -> LogicRule s sE o t tType q
       -- sentence of form E x . P
    EG :: t -> s -> LogicRule s sE o t tType q
        -- a free term,
        -- a sentence of the form E x . P
        -- Instantiate s using term t,
        -- If the resulting sentence is already proven, then the generalization is OK, and that is sentence s.
    UI :: t -> s -> LogicRule s sE o t tType q
        -- a free term,
        -- a sentence of the form A x . P
        -- Instantiate s using term t,
        -- If the resulting sentence is already proven, then the generalization is OK, and that is sentence s.

    Theorem :: TheoremSchema s [LogicRule s sE o t tType q] o tType -> LogicRule s sE o t tType q
    TheoremM :: TheoremAlgSchema tType [LogicRule s sE o t tType q] s o q () -> 
                             LogicRule s sE o t tType q
    ENegIntro :: s -> LogicRule s sE o t tType q
    ANegIntro :: s -> LogicRule s sE o t tType q
    EqRefl :: t -> LogicRule s sE o t tType q
    EqSym :: s -> LogicRule s sE o t tType q
    EqTrans :: s -> s -> LogicRule s sE o t tType q
    EqSubst :: Int -> s -> s -> LogicRule s sE o t tType q
       -- Template P(X idx), Equality a == b
    deriving(Show)


instance REM.LogicRuleClass [LogicRule s sE o t tType q] s o tType sE where
     remark:: Text -> [LogicRule s sE o t tType q]
     remark rem = [(PropRule . PL.BaseRule . REM.Remark) rem]
     rep :: s -> [LogicRule s sE o t tType q]
     rep s = [(PropRule . PL.BaseRule . REM.Rep) s]
     fakeProp:: [s] -> s -> [LogicRule s sE o t tType q]
     fakeProp deps s = [(PropRule . PL.BaseRule . REM.FakeProp deps) s]
     fakeConst:: o -> tType -> [LogicRule s sE o t tType q]
     fakeConst o t = [PropRule $ PL.BaseRule $ REM.FakeConst o t]

instance PL.LogicRuleClass [LogicRule s sE o t tType q] s tType sE o where
     mp:: s -> [LogicRule s sE o t tType q]
     mp a = [PropRule  (PL.MP a)]     
     exclMid:: s -> [LogicRule s sE o t tType q]
     exclMid a = [PropRule  (PL.ExclMid a)]
     simpL:: s -> [LogicRule s sE o t tType q]
     simpL a = [PropRule  (PL.SimpL a)]
     simpR :: s -> [LogicRule s sE o t tType q]
     simpR a = [PropRule (PL.SimpR a)]

     adj:: s -> s -> [LogicRule s sE o t tType q]
     adj a b = [PropRule  (PL.Adj a b)]
     contraF :: s -> [LogicRule s sE o t tType q]
     contraF a = [PropRule  (PL.ContraF a)]
     absurd:: s -> [LogicRule s sE o t tType q]
     absurd a = [PropRule  (PL.Absurd a)]    
     disjIntroL :: s -> s -> [LogicRule s sE o t tType q]
     disjIntroL a b = [PropRule (PL.DisjIntroL a b)]

     disjIntroR :: s -> s -> [LogicRule s sE o t tType q]
     disjIntroR a b = [PropRule (PL.DisjIntroR a b)]

     disjElim :: s -> s -> s -> [LogicRule s sE o t tType q]
     disjElim a b c = [PropRule (PL.DisjElim a b c)]

     doubleNegElim :: s -> [LogicRule s sE o t tType q]
     doubleNegElim a = [PropRule (PL.DoubleNegElim a)]

     deMorganConj :: s -> [LogicRule s sE o t tType q]
     deMorganConj a = [PropRule (PL.DeMorganConj a)]

     deMorganDisj :: s -> [LogicRule s sE o t tType q]
     deMorganDisj a = [PropRule (PL.DeMorganDisj a)]

     bicondIntro :: s -> s -> [LogicRule s sE o t tType q]
     bicondIntro a b = [PropRule (PL.BicondIntro a b)]

     bicondElimL :: s -> [LogicRule s sE o t tType q]
     bicondElimL a = [PropRule (PL.BicondElimL a)]

     bicondElimR :: s -> [LogicRule s sE o t tType q]
     bicondElimR a = [PropRule (PL.BicondElimR a)]

     absorpAnd :: s -> [LogicRule s sE o t tType q]
     absorpAnd a = [PropRule (PL.AbsorpAnd a)]

     absorpOr :: s -> [LogicRule s sE o t tType q]
     absorpOr a = [PropRule (PL.AbsorpOr a)]

     distAndOverOr :: s -> [LogicRule s sE o t tType q]
     distAndOverOr a = [PropRule (PL.DistAndOverOr a)]

     distOrOverAnd :: s -> [LogicRule s sE o t tType q]
     distOrOverAnd a = [PropRule (PL.DistOrOverAnd a)]

     peircesLaw :: s -> [LogicRule s sE o t tType q]
     peircesLaw p = [PropRule (PL.PeircesLaw p)]

 

class LogicRuleClass r s t tType sE o | r->s, r->o, r->tType, r->sE, r->t where
     ei :: s -> o -> r
     eiHilbert :: s -> r
     eg :: t -> s -> r
     ui :: t -> s -> r
     eNegIntro :: s -> r
     aNegIntro :: s -> r
     eqRefl :: t -> r
     eqSym :: s -> r
     eqTrans :: s -> s -> r
     eqSubst :: Int -> s -> s -> r


instance LogicRuleClass [LogicRule s sE o t tType q] s t tType sE o where
     ei:: s -> o -> [LogicRule s sE o t tType q]
     eiHilbert:: s -> [LogicRule s sE o t tType q]
     eiHilbert s = [EIHilbert s]
     ei s o = [EI s o]
     eg:: t -> s -> [LogicRule s sE o t tType q]
     eg t s = [EG t s]
     ui:: t -> s -> [LogicRule s sE o t tType q]
     ui t s = [UI t s]
     eNegIntro:: s -> [LogicRule s sE o t tType q]
     eNegIntro s = [ENegIntro s]
     aNegIntro:: s -> [LogicRule s sE o t tType q]
     aNegIntro s = [ANegIntro s]
     eqRefl :: t -> [LogicRule s sE o t tType q]
     eqRefl t = [EqRefl t]
     eqSym :: s -> [LogicRule s sE o t tType q]
     eqSym s = [EqSym s]
     eqTrans :: s -> s -> [LogicRule s sE o t tType q]
     eqTrans s1 s2 = [EqTrans s1 s2]
     eqSubst :: Int -> s -> s -> [LogicRule s sE o t tType q]
     eqSubst idx s1 s2 = [EqSubst idx s1 s2]
     





runProofAtomic :: (LogicSent s t tType o q,
                ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType q] o tType q,
               Show sE, Typeable sE, Show s, Typeable s, TypeableTerm t o tType sE q, TypedSent o tType sE s,
               Typeable o, Show o,Typeable tType, Show tType, Show t, Typeable t,
               StdPrfPrintMonad s o tType (Either SomeException), Eq t, QuantifiableTerm q tType, ShowableTerm s t, LogicTerm t,
               ShowableSent s) =>
                            LogicRule s sE o t tType q ->
                            PrfStdContext q s ->
                            PrfStdState s o tType ->
                            Either (LogicError s sE o t tType ) (Maybe s,Maybe (o,tType),PrfStdStep s o tType)
runProofAtomic rule context state  = 
      case rule of
          PropRule propR -> do
               left  LogicErrPL (PL.runProofAtomic propR context state)
          ProofByAsm schema -> do
               (implication,step) <- left LogicErrPrfByAsm (runProofByAsm schema context state)
               return (Just implication, Nothing, step)
          ProofBySubArg schema -> do
               step <- left LogicErrPrfBySubArg (runProofBySubArg schema context state)
               return (Just $ argPrfConsequent schema, Nothing, step)
          Theorem schema -> do
               step <- left LogicErrTheorem (establishTheorem schema context state)
               return (Just $ theorem schema, Nothing, step)
          TheoremM schema -> do
               (theorem,step) <- left LogicErrTheoremM (establishTmSilentM schema context state)
               return (Just theorem,Nothing, step)
          ProofByUG schema -> do
               (generalized,step) <- left LogicErrUG (runProofByUG schema context state)
               return (Just generalized,Nothing, step)
          EI existsSent const -> do 
               let mayExistsParse = parseExists existsSent
               (f,tType) <- maybe ((throwError . LogicErrEINotExists) existsSent) return mayExistsParse
               let mayExistsSentIdx = Data.Map.lookup existsSent (provenSents state)
               existsSentIdx <- maybe ((throwError . LogicErrEINotProven) existsSent) return mayExistsSentIdx
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . LogicErrEIConstDefined) const)
               let eIResultSent = (f . const2Term) const
               return (Just eIResultSent,Just (const,qTypeToTType tType), PrfStdStepStep eIResultSent "EI" [existsSentIdx])
          EG term generalization -> do
               let eitherTermType = getTypeTerm mempty varStack constDict term
               termType <- left PredProofTermSanity eitherTermType
               let mayParse = parseExists generalization
               (f,tType) <- maybe ((throwError . LogicErrEGNotExists) generalization) return mayParse
               unless (qTypeToTType tType == termType) ((throwError .  LogicErrEGTermTypeMismatch term termType) generalization)
               let sourceSent = f term
               let maySourceSentIdx = Data.Map.lookup sourceSent (provenSents state)
               sourceSentIdx <- maybe ((throwError . LogicErrEGNotGeneralization term) generalization) return maySourceSentIdx
               return (Just generalization,Nothing, PrfStdStepStep generalization "EG" [sourceSentIdx])
          UI term forallSent -> do
               let mayForallSentIdx = Data.Map.lookup forallSent (provenSents state)
               forallSentIdx <- maybe ((throwError . LogicErrUINotProven) forallSent) return mayForallSentIdx
               let mayForallParse = parseForall forallSent
               (f,tType) <- maybe ((throwError . LogicErrUINotForall) forallSent) return mayForallParse
               let eitherTermType = getTypeTerm mempty varStack constDict term
               termType <- left PredProofTermSanity eitherTermType
               unless (qTypeToTType tType == termType) ((throwError .  LogicErrUITermTypeMismatch term termType forallSent) (qTypeToTType tType))
               return (Just $ f term,Nothing, PrfStdStepStep (f term) "UI" [forallSentIdx])
          ENegIntro negExistsSent -> do
               let mayExistsSent = parseNeg negExistsSent
               existsSent <- maybe ((throwError . LogicErrENegNotExists) negExistsSent) return mayExistsSent
               let mayParse = parseExists existsSent
               (f, tType) <- maybe ((throwError . LogicErrENegNotExists) negExistsSent) return mayParse
               let mayNegExistsIdx = Data.Map.lookup negExistsSent (provenSents state)
               negExistsIdx <- maybe ((throwError . LogicErrENegNotProven) negExistsSent) return mayNegExistsIdx
               let forallNegSent = reverseParseQuantToForallNot f tType
               return (Just forallNegSent, Nothing, PrfStdStepStep forallNegSent "E_NEG" [negExistsIdx])
          ANegIntro negForallSent -> do
               let mayForallSent = parseNeg negForallSent
               forallSent <- maybe ((throwError . LogicErrANegNotForall) negForallSent) return mayForallSent
               let mayParse = parseForall forallSent
               (f, tType) <- maybe ((throwError . LogicErrANegNotForall) negForallSent) return mayParse
               let mayNegForallIdx = Data.Map.lookup negForallSent (provenSents state)
               negForallIdx <- maybe ((throwError . LogicErrANegNotProven) negForallSent) return mayNegForallIdx
               let existsNegSent = reverseParseQuantToExistsNot f tType
               return (Just existsNegSent, Nothing, PrfStdStepStep existsNegSent "A_NEG" [negForallIdx])
          EIHilbert existsSent -> do 
               let mayExistsParse = parseExists existsSent
               (f,tType) <- maybe ((throwError . LogicErrEINotExists) existsSent) return mayExistsParse
               let mayExistsSentIdx = Data.Map.lookup existsSent (provenSents state)
               existsSentIdx <- maybe ((throwError . LogicErrEINotProven) existsSent) return mayExistsSentIdx
               let hilbertObj = reverseParseQuantToHilbert f tType
               let eIResultSent = f hilbertObj
               return (Just eIResultSent,Nothing, PrfStdStepStep eIResultSent "EI_HILBERT" [existsSentIdx])
          EqRefl term -> do
              -- Check term sanity (similar to EG/UI)
              let eitherTermType = getTypeTerm mempty varStack constDict term
              termType <- left PredProofTermSanity eitherTermType
              let resultSent = term .==. term
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "EQ_REFL" [])

          EqSym eqSent -> do
              -- Parse the equality sentence (e.g., a .==. b)
              (termA, termB) <- maybe (throwError $ LogicErrSentenceNotEq eqSent) -- Add LogicErrSentenceNotEq to your error type
                                 return (parseEq eqSent)
              -- Check if the original equality is proven
              eqSentIdx <- maybe (throwError $ LogicErrEqNotProven eqSent) -- Add LogicErrEqNotProven
                                 return (Data.Map.lookup eqSent (provenSents state))
              -- Construct the symmetric sentence (b .==. a)
              let symSent = termB .==. termA
              return (Just symSent, Nothing, PrfStdStepStep symSent "EQ_SYM" [eqSentIdx])

          EqTrans eqSent1 eqSent2 -> do
              -- Parse the first equality (e.g., a .==. b)
              (termA, termB1) <- maybe (throwError $ LogicErrSentenceNotEq eqSent1) -- Re-use error
                                  return (parseEq eqSent1)
              -- Parse the second equality (e.g., b .==. c)
              (termB2, termC) <- maybe (throwError $ LogicErrSentenceNotEq eqSent2) -- Re-use error
                                  return (parseEq eqSent2)

              -- Check if the middle terms match
              unless (termB1 == termB2) (throwError $ LogicErrEqTransMismatch termB1 termB2) -- Add LogicErrEqTransMismatch

              -- Check if the premises are proven
              eqSent1Idx <- maybe (throwError $ LogicErrEqNotProven eqSent1) -- Re-use error
                                  return (Data.Map.lookup eqSent1 (provenSents state))
              eqSent2Idx <- maybe (throwError $ LogicErrEqNotProven eqSent2) -- Re-use error
                                  return (Data.Map.lookup eqSent2 (provenSents state))

              -- Construct the transitive sentence (a .==. c)
              let transSent = termA .==. termC
              return (Just transSent, Nothing, PrfStdStepStep transSent "EQ_TRANS" [eqSent1Idx, eqSent2Idx])
          EqSubst idx templateSent eqSent -> do
              -- Check if equality sentence a == b is proven
              eqSentIdx <- maybe (throwError $ LogicErrEqSubstEqNotProven eqSent)
                                 return (Data.Map.lookup eqSent (provenSents state))

                        
              -- Parse the equality sentence a == b
              (termA, termB) <- maybe (throwError $ LogicErrSentenceNotEq eqSent)
                                     return (parseEq eqSent)

              -- Get the type of termA
              -- The PredProofTermSanity error should never happen because we
              -- are getting a type from an already-proven sentence.
              let eitherTermType = getTypeTerm mempty varStack constDict termA
              termTypeA <- left PredProofTermSanity eitherTermType        

              -- Sanity check the template with the type of termA as the template var type.
              let templateVarTypeDict = Data.Map.insert idx termTypeA mempty
              let tmpltSanityErrorA = checkSanity templateVarTypeDict varStack constDict templateSent
              maybe (return ()) (throwError . LogicErrEqSubstTemplateSanityA templateSent termTypeA) tmpltSanityErrorA

              -- Instantiate the template with termA to get P(a)
              let sourceSent = sentSubX idx termA templateSent

              -- Check if the instantiated source sentence P(a) is proven
              sourceSentIdx <- maybe (throwError $ LogicErrEqSubstSourceNotProven sourceSent)
                                     return (Data.Map.lookup sourceSent (provenSents state))

              -- We aren't checking that the sanity of the template is sane relative to 
              -- the type of termB because, if the type of getTermType returns different
              -- types for termA and termB, these are just possible types, and 
              -- the equality of termA and termB guarantees that termA and termB have the same
              -- real underlying type, which should be a subtype of the effective types,
              -- and if the template is sane relative to the type of termA, because termA is identical to termB,
              -- then it must be sane when instantiated with termB. In other words CheckSanity on the template relative to the
              -- type of termA should return Nothing iff checkSanity relative to the type of termB returns Nothing. 
              --


              -- Perform the substitution in the template with termB to get P(b)
              let resultSent = sentSubX idx termB templateSent


              return (Just resultSent, Nothing, PrfStdStepStep resultSent "EQ_SUBST" [sourceSentIdx, eqSentIdx])






    where
        proven = (keysSet . provenSents) state
        constDict = fmap fst (consts state)
        varStack = freeVarTypeStack context




instance (LogicSent s t tType o q, Show sE, Typeable sE, Show s, Typeable s, TypedSent o tType sE s,
             TypeableTerm t o tType sE q, Typeable o, Show o, Typeable tType, Show tType,
             Monoid (PrfStdState s o tType), Show t, Typeable t,
             StdPrfPrintMonad s o tType (Either SomeException),
             Monoid (PrfStdContext q s), Eq t, QuantifiableTerm q tType, ShowableTerm s t, LogicTerm t,
             ShowableSent s) 
          => Proof (LogicError s sE o t tType ) 
             [LogicRule s sE o t tType q] 
             (PrfStdState s o tType) 
             (PrfStdContext q s)
             [PrfStdStep s o tType]
               s 
                 where

    runProofOpen :: (LogicSent s t tType o q, Show sE, Typeable sE, Show s, Typeable s,
                 TypedSent o tType sE s, TypeableTerm t o tType sE q, Typeable o,
                 Show o, Typeable tType, Show tType, QuantifiableTerm q tType) =>
                    [LogicRule s sE o t tType q]
                     -> PrfStdContext q s
                     -> PrfStdState s o tType 
                     -> Either (LogicError s sE o t tType ) (PrfStdState s o tType,[PrfStdStep s o tType], Last s)
    runProofOpen rs context oldState = foldM f (PrfStdState mempty mempty 0,[], Last Nothing) rs
       where
           f (newState,newSteps, mayLastProp) r =  fmap g (runProofAtomic r context (oldState <> newState))
             where
                 g ruleResult = case ruleResult of
                    (Just s,Nothing,step) -> (newState <> PrfStdState (Data.Map.insert s newLineIndex mempty) mempty 1,
                                         newSteps <> [step], (Last . Just) s)
                    (Just s,Just (newConst,tType), step) -> (newState <> 
                            PrfStdState (Data.Map.insert s newLineIndex mempty) 
                               (Data.Map.insert newConst (tType,newLineIndex) mempty) 1,
                               newSteps <> [step], (Last . Just) s)
                    (Nothing,Just (newConst,tType), step) -> (newState <> 
                            PrfStdState mempty
                               (Data.Map.insert newConst (tType,newLineIndex) mempty) 1,
                               newSteps <> [step], mayLastProp)
                    (Nothing,Nothing, step) -> (newState <>
                            PrfStdState mempty mempty 1,
                               newSteps <> [step], mayLastProp)
                    where
                        newStepCount = stepCount newState + 1
                        newLineIndex = stepIdxPrefix context <> [stepCount oldState + newStepCount-1]



instance REM.SubproofRule [LogicRule s sE o t tType q] s where
     proofBySubArg:: s -> [LogicRule s sE o t tType q] -> [LogicRule s sE o t tType q]
     proofBySubArg s r = [ProofBySubArg $ ProofBySubArgSchema s r]



instance PL.SubproofRule [LogicRule s sE o t tType q] s where
     proofByAsm:: s -> s -> [LogicRule s sE o t tType q] -> [LogicRule s sE o t tType q]
     proofByAsm asm cons subproof = [ProofByAsm $ ProofByAsmSchema asm cons subproof]


instance SubproofRule [LogicRule s sE o t tType q] s o tType q where
     theoremSchema:: TheoremSchema s [LogicRule s sE o t tType q] o tType -> [LogicRule s sE o t tType q]
     theoremSchema schema = [Theorem schema]

     theoremAlgSchema :: TheoremAlgSchema tType [LogicRule s sE o t tType q] s o q ()
             -> [LogicRule s sE o t tType q]
     theoremAlgSchema schema = [TheoremM schema]

     proofByUG:: s -> [LogicRule s sE o t tType q] -> [LogicRule s sE o t tType q]
     proofByUG s r  = [ProofByUG $ ProofByUGSchema s r]




instance RuleInject [REM.LogicRule tType s sE o q] [LogicRule s sE o t tType q] where
    injectRule:: [REM.LogicRule tType s sE o q] -> [LogicRule s sE o t tType q]
    injectRule = Prelude.map (PropRule . PL.BaseRule)


instance RuleInject [PL.LogicRule tType s sE o q] [LogicRule s sE o t tType q] where
    injectRule:: [PL.LogicRule tType s sE o q] -> [LogicRule s sE o t tType q]
    injectRule = Prelude.map PropRule


data TheoremSchema s r o tType where
   TheoremSchema :: {
                       constDict :: [(o,tType)],
                       lemmas :: [s],
                       theorem :: s,
                       theoremProof :: r               
                    } -> TheoremSchema s r o tType
    deriving Show


data ChkTheoremError senttype sanityerrtype logcicerrtype o tType where
   ChkTheoremErrLemmaNotEstablished :: senttype -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrLemmaSanity :: senttype -> sanityerrtype -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   --The lemma is insane or not closed
   ChkTheoremErrSubproofErr :: TestSubproofErr senttype sanityerrtype logcicerrtype -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrConstNotDefd :: o -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrConstTypeConflict :: o -> tType -> tType -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrSchemaDupConst :: o -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   deriving(Show)


assignSequentialSet :: Ord s => Int -> [s] -> (Int, Map s [Int])
assignSequentialSet base ls = 
    let 
        (count, indexMap) = Prelude.foldr (\el (i, m) -> 
            (i + 1, Data.Map.insert el [length ls + base - i - 1] m)) (base, mempty) ls
    in
        (count, indexMap)

assignSequentialMap :: Ord o => Int -> [(o,tType)] -> Either o (Int,Map o (tType,[Int]))
assignSequentialMap base ls = Prelude.foldr f (Right (base,mempty)) ls
   where 
      f (k, v) foldObj = case foldObj of
                           Left o -> Left o
                           Right (count,m) ->
                             case Data.Map.lookup k m of
                                Nothing -> Right (count+1, Data.Map.insert k (v,[length ls + base - count]) m)
                                Just _ -> Left k


checkTheoremOpen :: (ProofStd s eL1 r1 o tType q,TypedSent o tType sE s    )
                            => Maybe (PrfStdState s o tType,PrfStdContext q s) -> TheoremSchema s r1 o tType 
                                       -> Either (ChkTheoremError s sE eL1 o tType) [PrfStdStep s o tType]
                                       
checkTheoremOpen mayPrStateCxt (TheoremSchema constdict lemmas theorem subproof)  =
  do
       let eitherConstDictMap = assignSequentialMap 0 constdict
       (newStepCountA, newConsts) <- either (throwError . ChkTheoremErrSchemaDupConst) return eitherConstDictMap
       let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
       let constdictPure = Data.Map.map fst newConsts
       maybe (return ()) throwError (maybe (g1 constdictPure) (g2 constdictPure) mayPrStateCxt)
       let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
       let newState = PrfStdState newProven newConsts newStepCountB
       let preambleSteps = conststeps <> lemmasteps
       let mayPreambleLastProp = if Prelude.null lemmas then Last Nothing else (Last . Just . last) lemmas  
       left ChkTheoremErrSubproofErr (
                                      testSubproof newContext mempty newState preambleSteps mayPreambleLastProp theorem subproof)
      where
         conststeps = Prelude.foldr h1 [] constdict
         lemmasteps = Prelude.foldr h2 [] lemmas
         h1 (const,constType) accumList =  PrfStdStepConst const constType (q mayPrStateCxt) : accumList
            where
                 q Nothing = Nothing
                 q (Just (state,_)) = fmap snd (Data.Map.lookup const (consts state)) 
         h2 lemma accumList = PrfStdStepLemma lemma (q mayPrStateCxt) : accumList
            where
                 q Nothing = Nothing
                 q (Just (state,_)) = Data.Map.lookup lemma (provenSents state) 

         g2 constdictPure (PrfStdState alreadyProven alreadyDefinedConsts stepCount, 
                 PrfStdContext freeVarTypeStack stepIdfPrefix contextDepth) 
               = fmap constDictErr (constDictTest (fmap fst alreadyDefinedConsts) constdictPure)
                                               <|> Prelude.foldr f1 Nothing lemmas
           where
             constDictErr (k,Nothing) = ChkTheoremErrConstNotDefd k
             constDictErr (k, Just (a,b)) = ChkTheoremErrConstTypeConflict k a b
             f1 a = maybe (maybeLemmaMissing <|> maybeLemmaInsane) Just 
               where
                  maybeLemmaMissing = if not (a `Set.member` Data.Map.keysSet alreadyProven)
                                          then (Just . ChkTheoremErrLemmaNotEstablished) a else Nothing
                  maybeLemmaInsane = fmap (ChkTheoremErrLemmaSanity a) (checkSanity mempty [] constdictPure a)
         g1 constdictPure = Prelude.foldr f1 Nothing lemmas
           where
             f1 a = maybe maybeLemmaInsane Just 
               where
                  maybeLemmaInsane = fmap (ChkTheoremErrLemmaSanity a) (checkSanity mempty [] constdictPure a)

checkTheorem :: (ProofStd s eL1 r1 o tType q, TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType
                                       -> Either (ChkTheoremError s sE eL1 o tType) [PrfStdStep s o tType]
checkTheorem  = checkTheoremOpen Nothing


establishTheorem :: (ProofStd s eL1 r1 o tType q,  TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType -> PrfStdContext q s -> PrfStdState s o tType 
                                       -> Either (ChkTheoremError s sE eL1 o tType) (PrfStdStep s o tType)
establishTheorem schema context state = do
    steps <- checkTheoremOpen (Just (state,context)) schema
    let tm = theorem schema
    return (PrfStdStepTheorem tm steps)




data TheoremSchemaMT tType r s o q m x where
   TheoremSchemaMT :: {
                       mayTargetM :: MaybeT m (s,x), 
                       constDictM :: [(o,tType)],
                       lemmasM :: [s],
                       proofM :: ProofGenTStd tType r s o q m x,
                       protectedXVars :: [Int],
                       contextVarTypes :: [q]

                     } -> TheoremSchemaMT tType r s o q m x


instance (Show s, Show o, Show tType) => Show (TheoremSchemaMT tType r s o q m x) where
    show :: (Show s, Show o, Show tType) => TheoremSchemaMT tType r s o q m x -> String
    show (TheoremSchemaMT mayTarget constDict ls prog idxs qTypes) =
        "TheoremSchemaMT " <> show ls <> " <<Monadic subproof>> " <> show constDict


-- TheoremSchemaM


data SubproofMException s sE o tType where
   BigExceptLemmaSanityErr :: s -> sE -> SubproofMException s sE o tType
   BigExceptConstNotDefd :: o ->  SubproofMException s sE o tType --
   BigExceptConstTypeConflict :: o -> tType -> tType -> SubproofMException s sE o tType --
   BigExceptLemmaNotEstablished :: s -> SubproofMException s sE o tType --
   BigExceptSchemaConstDup :: o -> SubproofMException s sE o tType  --
   TheoremTargetMismatch :: s -> s -> SubproofMException s sE o tType
   TargetSanityErr :: s -> sE -> SubproofMException s sE o tType



   deriving(Show)


instance (
              Show sE, Typeable sE, 
              Show s, Typeable s,
              Show o, Typeable o,
              Show tType, Typeable tType)
           => Exception (SubproofMException s sE o tType)





type TheoremAlgSchema tType r s o q x = TheoremSchemaMT tType r s o q (Either SomeException) x


runProofByUGMWorker :: HelperConstraints m s tType o t sE eL r1 q
                 =>  q -> ProofGenTStd tType r1 s o q m x
                            -> ProofGenTStd tType r1 s o q m (s, [Int], x)
runProofByUGMWorker tt prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let newFrVarTypStack = tt : frVarTypeStack
        let newContextFrames = contextFrames context <> [False]
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContext = PrfStdContext newFrVarTypStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState mempty mempty 1
        let preambleSteps = [PrfStdStepFreevar (length frVarTypeStack) (qTypeToTType tt)]
        vIdx <- get
        (extraData,generalizable,subproof, newSteps) 
                 <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) prog vIdx
        let resultSent = createForall tt (Prelude.length frVarTypeStack) generalizable
        mayMonadifyRes <- monadifyProofStd $ proofByUG resultSent subproof
        idx <- maybe (error "No theorem returned by monadifyProofStd on ug schema. This shouldn't happen") (return . snd) mayMonadifyRes       
        return (resultSent,idx, extraData)






multiUGMWorker :: HelperConstraints m s tType o t sE eL r1 q =>
    [q] ->                             -- ^ List of types for UG variables (outermost first).
    ProofGenTStd tType r1 s o q m x ->       -- ^ The core program. Its monadic return 'x' is discarded.
                                           --   It must set 'Last s' with the prop to be generalized.
    ProofGenTStd tType r1 s o q m (s, [Int],x)  -- ^ Returns (final_generalized_prop, its_index).
multiUGMWorker typeList programCore =
    case typeList of
        [] ->
            -- Base case: No UGs to apply.
            -- Run 'programCore'. 'REM.runProofBySubArgM' will execute it,
            -- take its 'Last s' (the proposition proven by programCore) as the consequent,
            -- wrap it in a PRF_BY_SUBARG step, and return (consequent, index_of_that_step).
            do 
               (arg_result_prop, idx, extraData) <- runProofBySubArgM programCore
               return (arg_result_prop, idx,extraData)

        (outermost_ug_var_type : remaining_ug_types) ->
            -- Recursive step:
            -- 1. Define the inner program that needs to be wrapped by the current UG.
            --    This inner program is 'multiUGM' applied to the rest of the types and the original core program.
            --    Its result will be (partially_generalized_prop, its_index_from_inner_multiUGM).
            let 
                inner_action_yielding_proven_s_idx = do 
                    (_,_,extraData) <- multiUGMWorker remaining_ug_types programCore
                    return extraData
            in
            -- 2. 'runProofByUGM' expects its 'prog' argument to be of type '... m x_prog'.
            --    Here, 'inner_action_yielding_proven_s_idx' is our 'prog', and its 'x_prog' is '(s, [Int])'.
            --    This is fine; 'runProofByUGM' will execute it. The 'Last s' writer state will be
            --    set to the 's' part of the result of 'inner_action_yielding_proven_s_idx'.
            --    This 's' (the partially generalized proposition) is what 'runProofByUGM' will then generalize.
            --    'runProofByUGM' itself returns (final_ug_prop, final_ug_idx), matching our required type.
               do 
                   runProofByUGMWorker outermost_ug_var_type inner_action_yielding_proven_s_idx








checkTheoremMOpen :: (HelperConstraints m s tType o t sE eL r1 q) 
                 =>  Maybe (PrfStdState s o tType,PrfStdContext q s)  
                    -> Bool
                    -> TheoremSchemaMT tType r1 s o q m x
                    -> m (s, x, Either (r1,[PrfStdStep s o tType]) [Int], Maybe (s,x))
checkTheoremMOpen mayPrStateCxt errOnTargetMismatch (TheoremSchemaMT mayTargetM constdict lemmas prog idxs qTypes) =  do
    let eitherConstDictMap = assignSequentialMap 0 constdict
    (newStepCountA, newConsts) <- either (throwM . BigExceptSchemaConstDup) return eitherConstDictMap
    let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
    let constdictPure = Data.Map.map fst newConsts
    mayTarget <- runMaybeT mayTargetM
    maybe (maybe (return ()) throwM (g1 constdictPure)) (maybe (return ()) throwM . g2 constdictPure) mayPrStateCxt
    mayTarget <- runMaybeT mayTargetM
    case mayTarget of
        Just (targetSent, _) ->  do
            let maySe = checkSanity mempty [] constdictPure targetSent
            maybe (return ()) (throwM . TargetSanityErr targetSent) maySe
        Nothing -> return ()
    case mayPrStateCxt of
        Just (provenState, provenContext) ->
            case mayTarget of
                Just (targetSent, targetData) -> do
                    let lookup_data = Data.Map.lookup targetSent (provenSents provenState)
                    case lookup_data of
                        Just idxs -> do
                            return (targetSent, targetData, Right idxs,mayTarget)
                        Nothing -> do
                            let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
                            let preambleSteps = conststeps <> lemmasteps
                            let newState = PrfStdState newProven newConsts newStepCountB
                            let mayPreambleLastProp = if Prelude.null lemmas then Last Nothing else (Last . Just . last) lemmas
                            let maxIndex = if null idxs then 0 else maximum idxs + 1
    
                            (extra,tm,proof,newSteps) 
                                    <- runSubproofM newContext mempty newState preambleSteps mayPreambleLastProp prog (Sum maxIndex)
                            when (targetSent /= tm && errOnTargetMismatch) $
                                   throwM $ TheoremTargetMismatch tm targetSent
                            return (tm,extra, Left (proof,newSteps), mayTarget)
                Nothing -> do
                    let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
                    let preambleSteps = conststeps <> lemmasteps
                    let newState = PrfStdState newProven newConsts newStepCountB
                    let mayPreambleLastProp = if Prelude.null lemmas then Last Nothing else (Last . Just . last) lemmas
                    let maxIndex = if null idxs then 0 else maximum idxs + 1
    
                    (extra,tm,proof,newSteps) 
                                    <- runSubproofM newContext mempty newState preambleSteps mayPreambleLastProp prog (Sum maxIndex)
                    return (tm,extra, Left (proof,newSteps), mayTarget)
        Nothing -> do
            let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
            let preambleSteps = conststeps <> lemmasteps
            let newState = PrfStdState newProven newConsts newStepCountB
            let mayPreambleLastProp = if Prelude.null lemmas then Last Nothing else (Last . Just . last) lemmas
            let maxIndex = if null idxs then 0 else maximum idxs + 1
    
            (extra,tm,proof,newSteps) 
                        <- runSubproofM newContext mempty newState preambleSteps mayPreambleLastProp prog (Sum maxIndex)
            when errOnTargetMismatch $ do
                    let mayTargetSent = fmap fst mayTarget
                    maybe (return ()) (\targetSent -> 
                        unless (targetSent==tm) $
                            throwM $ TheoremTargetMismatch tm targetSent)  mayTargetSent       
            return (tm,extra, Left (proof,newSteps), mayTarget)

       where
            conststeps = Prelude.foldr h1 [] constdict
            lemmasteps = Prelude.foldr h2 [] lemmas
            h1 (const,constType) accumList = PrfStdStepConst const constType (q mayPrStateCxt) : accumList
              where
                 q Nothing = Nothing
                 q (Just (state,_)) = fmap snd (Data.Map.lookup const (consts state)) 
            h2 lemma accumList = PrfStdStepLemma lemma (q mayPrStateCxt) : accumList
              where
                 q Nothing = Nothing
                 q (Just (state,_)) = Data.Map.lookup lemma (provenSents state) 

            g2 constdictPure (PrfStdState alreadyProven alreadyDefinedConsts stepCount, PrfStdContext freeVarTypeStack stepIdfPrefix contextDepth) 
                 = fmap constDictErr (constDictTest (fmap fst alreadyDefinedConsts) constdictPure)
                                               <|> Prelude.foldr f1 Nothing lemmas
             where
                constDictErr (k,Nothing) = BigExceptConstNotDefd k
                constDictErr (k, Just (a,b)) = BigExceptConstTypeConflict k a b
                f1 a = maybe (maybeLemmaInsane <|> maybeLemmaMissing) Just 
                  where
                     maybeLemmaMissing = if not (a `Set.member` Data.Map.keysSet alreadyProven)
                                          then (Just . BigExceptLemmaNotEstablished) a else Nothing
                     maybeLemmaInsane = fmap (BigExceptLemmaSanityErr a) (checkSanity mempty [] constdictPure a)
            g1 constdictPure = Prelude.foldr f1 Nothing lemmas
              where
                 f1 a = maybe maybeLemmaInsane Just 
                   where
                      maybeLemmaInsane = fmap (BigExceptLemmaSanityErr a) (checkSanity mempty [] constdictPure a)




establishTmSilentM :: (HelperConstraints (Either SomeException) s tType o t sE eL r1 q)
                            =>  TheoremAlgSchema tType r1 s o q () -> 
                                PrfStdContext q s ->
                                PrfStdState s o tType -> 
                                    Either SomeException (s, PrfStdStep s o tType)
establishTmSilentM (schema :: TheoremAlgSchema tType r1 s o q ()) context state = 
    do
        (tm, (),_,_) <-  checkTheoremMOpen  (Just (state,context)) True schema
        return (tm, PrfStdStepTheoremM tm)



expandTheoremM :: (HelperConstraints (Either SomeException) s tType o t sE eL r1 q)
                            => TheoremAlgSchema tType r1 s o q () -> Either  SomeException (TheoremSchema s r1 o tType)
expandTheoremM ((TheoremSchemaMT mayTargetM constdict lemmas proofprog idxs qTypes):: TheoremAlgSchema tType r1 s o q ()) =
      do
          (tm,(),other,_) <- checkTheoremMOpen Nothing True (TheoremSchemaMT mayTargetM constdict lemmas proofprog idxs qTypes)
          (r1,_) <- either return (error "TheoremAlgSchema M produced unexpected Right value") other
          return $ TheoremSchema constdict lemmas tm r1


data ProofByUGSchema s r where
   ProofByUGSchema :: {
                       ugGeneralization :: s,
                       ugPrfProof :: r
                    } -> ProofByUGSchema s r
    deriving (Show)


class (PL.LogicSent s tType) => LogicSent s t tType o q | s ->tType, s ->t, t->s, s->o, s->q where
    parseExists :: s -> Maybe (t->s,q)
    parseHilbert :: t -> Maybe (t->s,q)
    parseEq :: s -> Maybe (t,t)
    (.==.) :: t -> t -> s
    parseExistsNot :: s -> Maybe (t->s,q)
    parseForallNot :: s-> Maybe (t->s,q)
    parseForall :: s -> Maybe (t->s,q)
    reverseParseQuantToExistsNot :: (t->s) -> q -> s
    reverseParseQuantToForallNot :: (t->s) -> q -> s
    reverseParseQuantToForall :: (t->s) -> q -> s
    reverseParseQuantToExists :: (t->s) -> q -> s
    reverseParseQuantToHilbert :: (t->s) -> q -> t
    sentSubX :: Int -> t -> s -> s
    sentSubXs :: [(Int, t)] -> s -> s
    aX :: q -> Int -> s -> s
    eX :: q -> Int -> s -> s
    hX :: q -> Int -> s -> t
    multiAx :: [(q,Int)] -> s -> s
    (./=.) :: t -> t -> s
    eXBang :: q -> Int -> s -> s
    tmpltPToFuncP :: Int -> s -> (t->s)
    createForall :: q -> Int -> s -> s
    

infix 4 .==.
infix 4 ./=.


class LogicTerm t where
    termSubX :: Int -> t -> t -> t
    termSubXs :: [(Int, t)] -> t -> t
    termSwapForX :: t -> Int -> t -> t
    x :: Int -> t
    termMaxXidx :: t -> Maybe Int





-- | Remaps indices inside tags using the provided function.
-- Preserves the tag wrappers ({%I...%} or {%i...%}) but updates the numbers inside.
remarkReMapIndices :: ([Int] -> [Int]) -> Text -> Text
remarkReMapIndices mapFunc input = go input
  where
    go text =
        let (prefix, matchStart) = T.breakOn "{%" text
        in if T.null matchStart
           then prefix
           else
               let potentialContent = T.drop 2 matchStart
                   (inner, rest) = T.breakOn "%}" potentialContent
               in if T.null rest
                  then prefix <> matchStart
                  else
                      if isValidContent inner
                      then 
                          let replacement = processTag inner
                              remainder = T.drop 2 rest
                          in prefix <> replacement <> go remainder
                      else 
                          prefix <> "{%" <> go potentialContent

    isValidContent :: Text -> Bool
    isValidContent t
        | T.null t = False
        | otherwise = 
            let (mode, content) = (T.head t, T.tail t)
            in (mode == 'I' || mode == 'i') && T.all (\c -> isDigit c || c == '.') content

    processTag :: Text -> Text
    processTag t =
        let mode = T.head t
            content = T.tail t
            -- Split content "1.2.3" -> ["1", "2", "3"]
            parts = T.splitOn "." content
            -- Parse strings to Ints
            currentIdxs = Prelude.map parseOrZero parts
            -- Apply user mapping function
            newIdxs = mapFunc currentIdxs
            -- Convert back to dot-separated string
            newContent = T.intercalate "." $ Prelude.map (T.pack . show) newIdxs
        in "{%" <> T.singleton mode <> newContent <> "%}"

    parseOrZero :: Text -> Int
    parseOrZero txt = case TR.decimal txt of
        Right (n, _) -> n
        Left _       -> 0





ugReindexTheoremStep :: ([Int] -> [Int]) -> PrfStdStep s o tType -> PrfStdStep s o tType
ugReindexTheoremStep indexMap step = case step of
    PrfStdStepLemma sent mayIdx -> PrfStdStepLemma sent (fmap indexMap mayIdx)
    PrfStdStepConst constName constType mayIdx -> PrfStdStepConst constName constType (fmap indexMap mayIdx)
    _ -> step


ugReindexStep ::  ([Int] -> [Int]) -> PrfStdStep s o tType -> PrfStdStep s o tType
ugReindexStep indexMap step = case step of
    PrfStdStepStep sent ruleName idxs -> PrfStdStepStep sent ruleName (Prelude.map indexMap idxs)
    PrfStdStepLemma sent mayIdx -> PrfStdStepLemma sent (fmap indexMap mayIdx)
    PrfStdStepConst constName constType mayIdx -> PrfStdStepConst constName constType (fmap indexMap mayIdx)
    PrfStdStepTheorem sent subSteps -> PrfStdStepTheorem sent (Prelude.map (ugReindexTheoremStep indexMap) subSteps)
    PrfStdStepSubproof sent ruleName subSteps -> PrfStdStepSubproof sent ruleName (ugReindex indexMap subSteps)
    PrfStdStepTheoremM sent -> PrfStdStepTheoremM sent
    PrfStdStepFreevar idx termType -> PrfStdStepFreevar idx termType
    PrfStdStepFakeConst constName termType ->  PrfStdStepFakeConst constName termType
    PrfStdStepRemark body -> PrfStdStepRemark (remarkReMapIndices indexMap body)

ugReindex :: ([Int] -> [Int]) -> [PrfStdStep s o tType] -> [PrfStdStep s o tType]
ugReindex indexMap =
    Prelude.map (ugReindexStep indexMap)



data SubproofError s sE eL where
   ProofByUGErrSubproofFailedOnErr :: TestSubproofErr s sE eL
                                    -> SubproofError s sE eL
   ProofByUGErrGenNotForall :: s -> SubproofError s sE eL 
     deriving(Show)

runProofByUG :: ( ProofStd s eL1 r1 o tType q, LogicSent s t tType o q, TypedSent o tType sE s,
                  TypeableTerm t o tType sE q, QuantifiableTerm q tType)
                        => ProofByUGSchema s r1
                            -> PrfStdContext q s
                            -> PrfStdState s o tType
                          -> Either (SubproofError s sE eL1) (s, PrfStdStep s o tType)
runProofByUG (ProofByUGSchema generalization subproof) context state =
      do
         let varstack = freeVarTypeStack context
         let mayParse = parseForall generalization
         (f,tType) <- maybe ((throwError . ProofByUGErrGenNotForall) generalization) return mayParse
         let newVarstack = tType : varstack
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext newVarstack newStepIdxPrefix newContextFrames
         let newState = PrfStdState mempty mempty 1
         let newFreeTerm = free2Term $ length varstack
         let generalizable = f newFreeTerm
         let preambleSteps = [PrfStdStepFreevar (length varstack) (qTypeToTType tType)]
         let eitherTestResult = testSubproof newContext state newState preambleSteps (Last Nothing) generalizable subproof
         finalSteps <- either (throwError . ProofByUGErrSubproofFailedOnErr) return eitherTestResult
         let finalStepsNormalized = 
                if length finalSteps == 2 then
                    case finalSteps!!1 of
                        PrfStdStepSubproof _ "PRF_BY_UG" substeps -> head finalSteps : ugReindex indexMap substeps
                        _ -> finalSteps
                else finalSteps
         return  (generalization, PrfStdStepSubproof generalization "PRF_BY_UG" finalStepsNormalized)
             where
                indexMap oldIdx = 
                    if length oldIdx > length (stepIdxPrefix context) + 2 then
                        -- this cannot happen unless lenght oldIdx >= 3, since lenght oldIdx >= 1 automatically
                        take (length (stepIdxPrefix context) + 1) oldIdx ++  [oldIdx!!(length (stepIdxPrefix context)+2) + 1] ++ drop (length (stepIdxPrefix context) + 3) oldIdx
                    else
                        oldIdx


-- take 1 from 2.1.1.0

-- then we get 2

-- 2.1.1.0 mapped to 1 ....somehow

-- 2.1.0 goes to 2.1


-- 2.1.1.0 has to go to 2.2.0

--first idx kept
-- second dropt
-- third incremented
--remaning kept


class SubproofRule r s o tType q | r->o, r -> tType, r -> q where
   theoremSchema :: TheoremSchema s r o tType -> r
   theoremAlgSchema :: TheoremAlgSchema tType r s o q () -> r
   proofByUG :: s -> r -> r





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


type HelperConstraints m s tType o t sE eL r q = ( 
              PL.HelperConstraints r s o tType sE eL q m
            , LogicSent s t tType o q
            , LogicRuleClass r s t tType sE o
            , SubproofRule r s o tType q
            , TypeableTerm t o tType sE q
            , LogicTerm t
            , ShowableTerm s t
            , Typeable t
            , Show t
            , QuantifiableTerm q tType
            , BASE.LogicRuleClass r s o tType sE
            , StdPrfPrintMonad
                      s o tType (Either SomeException)        
            , Eq t
            ) 
            
type SentConstraints s t tType o q sE = (LogicSent s t tType o q, LogicTerm t, TypeableTerm t o tType sE q, TypedSent o tType sE s, 
                                        Eq t,Show t)


type MonadSent s t tType o q sE m = (SentConstraints s t tType o q sE,  MonadState (Sum Int) m)

