{-# LANGUAGE UndecidableInstances #-}

module RuleSets.PropLogic.Core 
(
    LogicError, LogicRule(..), runProofAtomic,
    LogicRuleClass(..), SubproofRule(..),
    ProofByAsmSchema(..), SubproofError, runProofByAsm, LogicSent(..),
    HelperConstraints(..)
) where

import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map, singleton )
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
import StdPattern
    ( PrfStdState(..),
      PrfStdContext(..),
      Proof,
      TestSubproofErr(..),
      StdPrfPrintMonad,
      TypedSent(..),
      PrfStdStep(PrfStdStepStep,PrfStdStepSubproof),
      ProofStd,
      ProofGenTStd,
      monadifyProofStd,
      modifyPS,
      RuleInject(..),
      getProofState
      )

import Kernel
import Internal.StdPattern

import RuleSets.BaseLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError,
   SubproofError,
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   HelperConstraints)
import qualified RuleSets.BaseLogic.Core as REM
import RuleSets.BaseLogic.Helpers


data LogicError s sE o tType where
    LogicErrMPImplNotProven :: s-> LogicError s sE o tType
    LogicErrMPAnteNotProven :: s-> LogicError s sE o tType
    LogicErrSentenceNotImp :: s -> LogicError s sE o tType
    LogicErrSentenceNotAdj :: s -> LogicError s sE o tType
    LogicErrSentenceNotNeg :: s -> LogicError s sE o tType
    LogicErrSentenceNotDoubleNeg :: s -> LogicError s sE o tType
    LogicErrPrfByAsmErr :: SubproofError s sE (LogicError s sE o tType) -> LogicError s sE o tType
    LogicErrPrfBySubArgErr :: REM.SubproofError s sE (LogicError s sE o tType) -> LogicError s sE o tType
    LogicErrExclMidSanityErr :: s -> sE -> LogicError s sE o tType
    LogicErrSimpLAdjNotProven :: s -> LogicError s sE o tType
    LogicErrAdjLeftNotProven :: s -> LogicError s sE o tType
    LogicErrAdjRightNotProven :: s -> LogicError s sE o tType
    LogicErrRepOriginNotProven :: s -> LogicError s sE o tType
    LogicErrFakeSanityErr :: s -> sE -> LogicError s sE o tType
    LogicErrBasic :: REM.LogicError s sE o -> LogicError s sE o tType
    LogicErrContraPNotProven :: s -> LogicError s sE o tType
    LogicErrContraNotPNotProven :: s -> LogicError s sE o tType
    LogicErrAbsurdityNotProven :: s -> LogicError s sE o tType
    LogicErrConseqNotFalse :: s -> LogicError s sE o tType
    LogicErrDisjIntroLRightNotSane :: s -> sE -> LogicError s sE o tType
    LogicErrDisjIntroLLeftNotProven :: s -> LogicError s sE o tType
    LogicErrDisjIntroRLeftNotSane :: s -> sE -> LogicError s sE o tType
    LogicErrDisjIntroRRightNotProven :: s -> LogicError s sE o tType
    LogicErrDisjElimPMismatch :: s -> s-> LogicError s sE o tType
    LogicErrDisjElimQMismatch :: s -> s-> LogicError s sE o tType
    LogicErrDisjElimRNotProven :: s -> LogicError s sE o tType
    LogicErrDisjElimDisjNotProven :: s -> LogicError s sE o tType
    LogicErrDisjElimPImpRNotProven :: s -> LogicError s sE o tType
    LogicErrDisjElimQImpRNotProven :: s -> LogicError s sE o tType
    LogicErrSentenceNotDisj :: s -> LogicError s sE o tType
    LogicErrDisjElimRMismatch :: s -> s -> LogicError s sE o tType
    LogicErrDoubleNegNotProven :: s -> LogicError s sE o tType
    LogicErrDeMorganConjNotProven :: s -> LogicError s sE o tType
    LogicErrDeMorganDisjNotProven :: s -> LogicError s sE o tType
    LogicErrSentenceNotNegConj :: s -> LogicError s sE o tType
    LogicErrSentenceNotNegDisj :: s -> LogicError s sE o tType
    LogicErrBicondIntroPImpQNotProven :: s -> LogicError s sE o tType
    LogicErrBicondIntroQImpPNotProven :: s -> LogicError s sE o tType
    LogicErrBicondIntroMismatch1 :: s -> s -> LogicError s sE o tType
    LogicErrBicondIntroMismatch2 :: s -> s -> LogicError s sE o tType
    LogicErrBicondElimLNotProven :: s -> LogicError s sE o tType
    LogicErrBicondElimRNotProven :: s -> LogicError s sE o tType
    LogicErrSentenceNotBicond :: s -> LogicError s sE o tType
    LogicErrAbsorpOrMismatch :: s -> s -> LogicError s sE o tType
    LogicErrAbsorpAndMismatch :: s -> s -> LogicError s sE o tType
    LogicErrAbsorpOrNotProven :: s -> LogicError s sE o tType
    LogicErrAbsorpAndNotProven :: s -> LogicError s sE o tType
    LogicErrInvalidAbsorpOr :: s -> LogicError s sE o tType
    LogicErrInvalidAbsorpAnd :: s -> LogicError s sE o tType
    LogicErrDistAndOverOrNotProven :: s -> LogicError s sE o tType
    LogicErrDistOrOverAndNotProven :: s -> LogicError s sE o tType
    LogicErrInvalidDistAndOverOr :: s -> LogicError s sE o tType
    LogicErrInvalidDistOrOverAnd :: s -> LogicError s sE o tType
    LogicErrPeircesLawNotProven :: s -> LogicError s sE o tType
    LogicErrInvalidPeircesLaw :: s -> LogicError s sE o tType




    deriving(Show)

data LogicRule tType s sE o q t where
    BaseRule :: REM.LogicRule tType s sE o q t -> LogicRule tType s sE o q t
    MP :: s -> LogicRule tType s sE o q t
    ProofByAsm :: ProofByAsmSchema s [LogicRule tType s sE o q t] -> LogicRule tType s sE o q t
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o q t] -> LogicRule tType s sE o q t
    ExclMid :: s -> LogicRule tType s sE o q t
    SimpL :: s -> LogicRule tType s sE o q t
    SimpR :: s -> LogicRule tType s sE o q t
    Adj :: s -> s -> LogicRule tType s sE o q t
    ContraF:: s -> LogicRule tType s sE o q t
    Absurd :: s -> LogicRule tType s sE o q t
    DisjIntroL :: s -> s -> LogicRule tType s sE o q t
    DisjIntroR :: s -> s -> LogicRule tType s sE o q t
    DisjElim :: s -> s -> s -> LogicRule tType s sE o q t
    DoubleNegElim :: s -> LogicRule tType s sE o q t
    DeMorganConj :: s -> LogicRule tType s sE o q t
    DeMorganDisj :: s -> LogicRule tType s sE o q t
    BicondIntro :: s -> s -> LogicRule tType s sE o q t
    BicondElimL :: s -> LogicRule tType s sE o q t
    BicondElimR :: s -> LogicRule tType s sE o q t
    AbsorpAnd :: s -> LogicRule tType s sE o q t  -- P ∧ (P ∨ Q) ⟶ P
    AbsorpOr :: s -> LogicRule tType s sE o q t  -- P ∨ (P ∧ Q) ⟶ P
    DistAndOverOr :: s -> LogicRule tType s sE o q t  -- P ∧ (Q ∨ R) ⟶ (P ∧ Q) ∨ (P ∧ R)
    DistOrOverAnd :: s -> LogicRule tType s sE o q t   -- P ∨ (Q ∧ R) ⟶ (P ∨ Q) ∧ (P ∨ R)

    PeircesLaw :: s -> LogicRule tType s sE o q t  -- Peirce’s Law: ((P → Q) → P) → P


    deriving(Show)



runProofAtomic :: (ProofStd s (LogicError s sE o tType) [LogicRule tType s sE o q t] o tType q t,
               LogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
               Show o, Typeable o, Typeable tType, Show tType, StdPrfPrintMonad q s o tType t (Either SomeException)) =>
                            LogicRule tType s sE o q t-> PrfStdContext q s o tType t -> PrfStdState s o tType t
                                      -> Either (LogicError s sE o tType) (Maybe s,Maybe (o,tType),Maybe (Text, TagData s t), Bool,PrfStdStep s o tType t)
runProofAtomic rule context state = 
      case rule of
        BaseRule r -> do
            either (throwError . LogicErrBasic) return (REM.runProofAtomic r context state)
        MP implication -> do
             (antecedant, conseq) <- maybe ((throwError . LogicErrSentenceNotImp) implication) return (parse_implication implication)
             impIndex <- maybe ((throwError . LogicErrMPImplNotProven) implication) return (Data.Map.lookup implication (provenSents state))
             anteIndex <- maybe ((throwError . LogicErrMPAnteNotProven) antecedant) return (Data.Map.lookup antecedant (provenSents state))
             return (Just conseq, Nothing, Nothing, False, PrfStdStepStep conseq "MP" Nothing [implication,antecedant])
        ProofByAsm schema -> do
             (imp, step) <- left LogicErrPrfByAsmErr (runProofByAsm schema context state)
             return (Just imp, Nothing, Nothing, False, step)
        ProofBySubArg schema -> do
             step <- left LogicErrPrfBySubArgErr (runProofBySubArg schema context state)
             return (Just $ argPrfConsequent schema, Nothing, Nothing, False, step)
        ExclMid s -> do
             maybe (return ())   (throwError . LogicErrExclMidSanityErr s) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state))s)
             let prop = s .||. neg s
             return (Just prop, Nothing, Nothing, False, PrfStdStepStep prop "EXMID" Nothing [])
        SimpL aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just a, Nothing, Nothing, False, PrfStdStepStep a "SIMP_L" Nothing [aAndB])
        SimpR aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just b, Nothing, Nothing, False, PrfStdStepStep b "SIMP_R" Nothing [aAndB])
        Adj a b -> do
            leftIndex <- maybe ((throwError . LogicErrAdjLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            rightIndex <- maybe ((throwError . LogicErrAdjRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            let aAndB = a .&&. b
            return (Just aAndB, Nothing, Nothing, False, PrfStdStepStep aAndB "ADJ" Nothing [a,b])
        ContraF p -> do
            let notP = neg p
            idx <- maybe ((throwError . LogicErrContraPNotProven) p) return (Data.Map.lookup p (provenSents state))
            idx' <- maybe ((throwError . LogicErrContraNotPNotProven) notP) return (Data.Map.lookup notP (provenSents state))
            return (Just false, Nothing, Nothing, False, PrfStdStepStep false "CONTRA" Nothing [p,notP])
          
        Absurd sImpF ->do
            (antecedant, conseq) <- maybe ((throwError . LogicErrSentenceNotImp) sImpF) return (parse_implication sImpF)
            unless (conseq == false) (throwError . LogicErrConseqNotFalse $ conseq)
            idx <- maybe ((throwError . LogicErrAbsurdityNotProven) sImpF) return (Data.Map.lookup sImpF (provenSents state))
            let negation = neg antecedant
            return (Just negation , Nothing, Nothing, False, PrfStdStepStep negation "ABSURD" Nothing [sImpF])

        DisjIntroL a b -> do
            leftIndex <- maybe ((throwError . LogicErrDisjIntroLLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            maybe (return ())   (throwError . LogicErrDisjIntroLRightNotSane b) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state)) b)
            let aOrB = a .||. b
            return (Just aOrB, Nothing, Nothing, False, PrfStdStepStep aOrB "DISJ_INTRO_L" Nothing [a])
        DisjIntroR a b -> do
            rightIndex <- maybe ((throwError . LogicErrDisjIntroRRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            maybe (return ())   (throwError . LogicErrDisjIntroRLeftNotSane a) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state)) a)
            let aOrB = a .||. b
            return (Just aOrB, Nothing, Nothing, False, PrfStdStepStep aOrB "DISJ_INTRO_R" Nothing [b])

        DisjElim disj pImpR qImpR -> do
            -- Ensure disjunction (P ∨ Q) is proven
            disjIndex <- maybe (throwError $ LogicErrDisjElimDisjNotProven disj) 
                        return 
                        (Data.Map.lookup disj (provenSents state))

            -- Ensure both implications (P → R and Q → R) are proven
            pImpRIndex <- maybe (throwError $ LogicErrDisjElimPImpRNotProven pImpR) 
                         return 
                         (Data.Map.lookup pImpR (provenSents state))

            qImpRIndex <- maybe (throwError $ LogicErrDisjElimQImpRNotProven qImpR) 
                         return 
                         (Data.Map.lookup qImpR (provenSents state))

            -- Parse the disjunction (P ∨ Q) and implications
            (p, q) <- maybe (throwError $ LogicErrSentenceNotDisj disj) return (parseDisj disj)
            (pAnte, r1) <- maybe (throwError $ LogicErrSentenceNotImp pImpR) return (parse_implication pImpR)
            (qAnte, r2) <- maybe (throwError $ LogicErrSentenceNotImp qImpR) return (parse_implication qImpR)

            -- Ensure P matches the antecedent of P → R
            unless (p == pAnte) (throwError $ LogicErrDisjElimPMismatch p pAnte)

            -- Ensure Q matches the antecedent of Q → R
            unless (q == qAnte) (throwError $ LogicErrDisjElimQMismatch q qAnte)

            -- Ensure both implications lead to the same conclusion R
            unless (r1 == r2) (throwError $ LogicErrDisjElimRMismatch r1 r2)

            -- Conclusion: R
            let result = r1
            return (Just result, Nothing, Nothing, False, PrfStdStepStep result "DISJ_ELIM" Nothing [disj, pImpR, qImpR])
        DoubleNegElim doubleNegP -> do
            notP <- maybe ((throwError . LogicErrSentenceNotDoubleNeg) doubleNegP) return (parseNeg doubleNegP)
            innerP <- maybe ((throwError . LogicErrSentenceNotDoubleNeg) doubleNegP) return (parseNeg notP)
            idx <- maybe ((throwError . LogicErrDoubleNegNotProven) doubleNegP) return (Data.Map.lookup doubleNegP (provenSents state))
            return (Just innerP, Nothing, Nothing, False, PrfStdStepStep innerP "DOUBLE_NEG_ELIM" Nothing [doubleNegP])
        DeMorganConj negAnd -> do
            -- Step 1: Ensure negAnd is a negation
            inner <- maybe (throwError $ LogicErrSentenceNotNegConj negAnd) return (parseNeg negAnd)
            
            -- Step 2: Ensure the inner sentence is a conjunction
            (p, q) <- maybe (throwError $ LogicErrSentenceNotNegConj negAnd) return (parseAdj inner)
            
            -- Step 3: Construct the disjunction ¬P ∨ ¬Q
            let disj = neg p .||. neg q
            
            -- Step 4: Ensure negAnd is already proven
            index <- maybe (throwError $ LogicErrDeMorganConjNotProven negAnd) return (Data.Map.lookup negAnd (provenSents state))
            
            -- Step 5: Return the new sentence
            return (Just disj, Nothing, Nothing, False, PrfStdStepStep disj "DEMORGAN_CONJ" Nothing [negAnd])

        DeMorganDisj negOr -> do
            -- Step 1: Ensure negOr is a negation
            inner <- maybe (throwError $ LogicErrSentenceNotNegDisj negOr) return (parseNeg negOr)
            
            -- Step 2: Ensure the inner sentence is a disjunction
            (p, q) <- maybe (throwError $ LogicErrSentenceNotNegDisj negOr) return (parseDisj inner)
            
            -- Step 3: Construct the conjunction ¬P ∧ ¬Q
            let conj = neg p .&&. neg q
            
            -- Step 4: Ensure negOr is already proven
            index <- maybe (throwError $ LogicErrDeMorganDisjNotProven negOr) return (Data.Map.lookup negOr (provenSents state))
            
            -- Step 5: Return the new sentence
            return (Just conj, Nothing, Nothing, False, PrfStdStepStep conj "DEMORGAN_DISJ" Nothing [negOr])
        BicondIntro pImpQ qImpP -> do
            -- Ensure P → Q is proven
            pImpQIndex <- maybe (throwError $ LogicErrBicondIntroPImpQNotProven pImpQ)
                  return 
                  (Data.Map.lookup pImpQ (provenSents state))

            -- Ensure Q → P is proven
            qImpPIndex <- maybe (throwError $ LogicErrBicondIntroQImpPNotProven qImpP)
                  return (Data.Map.lookup qImpP (provenSents state))

            -- Parse implications
            (p1, q1) <- maybe (throwError $ LogicErrSentenceNotImp pImpQ) return (parse_implication pImpQ)
            (q2, p2) <- maybe (throwError $ LogicErrSentenceNotImp qImpP) return (parse_implication qImpP)

            -- Ensure antecedents match
            unless (p1 == p2) (throwError $ LogicErrBicondIntroMismatch1 p1 p2)

            -- Ensure consequents match
            unless (q1 == q2) (throwError $ LogicErrBicondIntroMismatch2 q1 q2)

            -- Conclusion: P ↔ Q
            let bicond = p1 .<->. q1
            return (Just bicond, Nothing, Nothing, False, PrfStdStepStep bicond "BICOND_INTRO" Nothing [pImpQ, qImpP])
        BicondElimL bicond -> do
            (p, q) <- maybe (throwError $ LogicErrSentenceNotBicond bicond) return (parseIff bicond)
            bicondIndex <- maybe (throwError $ LogicErrBicondElimLNotProven bicond) return (Data.Map.lookup bicond (provenSents state))
            let imp = p .->. q
            return (Just imp, Nothing, Nothing, False, PrfStdStepStep imp "BICOND_ELIM_L" Nothing [bicond])

        BicondElimR bicond -> do
            (p, q) <- maybe (throwError $ LogicErrSentenceNotBicond bicond) return (parseIff bicond)
            bicondIndex <- maybe (throwError $ LogicErrBicondElimRNotProven bicond) return (Data.Map.lookup bicond (provenSents state))
            let imp = q .->. p
            return (Just imp, Nothing, Nothing, False, PrfStdStepStep imp "BICOND_ELIM_R" Nothing [bicond])
        AbsorpAnd lhs -> do 
           --lhs = P ∧ (P ∨ Q) ⟶ P
           (p, rhs) <- maybe (throwError $ LogicErrInvalidAbsorpAnd lhs) return (parse_implication lhs)
           (p', q)  <- maybe (throwError $ LogicErrInvalidAbsorpAnd lhs) return (parseAdj rhs)
           unless (p == p') (throwError $ LogicErrAbsorpAndMismatch p p')
           index <- maybe (throwError $ LogicErrAbsorpAndNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
           return (Just p, Nothing, Nothing, False, PrfStdStepStep p "ABSORP_1" Nothing [lhs])

        AbsorpOr lhs -> do
           -- lhs = P ∨ (P ∧ Q) ⟶ P
           (p, rhs) <- maybe (throwError $ LogicErrInvalidAbsorpOr lhs) return (parseDisj lhs)
           (p', q)  <- maybe (throwError $ LogicErrInvalidAbsorpOr lhs) return (parseAdj rhs)
           unless (p == p') (throwError $ LogicErrAbsorpOrMismatch p p')
           index <- maybe (throwError $ LogicErrAbsorpOrNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
           return (Just p, Nothing, Nothing, False, PrfStdStepStep p "ABSORP_2" Nothing [lhs])
        DistAndOverOr lhs -> do
            (p, rhs) <- maybe (throwError $ LogicErrInvalidDistAndOverOr lhs) return (parseAdj lhs)
            (q, r)   <- maybe (throwError $ LogicErrInvalidDistAndOverOr lhs) return (parseDisj rhs)
            index <- maybe (throwError $ LogicErrDistAndOverOrNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
            let conclusion = (p .&&. q) .||. (p .&&. r)
            return (Just conclusion, Nothing, Nothing, False, PrfStdStepStep conclusion "DIST_AND_OVER_OR" Nothing [lhs])

        DistOrOverAnd lhs -> do
            (p, rhs) <- maybe (throwError $ LogicErrInvalidDistOrOverAnd lhs) return (parseDisj lhs)
            (q, r)   <- maybe (throwError $ LogicErrInvalidDistOrOverAnd lhs) return (parseAdj rhs)
            index <- maybe (throwError $ LogicErrDistOrOverAndNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
            let conclusion = (p .&&. q) .||. (p .&&. r)
            return (Just conclusion, Nothing, Nothing, False, PrfStdStepStep conclusion "DIST_OR_OVER_AND" Nothing [lhs])
        PeircesLaw lhs -> do

            -- Parse (P → Q) → P
           (p1ImpQ,p2) <- maybe (throwError $ LogicErrInvalidPeircesLaw lhs) return (parse_implication lhs)
           (p1, q) <- maybe (throwError $ LogicErrInvalidPeircesLaw lhs) return (parse_implication p1ImpQ)
           unless (p1 == p2) (throwError $ LogicErrInvalidPeircesLaw lhs)

           -- Ensure the given implication is proven
           index <- maybe (throwError $ LogicErrPeircesLawNotProven lhs) return (Data.Map.lookup lhs (provenSents state))

            -- Return P
           return (Just p1, Nothing, Nothing, False, PrfStdStepStep p1 "PEIRCE" Nothing [lhs])

instance (LogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType t),
          StdPrfPrintMonad q s o tType t (Either SomeException),
          Monoid (PrfStdContext q s o tType t))
             => Proof (LogicError s sE o tType)
                 [LogicRule tType s sE o q t] 
                 (PrfStdState s o tType t) 
                 (PrfStdContext q s o tType t)
                 [PrfStdStep s o tType t]
                 s
                    where
  runProofOpen :: (LogicSent s tType, Show sE, Typeable sE, Show s, Typeable s,
               Ord o, TypedSent o tType sE s, Typeable o, Show o, Typeable tType,
               Show tType, Monoid (PrfStdState s o tType t)) =>
                 [LogicRule tType s sE o q t] -> 
                 PrfStdContext q s o tType t -> PrfStdState s o tType t
                        -> Either (LogicError s sE o tType) (PrfStdState s o tType t, [PrfStdStep s o tType t],Last s) 
  runProofOpen rs context oldState = foldM f (mempty,[], Last Nothing) rs
       where
           f (newState,newSteps, mayLastProp) r =  fmap g (runProofAtomic r context (oldState <> newState))
             where
                 g ruleResult = case ruleResult of
                    (Just s,Nothing,Nothing, False, step) -> (newState <> 
                         PrfStdState {
                            provenSents= Data.Map.insert s (newLineIndex False) mempty,
                            consts = mempty,
                            stepCount = 1, 
                            tagData = mempty, 
                            remarkTagIdxs = mempty},
                                         newSteps <> [step], (Last . Just) s)
                    (Just s,Just (newConst,tType), Nothing, False, step) -> (newState <> 
                            PrfStdState {
                                provenSents = Data.Map.insert s (newLineIndex False) mempty,
                                consts = Data.Map.insert newConst (tType,newLineIndex False) mempty,
                                stepCount = 1,
                                tagData = mempty,
                                remarkTagIdxs = mempty
                            },
                               newSteps <> [step], (Last . Just) s)
                    (Nothing,Just (newConst,tType), Nothing, False, step) -> (newState <> 
                            PrfStdState {
                                provenSents = mempty,
                                consts = Data.Map.insert newConst (tType,newLineIndex False) mempty,
                                stepCount = 1,
                                tagData = mempty,
                                remarkTagIdxs = mempty
                            },
                               newSteps <> [step], mayLastProp)
                    (Nothing,Nothing, Nothing, False, step) -> (newState <>
                            PrfStdState {
                                provenSents = mempty,
                                consts = mempty,
                                stepCount = 1, 
                                tagData = mempty,
                                remarkTagIdxs = mempty
                            },
                               newSteps <> [step], mayLastProp)
                    (Nothing, Nothing, Just (tagName, tagData), True, step) -> (newState <>
                            PrfStdState {
                                provenSents = mempty,
                                consts = mempty,
                                stepCount = 0,
                                tagData = Data.Map.singleton tagName tagData,
                                remarkTagIdxs = Data.Map.singleton tagName (newLineIndex True)
                            },
                               newSteps <> [step], mayLastProp)
                    (Nothing, Nothing, Just (tag, tagData), False, step) -> 
                        -- this pattern matches if we have a remark with a tag
                        (newState <>
                            PrfStdState {
                                provenSents = mempty,
                                consts = mempty,
                                stepCount = 1,
                                tagData = Data.Map.singleton tag tagData,
                                remarkTagIdxs = Data.Map.singleton tag (newLineIndex False)
                            },
                            newSteps <> [step], mayLastProp)
                    where
                        newStepCount hiddenStep = if hiddenStep then stepCount newState else stepCount newState + 1
                        newLineIndex hiddenStep = stepIdxPrefix context <> [stepCount oldState + newStepCount hiddenStep-1]



instance REM.LogicRuleClass [LogicRule tType s sE o q t] s o tType sE t where
    remark :: Text -> Maybe Text -> [LogicRule tType s sE o q t]
    remark rem mayTag = [(BaseRule . REM.Remark rem) mayTag]
    rep :: s -> [LogicRule tType s sE o q t]
    rep s = [BaseRule . REM.Rep $ s]
    fakeProp :: [s] -> s -> [LogicRule tType s sE o q t]
    fakeProp deps s = [BaseRule . REM.FakeProp deps $ s]
    fakeConst:: o -> tType -> [LogicRule tType s sE o q t]
    fakeConst o t = [BaseRule $ REM.FakeConst o t]
    tagSent :: Text -> s -> [LogicRule tType s sE o q t]
    tagSent tagName sent = [BaseRule $ REM.TagSent tagName sent]
    tagTerm :: Text -> t -> [LogicRule tType s sE o q t]
    tagTerm tagName term = [BaseRule $ REM.TagTerm tagName term]

        --   return . PropRemark . REM.ProofBySubArg  


instance RuleInject [REM.LogicRule tType s sE o q t] [LogicRule tType s sE o q t] where
    injectRule :: [REM.LogicRule tType s sE o q t] -> [LogicRule tType s sE o q t]
    injectRule = Prelude.map BaseRule


class LogicRuleClass r s tType sE o | r-> s, r->tType, r->sE, r->o where
    mp :: s -> r
    exclMid :: s -> r
    simpL :: s -> r
    simpR :: s -> r
    adj :: s -> s -> r
    contraF :: s -> r
    absurd :: s -> r
    disjIntroL :: s -> s -> r
    disjIntroR :: s -> s -> r
    disjElim :: s -> s -> s -> r
    doubleNegElim :: s -> r
    deMorganConj :: s -> r
    deMorganDisj :: s -> r
    bicondIntro :: s -> s -> r
    bicondElimL :: s -> r
    bicondElimR :: s -> r
    absorpAnd :: s -> r
    absorpOr :: s -> r
    distAndOverOr :: s -> r
    distOrOverAnd :: s -> r
    peircesLaw :: s -> r

instance LogicRuleClass [LogicRule tType s sE o q t] s tType sE o where
    mp :: s -> [LogicRule tType s sE o q t]
    mp s = [MP s]
    exclMid :: s -> [LogicRule tType s sE o q t]
    exclMid s = [ExclMid s]
    simpL :: s -> [LogicRule tType s sE o q t]
    simpL s = [SimpL s]
    simpR :: s -> [LogicRule tType s sE o q t]
    simpR s = [SimpR s]
    adj :: s -> s -> [LogicRule tType s sE o q t]
    adj a b = [Adj a b]
    contraF :: s -> [LogicRule tType s sE o q t]
    contraF s = [ContraF s]
    absurd :: s -> [LogicRule tType s sE o q t]
    absurd s = [Absurd s]
    disjIntroL :: s -> s -> [LogicRule tType s sE o q t]
    disjIntroL a b = [DisjIntroL a b]
    disjIntroR :: s -> s -> [LogicRule tType s sE o q t]
    disjIntroR a b = [DisjIntroR a b]
    disjElim :: s -> s -> s -> [LogicRule tType s sE o q t]
    disjElim a b c = [DisjElim a b c]
    doubleNegElim :: s -> [LogicRule tType s sE o q t]
    doubleNegElim s = [DoubleNegElim s]
    deMorganConj :: s -> [LogicRule tType s sE o q t]
    deMorganConj s = [DeMorganConj s]
    deMorganDisj :: s -> [LogicRule tType s sE o q t]
    deMorganDisj s = [DeMorganDisj s]
    bicondIntro :: s -> s -> [LogicRule tType s sE o q t]
    bicondIntro a b = [BicondIntro a b]
    bicondElimL :: s -> [LogicRule tType s sE o q t]
    bicondElimL s = [BicondElimL s]
    bicondElimR :: s -> [LogicRule tType s sE o q t]
    bicondElimR s = [BicondElimR s]
    absorpAnd :: s -> [LogicRule tType s sE o q t]
    absorpAnd s = [AbsorpAnd s]
    absorpOr :: s -> [LogicRule tType s sE o q t]
    absorpOr s = [AbsorpOr s]
    distAndOverOr :: s -> [LogicRule tType s sE o q t]
    distAndOverOr s = [DistAndOverOr s]
    distOrOverAnd :: s -> [LogicRule tType s sE o q t]
    distOrOverAnd s = [DistOrOverAnd s]
    peircesLaw :: s -> [LogicRule tType s sE o q t]
    peircesLaw p = [PeircesLaw p]




instance REM.SubproofRule [LogicRule tType s sE o q t] s where
    proofBySubArg :: s -> [LogicRule tType s sE o q t] -> [LogicRule tType s sE o q t]
    proofBySubArg s r = [ProofBySubArg $ ProofBySubArgSchema s r]
 

instance SubproofRule [LogicRule tType s sE o q t] s where
    proofByAsm :: s -> s -> [LogicRule tType s sE o q t] -> [LogicRule tType s sE o q t]
    proofByAsm asm cons subproof = [ProofByAsm $ ProofByAsmSchema asm cons subproof]




standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType t), ProofStd s eL r o tType q t, StdPrfPrintMonad q s o tType t m    )
       => r -> ProofGenTStd tType r s o q t m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex


mpM, exclMidM, simpLM, simpRM, absurdM, doubleNegElimM, deMorganConjM, 
       deMorganDisjM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM, 
       peircesLawM, contraFM ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType t), StdPrfPrintMonad q s o tType t m,
       StdPrfPrintMonad q s o tType t (Either SomeException), Monoid (PrfStdContext q s o tType t),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType q t, Typeable eL, Show eL )
          => s -> ProofGenTStd tType r s o q t m (s,[Int])

adjM, disjIntroLM, disjIntroRM,  bicondIntroM  ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType t), StdPrfPrintMonad q s o tType t m,
       StdPrfPrintMonad q s o tType t (Either SomeException), Monoid (PrfStdContext q s o tType t),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType q t, Typeable eL, Show eL )
          => s -> s -> ProofGenTStd tType r s o q t m (s,[Int])

disjElimM ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType t), StdPrfPrintMonad q s o tType t m,
       StdPrfPrintMonad q s o tType t (Either SomeException), Monoid (PrfStdContext q s o tType t),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType q t, Typeable eL, Show eL )
          => s -> s -> s -> ProofGenTStd tType r s o q t m (s,[Int])

mpM s = standardRuleM (mp s)
exclMidM s = standardRuleM (exclMid s)
simpLM s = standardRuleM (simpL s)
simpRM s = standardRuleM (simpR s)
adjM a b = standardRuleM (adj a b)
contraFM s = standardRuleM (contraF s)
absurdM s = standardRuleM (absurd s)
disjIntroLM a b = standardRuleM (disjIntroL a b)
disjIntroRM a b = standardRuleM (disjIntroR a b)
disjElimM p q r = standardRuleM (disjElim p q r)
doubleNegElimM s = standardRuleM (doubleNegElim s)
deMorganConjM s = standardRuleM (deMorganConj s)
deMorganDisjM s = standardRuleM (deMorganDisj s)
bicondIntroM a b = standardRuleM (bicondIntro a b)
bicondElimLM s = standardRuleM (bicondElimL s)
bicondElimRM s = standardRuleM (bicondElimR s)
absorpAndM s = standardRuleM (absorpAnd s)
absorpOrM s = standardRuleM (absorpOr s)
distAndOverOrM s = standardRuleM (distAndOverOr s)
distOrOverAndM s = standardRuleM (distOrOverAnd s)
peircesLawM p = standardRuleM (peircesLaw p)






data ProofByAsmSchema s r where
   ProofByAsmSchema :: {
                       asmPrfAsm :: s,
                       asmPrfConsequent :: s,
                       asmPrfProof :: r
                    } -> ProofByAsmSchema s r
    deriving Show



data SubproofError senttype sanityerrtype logcicerrtype where
   ProofByAsmErrAsmNotSane :: senttype -> sanityerrtype -> SubproofError senttype sanityerrtype logcicerrtype
   ProofByAsmErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> SubproofError senttype sanityerrtype logcicerrtype
    deriving(Show)


runProofByAsm :: (ProofStd s eL1 r1 o tType q t, LogicSent s tType, TypedSent o tType sE s) => 
                       ProofByAsmSchema s r1 ->  
                        PrfStdContext q s o tType t-> 
                        PrfStdState s o tType t ->
                        Either (SubproofError s sE eL1) (s,PrfStdStep s o tType t)
runProofByAsm (ProofByAsmSchema assumption consequent subproof) context state  =
      do
         let frVarTypeStack = freeVarTypeStack context
         let constdict = fmap fst (consts state)
         let sc = checkSanity mempty frVarTypeStack constdict assumption
         maybe (return ()) (throwError .  ProofByAsmErrAsmNotSane assumption) sc
         let alreadyProven = provenSents state
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
         let newSents = Data.Map.insert assumption (newStepIdxPrefix ++ [0]) mempty
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames (Just state)
         let newState = PrfStdState {
            provenSents = newSents,
            consts = mempty,
            stepCount = 1,
            tagData = mempty,
            remarkTagIdxs = mempty
         }
         let preambleSteps = [PrfStdStepStep assumption "ASM" Nothing []]
         let mayPreambleLastProp = (Last . Just) assumption
         let eitherTestResult = testSubproof newContext state newState preambleSteps mayPreambleLastProp consequent subproof
         finalSteps <- either (throwError . ProofByAsmErrSubproofFailedOnErr) return eitherTestResult
         let implication = assumption .->. consequent
         return (implication, PrfStdStepSubproof implication "PRF_BY_ASM" finalSteps)






class SubproofRule r s  where
   proofByAsm :: s -> s -> r -> r




class (Ord s, Eq tType) 
              => LogicSent s tType | s -> tType where
     (.&&.) :: s -> s -> s
     parseAdj :: s -> Maybe(s,s)
     (.->.) :: s->s->s
     parse_implication:: s -> Maybe (s,s)
     neg :: s -> s
     parseNeg :: s -> Maybe s
     (.||.) :: s -> s -> s
     parseDisj :: s -> Maybe (s,s)
     false :: s
     (.<->.) :: s -> s -> s
     parseIff :: s -> Maybe (s,s)



infixr 3 .&&.
infixr 2 .||.
infixr 0 .->.
infixr 0 .<->.


type HelperConstraints r1 s o tType sE eL1 q t m = (
                      REM.HelperConstraints r1 s o tType sE eL1 q t m
                    , LogicSent s tType
                    , SubproofRule r1 s
                    , LogicRuleClass r1 s tType sE o
          )