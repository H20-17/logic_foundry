module RuleSets.Internal.PropLogic 
(
    LogicError, LogicRule(..), runProofAtomic, mpM, simpLM, adjM, 
    LogicRuleClass(..), SubproofRule(..),
    ProofByAsmSchema(..), SubproofError, runProofByAsm, runProofByAsmM, LogicSent(..),
    SubproofMException(..), contraFM, absurdM, MetaRuleError(..), disjIntroLM, disjIntroRM, disjElimM, doubleNegElimM,
    deMorganConjM, deMorganDisjM, bicondIntroM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM,
    peircesLawM, modusTollensM, imp2ConjM
) where

import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
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

import RuleSets.Internal.BaseLogic hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError,
   SubproofError,
   LogicRule(..),
   LogicError(..),
   runProofAtomic)
import qualified RuleSets.Internal.BaseLogic as REM


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
    LogicErrSentencesNotContra :: s -> s -> LogicError s sE o tType
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

data LogicRule tType s sE o where
    BaseRule :: REM.LogicRule tType s sE o -> LogicRule tType s sE o
    MP :: s -> LogicRule tType s sE o
    ProofByAsm :: ProofByAsmSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ExclMid :: s -> LogicRule tType s sE o
    SimpL :: s -> LogicRule tType s sE o
    SimpR :: s -> LogicRule tType s sE o
    Adj :: s -> s -> LogicRule tType s sE o
    ContraF:: s -> s -> LogicRule tType s sE o
    Absurd :: s -> LogicRule tType s sE o
    DisjIntroL :: s -> s -> LogicRule tType s sE o
    DisjIntroR :: s -> s -> LogicRule tType s sE o
    DisjElim :: s -> s -> s -> LogicRule tType s sE o
    DoubleNegElim :: s -> LogicRule tType s sE o
    DeMorganConj :: s -> LogicRule tType s sE o
    DeMorganDisj :: s -> LogicRule tType s sE o
    BicondIntro :: s -> s -> LogicRule tType s sE o
    BicondElimL :: s -> LogicRule tType s sE o
    BicondElimR :: s -> LogicRule tType s sE o
    AbsorpAnd :: s -> LogicRule tType s sE o  -- P ∧ (P ∨ Q) ⟶ P
    AbsorpOr :: s -> LogicRule tType s sE o   -- P ∨ (P ∧ Q) ⟶ P
    DistAndOverOr :: s -> LogicRule tType s sE o  -- P ∧ (Q ∨ R) ⟶ (P ∧ Q) ∨ (P ∧ R)
    DistOrOverAnd :: s -> LogicRule tType s sE o   -- P ∨ (Q ∧ R) ⟶ (P ∨ Q) ∧ (P ∨ R)
    
    PeircesLaw :: s -> LogicRule tType s sE o  -- Peirce’s Law: ((P → Q) → P) → P


    deriving(Show)



runProofAtomic :: (ProofStd s (LogicError s sE o tType) [LogicRule tType s sE o] o tType,
               LogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
               Show o, Typeable o, Typeable tType, Show tType, StdPrfPrintMonad s o tType (Either SomeException)) =>
                            LogicRule tType s sE o -> PrfStdContext tType -> PrfStdState s o tType 
                                      -> Either (LogicError s sE o tType) (Maybe s,Maybe (o,tType),PrfStdStep s o tType)
runProofAtomic rule context state = 
      case rule of
        BaseRule r -> do
            either (throwError . LogicErrBasic) return (REM.runProofAtomic r context state)
        MP implication -> do
             (antecedant, conseq) <- maybe ((throwError . LogicErrSentenceNotImp) implication) return (parse_implication implication)
             impIndex <- maybe ((throwError . LogicErrMPImplNotProven) implication) return (Data.Map.lookup implication (provenSents state))
             anteIndex <- maybe ((throwError . LogicErrMPAnteNotProven) antecedant) return (Data.Map.lookup antecedant (provenSents state))
             return (Just conseq, Nothing, PrfStdStepStep conseq "MP" [impIndex,anteIndex])
        ProofByAsm schema -> do
             (imp, step) <- left LogicErrPrfByAsmErr (runProofByAsm schema context state)
             return (Just imp, Nothing, step)
        ProofBySubArg schema -> do
             step <- left LogicErrPrfBySubArgErr (runProofBySubArg schema context state)
             return (Just $ argPrfConsequent schema, Nothing, step)
        ExclMid s -> do
             maybe (return ())   (throwError . LogicErrExclMidSanityErr s) (checkSanity (freeVarTypeStack context) s (fmap fst (consts state)))
             let prop = s .||. neg s
             return (Just prop, Nothing, PrfStdStepStep prop "EXMID" [])
        SimpL aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just a, Nothing, PrfStdStepStep a "SIMP_L" [aAndBIndex])
        SimpR aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just b, Nothing, PrfStdStepStep a "SIMP_R" [aAndBIndex])
        Adj a b -> do
            leftIndex <- maybe ((throwError . LogicErrAdjLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            rightIndex <- maybe ((throwError . LogicErrAdjRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            let aAndB = a .&&. b
            return (Just aAndB, Nothing, PrfStdStepStep aAndB "ADJ" [leftIndex,rightIndex])
        ContraF p notP -> do
            pOther <- maybe ((throwError . LogicErrSentenceNotNeg) notP) return (parseNeg notP)
            unless (p == pOther) (throwError $ LogicErrSentencesNotContra p notP)
            idx <- maybe ((throwError . LogicErrContraPNotProven) p) return (Data.Map.lookup p (provenSents state))
            idx' <- maybe ((throwError . LogicErrContraNotPNotProven) notP) return (Data.Map.lookup notP (provenSents state))
            return (Just false, Nothing, PrfStdStepStep false "CONTRA" [idx,idx'])
          
        Absurd sImpF ->do
            (antecedant, conseq) <- maybe ((throwError . LogicErrSentenceNotImp) sImpF) return (parse_implication sImpF)
            unless (conseq == false) (throwError . LogicErrConseqNotFalse $ conseq)
            idx <- maybe ((throwError . LogicErrAbsurdityNotProven) sImpF) return (Data.Map.lookup sImpF (provenSents state))
            let negation = neg antecedant
            return (Just negation , Nothing, PrfStdStepStep negation "ABSURD" [idx])

        DisjIntroL a b -> do
            leftIndex <- maybe ((throwError . LogicErrDisjIntroLLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            maybe (return ())   (throwError . LogicErrDisjIntroLRightNotSane b) (checkSanity (freeVarTypeStack context) b (fmap fst (consts state)))
            let aOrB = a .||. b
            return (Just aOrB, Nothing, PrfStdStepStep aOrB "DISJ_INTRO_L" [leftIndex])
        DisjIntroR a b -> do
            rightIndex <- maybe ((throwError . LogicErrDisjIntroRRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            maybe (return ())   (throwError . LogicErrDisjIntroRLeftNotSane a) (checkSanity (freeVarTypeStack context) a (fmap fst (consts state)))
            let aOrB = a .||. b
            return (Just aOrB, Nothing, PrfStdStepStep aOrB "DISJ_INTRO_R" [rightIndex])

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
            return (Just result, Nothing, PrfStdStepStep result "DISJ_ELIM" [disjIndex, pImpRIndex, qImpRIndex])
        DoubleNegElim doubleNegP -> do
            notP <- maybe ((throwError . LogicErrSentenceNotDoubleNeg) doubleNegP) return (parseNeg doubleNegP)
            innerP <- maybe ((throwError . LogicErrSentenceNotDoubleNeg) doubleNegP) return (parseNeg notP)
            idx <- maybe ((throwError . LogicErrDoubleNegNotProven) doubleNegP) return (Data.Map.lookup doubleNegP (provenSents state))
            return (Just innerP, Nothing, PrfStdStepStep innerP "DOUBLE_NEG_ELIM" [idx])
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
            return (Just disj, Nothing, PrfStdStepStep disj "DEMORGAN_CONJ" [index])

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
            return (Just conj, Nothing, PrfStdStepStep conj "DEMORGAN_DISJ" [index])
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
            return (Just bicond, Nothing, PrfStdStepStep bicond "BICOND_INTRO" [pImpQIndex, qImpPIndex])
        BicondElimL bicond -> do
            (p, q) <- maybe (throwError $ LogicErrSentenceNotBicond bicond) return (parseIff bicond)
            bicondIndex <- maybe (throwError $ LogicErrBicondElimLNotProven bicond) return (Data.Map.lookup bicond (provenSents state))
            let imp = p .->. q
            return (Just imp, Nothing, PrfStdStepStep imp "BICOND_ELIM_L" [bicondIndex])

        BicondElimR bicond -> do
            (p, q) <- maybe (throwError $ LogicErrSentenceNotBicond bicond) return (parseIff bicond)
            bicondIndex <- maybe (throwError $ LogicErrBicondElimRNotProven bicond) return (Data.Map.lookup bicond (provenSents state))
            let imp = q .->. p
            return (Just imp, Nothing, PrfStdStepStep imp "BICOND_ELIM_R" [bicondIndex])
        AbsorpAnd lhs -> do 
           --lhs = P ∧ (P ∨ Q) ⟶ P
           (p, rhs) <- maybe (throwError $ LogicErrInvalidAbsorpAnd lhs) return (parse_implication lhs)
           (p', q)  <- maybe (throwError $ LogicErrInvalidAbsorpAnd lhs) return (parseAdj rhs)
           unless (p == p') (throwError $ LogicErrAbsorpAndMismatch p p')
           index <- maybe (throwError $ LogicErrAbsorpAndNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
           return (Just p, Nothing, PrfStdStepStep p "ABSORP_1" [index])

        AbsorpOr lhs -> do
           -- lhs = P ∨ (P ∧ Q) ⟶ P
           (p, rhs) <- maybe (throwError $ LogicErrInvalidAbsorpOr lhs) return (parseDisj lhs)
           (p', q)  <- maybe (throwError $ LogicErrInvalidAbsorpOr lhs) return (parseAdj rhs)
           unless (p == p') (throwError $ LogicErrAbsorpOrMismatch p p')
           index <- maybe (throwError $ LogicErrAbsorpOrNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
           return (Just p, Nothing, PrfStdStepStep p "ABSORP_2" [index])
        DistAndOverOr lhs -> do
            (p, rhs) <- maybe (throwError $ LogicErrInvalidDistAndOverOr lhs) return (parseAdj lhs)
            (q, r)   <- maybe (throwError $ LogicErrInvalidDistAndOverOr lhs) return (parseDisj rhs)
            index <- maybe (throwError $ LogicErrDistAndOverOrNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
            let conclusion = (p .&&. q) .||. (p .&&. r)
            return (Just conclusion, Nothing, PrfStdStepStep conclusion "DIST_AND_OVER_OR" [index])

        DistOrOverAnd lhs -> do
            (p, rhs) <- maybe (throwError $ LogicErrInvalidDistOrOverAnd lhs) return (parseDisj lhs)
            (q, r)   <- maybe (throwError $ LogicErrInvalidDistOrOverAnd lhs) return (parseAdj rhs)
            index <- maybe (throwError $ LogicErrDistOrOverAndNotProven lhs) return (Data.Map.lookup lhs (provenSents state))
            let conclusion = (p .&&. q) .||. (p .&&. r)
            return (Just conclusion, Nothing, PrfStdStepStep conclusion "DIST_OR_OVER_AND" [index])
        PeircesLaw lhs -> do

            -- Parse (P → Q) → P
           (p1ImpQ,p2) <- maybe (throwError $ LogicErrInvalidPeircesLaw lhs) return (parse_implication lhs)
           (p1, q) <- maybe (throwError $ LogicErrInvalidPeircesLaw lhs) return (parse_implication p1ImpQ)
           unless (p1 == p2) (throwError $ LogicErrInvalidPeircesLaw lhs)

           -- Ensure the given implication is proven
           index <- maybe (throwError $ LogicErrPeircesLawNotProven lhs) return (Data.Map.lookup lhs (provenSents state))

            -- Return P
           return (Just p1, Nothing, PrfStdStepStep p1 "PEIRCE" [index])

instance (LogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType),
          StdPrfPrintMonad s o tType (Either SomeException),
          Monoid (PrfStdContext tType))
             => Proof (LogicError s sE o tType)
                 [LogicRule tType s sE o] 
                 (PrfStdState s o tType) 
                 (PrfStdContext tType)
                 [PrfStdStep s o tType]
                 s
                    where
  runProofOpen :: (LogicSent s tType, Show sE, Typeable sE, Show s, Typeable s,
               Ord o, TypedSent o tType sE s, Typeable o, Show o, Typeable tType,
               Show tType, Monoid (PrfStdState s o tType)) =>
                 [LogicRule tType s sE o] -> 
                 PrfStdContext tType  -> PrfStdState s o tType
                        -> Either (LogicError s sE o tType) (PrfStdState s o tType, [PrfStdStep s o tType],Last s) 
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



instance REM.LogicRuleClass [LogicRule tType s sE o] s o tType sE where
    remark :: Text -> [LogicRule tType s sE o]
    remark rem = [(BaseRule . REM.Remark) rem]
    rep :: s -> [LogicRule tType s sE o]
    rep s = [BaseRule . REM.Rep $ s]
    fakeProp :: s -> [LogicRule tType s sE o]
    fakeProp s = [BaseRule . REM.FakeProp $ s]
    fakeConst:: o -> tType -> [LogicRule tType s sE o]
    fakeConst o t = [BaseRule $ REM.FakeConst o t]

        --   return . PropRemark . REM.ProofBySubArg  


instance RuleInject [REM.LogicRule tType s sE o] [LogicRule tType s sE o] where
    injectRule :: [REM.LogicRule tType s sE o] -> [LogicRule tType s sE o]
    injectRule = Prelude.map BaseRule


class LogicRuleClass r s tType sE o | r-> s, r->tType, r->sE, r->o where
    mp :: s -> r
    exclMid :: s -> r
    simpL :: s -> r
    simpR :: s -> r
    adj :: s -> s -> r
    contraF :: s -> s -> r
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

instance LogicRuleClass [LogicRule tType s sE o] s tType sE o where
    mp :: s -> [LogicRule tType s sE o]
    mp s = [MP s]
    exclMid :: s -> [LogicRule tType s sE o]
    exclMid s = [ExclMid s]
    simpL :: s -> [LogicRule tType s sE o]
    simpL s = [SimpL s]
    simpR :: s -> [LogicRule tType s sE o]
    simpR s = [SimpL s]
    adj :: s -> s -> [LogicRule tType s sE o]
    adj a b = [Adj a b]
    contraF :: s -> s -> [LogicRule tType s sE o]
    contraF s notS = [ContraF s notS]
    absurd :: s -> [LogicRule tType s sE o]
    absurd s = [Absurd s]
    disjIntroL :: s -> s -> [LogicRule tType s sE o]
    disjIntroL a b = [DisjIntroL a b]
    disjIntroR :: s -> s -> [LogicRule tType s sE o]
    disjIntroR a b = [DisjIntroR a b]
    disjElim :: s -> s -> s -> [LogicRule tType s sE o]
    disjElim a b c = [DisjElim a b c]
    doubleNegElim :: s -> [LogicRule tType s sE o]
    doubleNegElim s = [DoubleNegElim s]
    deMorganConj :: s -> [LogicRule tType s sE o]
    deMorganConj s = [DeMorganConj s]
    deMorganDisj :: s -> [LogicRule tType s sE o]
    deMorganDisj s = [DeMorganDisj s]
    bicondIntro :: s -> s -> [LogicRule tType s sE o]
    bicondIntro a b = [BicondIntro a b]
    bicondElimL :: s -> [LogicRule tType s sE o]
    bicondElimL s = [BicondElimL s]
    bicondElimR :: s -> [LogicRule tType s sE o]
    bicondElimR s = [BicondElimR s]
    absorpAnd :: s -> [LogicRule tType s sE o]
    absorpAnd s = [AbsorpAnd s]
    absorpOr :: s -> [LogicRule tType s sE o]
    absorpOr s = [AbsorpOr s]
    distAndOverOr :: s -> [LogicRule tType s sE o]
    distAndOverOr s = [DistAndOverOr s]
    distOrOverAnd :: s -> [LogicRule tType s sE o]
    distOrOverAnd s = [DistOrOverAnd s]
    peircesLaw :: s -> [LogicRule tType s sE o]
    peircesLaw p = [PeircesLaw p]




instance REM.SubproofRule [LogicRule tType s sE o] s where
    proofBySubArg :: s -> [LogicRule tType s sE o] -> [LogicRule tType s sE o]
    proofBySubArg s r = [ProofBySubArg $ ProofBySubArgSchema s r]
 

instance SubproofRule [LogicRule tType s sE o] s where
    proofByAsm :: s -> s -> [LogicRule tType s sE o] -> [LogicRule tType s sE o]
    proofByAsm asm cons subproof = [ProofByAsm $ ProofByAsmSchema asm cons subproof]




standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex


mpM, exclMidM, simpLM, simpRM, absurdM, doubleNegElimM, deMorganConjM, 
       deMorganDisjM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM,
       peircesLawM ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType, Typeable eL, Show eL )
          => s -> ProofGenTStd tType r s o m (s,[Int])

adjM, disjIntroLM, disjIntroRM,  bicondIntroM, contraFM  ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType, Typeable eL, Show eL )
          => s -> s -> ProofGenTStd tType r s o m (s,[Int])

disjElimM ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType, Typeable eL, Show eL )
          => s -> s -> s -> ProofGenTStd tType r s o m (s,[Int])

mpM s = standardRuleM (mp s)
exclMidM s = standardRuleM (exclMid s)
simpLM s = standardRuleM (simpL s)
simpRM s = standardRuleM (simpR s)
adjM a b = standardRuleM (adj a b)
contraFM s notS = standardRuleM (contraF s notS)
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

data MetaRuleError s where
    MetaRuleErrNotImp :: s -> MetaRuleError s
    MetaRuleErrNotModusTollens :: s -> MetaRuleError s
    deriving (Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)


imp2ConjM :: (SubproofRule r1 s, MonadThrow m, Monoid r1,  TypedSent o tType sE s, LogicRuleClass r1 s tType sE o, 
  StdPrfPrintMonad s o tType m,  StdPrfPrintMonad s o tType (Either SomeException),  LogicSent s tType,  
  Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
  Show eL, Show o, Show s, Show sE, Show tType, Typeable eL,  
  Typeable o, Typeable s, Typeable sE, Typeable tType) => 
            s -> ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int])
imp2ConjM s = do
    (a,b) <- maybe (throwM $ MetaRuleErrNotImp s) return (parse_implication s)
    runProofByAsmM a $ do
        mpM s
        disjIntroRM (neg a) b


modusTollensM :: (Monoid r1,
                  MonadThrow m, LogicSent s tType,
                Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                 Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType, TypedSent o tType sE s, StdPrfPrintMonad s o tType m,
                 REM.SubproofRule r1 s, Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o, 
                 StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o)
    => s
    -> ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int])
modusTollensM s = do
    -- Parse (P → Q) and ¬Q from the input statement s
    (p,q) <- maybe (throwM $ MetaRuleErrNotModusTollens s) return (parse_implication s)
    let negQ = neg q


    runProofBySubArgM $ do
    -- Derive ¬P from ¬Q and P → Q (Modus Tollens)
        (absurdity,_) <- runProofByAsmM p $ do
            (q,_) <- mpM s
            contraFM q negQ
            --False now derived
        absurdM absurdity

doubleNegIntroM :: (Monoid r1, MonadThrow m, LogicSent s tType,
                   Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                   Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType,
                   TypedSent o tType sE s, StdPrfPrintMonad s o tType m, REM.SubproofRule r1 s,
                   Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                   StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o)
    => s  -- The sentence P, which must be already proven
    -> ProofGenTStd tType r1 s o m (s, [Int]) -- Returns the proven ¬¬P and its index
doubleNegIntroM p = do
    -- Prove ¬P → ⊥ by assuming ¬P and deriving a contradiction with P
    (negP_imp_False, _) <- runProofByAsmM (neg p) $ do
        -- Inside this subproof, (neg p) is assumed.
        -- contraFM uses 'p' (proven outside) and 'neg p' (the assumption).
        contraFM p (neg p) -- Derive False (⊥)

    -- Use the Absurd rule: (¬P → ⊥) ⊢ ¬¬P
    (negNegP, negNegPIdx) <- absurdM negP_imp_False
    return (negNegP, negNegPIdx)


 
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


runProofByAsm :: (ProofStd s eL1 r1 o tType, LogicSent s tType, TypedSent o tType sE s) => 
                       ProofByAsmSchema s r1 ->  
                        PrfStdContext tType -> 
                        PrfStdState s o tType ->
                        Either (SubproofError s sE eL1) (s,PrfStdStep s o tType)
runProofByAsm (ProofByAsmSchema assumption consequent subproof) context state  =
      do
         let frVarTypeStack = freeVarTypeStack context
         let constdict = fmap fst (consts state)
         let sc = checkSanity frVarTypeStack assumption constdict
         maybe (return ()) (throwError .  ProofByAsmErrAsmNotSane assumption) sc
         let alreadyProven = provenSents state
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
         let newSents = Data.Map.insert assumption (newStepIdxPrefix ++ [0]) mempty
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames
         let newState = PrfStdState newSents mempty 1
         let preambleSteps = [PrfStdStepStep assumption "ASM" []]
         let mayPreambleLastProp = (Last . Just) assumption
         let eitherTestResult = testSubproof newContext state newState preambleSteps mayPreambleLastProp consequent subproof
         finalSteps <- either (throwError . ProofByAsmErrSubproofFailedOnErr) return eitherTestResult
         let implication = assumption .->. consequent
         return (implication, PrfStdStepSubproof implication "PRF_BY_ASM" finalSteps)




data SubproofMException s sE where
    BigExceptAsmSanity :: s -> sE -> SubproofMException s sE
    deriving(Show)

instance (
              Show sE, Typeable sE, 
              Show s, Typeable s)
           => Exception (SubproofMException s sE)

class SubproofRule r s  where
   proofByAsm :: s -> s -> r -> r

runProofByAsmM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       LogicSent s tType, MonadThrow m,
                       Show s, Typeable s,
                       Show eL1, Typeable eL1, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, SubproofRule r1 s )
                 =>   s -> ProofGenTStd tType r1 s o m x
                            -> ProofGenTStd tType r1 s o m (s, [Int])
runProofByAsmM asm prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let constdict = fmap fst (consts state)
        let sc = checkSanity frVarTypeStack asm constdict
        maybe (return ()) (throwM . BigExceptAsmSanity asm) sc
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newSents = Data.Map.insert asm (newStepIdxPrefix ++ [0]) mempty
        let newContextFrames = contextFrames context <> [False]
        let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState newSents mempty 1
        let preambleSteps = [PrfStdStepStep asm "ASM" []]
        let mayPreambleLastProp = (Last . Just) asm
        (extraData,consequent,subproof,newSteps) 
                 <- lift $ runSubproofM newContext state newState preambleSteps mayPreambleLastProp prog
        mayMonadifyRes <- monadifyProofStd $ proofByAsm asm consequent subproof
        idx <- maybe (error "No theorem returned by monadifyProofStd on asm schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (asm .->. consequent,idx)




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
