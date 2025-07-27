module RuleSets.PropLogic 
(
    LogicError, LogicRule(..), runProofAtomic, mpM, simpLM,
    simpRM, adjM, 
    LogicRuleClass(..), SubproofRule(..),
    ProofByAsmSchema(..), SubproofError, runProofByAsm, runProofByAsmM, LogicSent(..),
    SubproofMException(..), contraFM, absurdM, MetaRuleError(..), disjIntroLM, disjIntroRM, disjElimM, doubleNegElimM,
    deMorganConjM, deMorganDisjM, bicondIntroM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM,
    peircesLawM, modusTollensM, imp2DisjM, negAndNotToOrM, negImpToConjViaEquivM, negBicondToPosBicondM,
    disjunctiveSyllogismM, exFalsoM, deconstructAdjM
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

import RuleSets.BaseLogic hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError,
   SubproofError,
   LogicRule(..),
   LogicError(..),
   runProofAtomic)
import qualified RuleSets.BaseLogic as REM


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

data LogicRule tType s sE o where
    BaseRule :: REM.LogicRule tType s sE o -> LogicRule tType s sE o
    MP :: s -> LogicRule tType s sE o
    ProofByAsm :: ProofByAsmSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ExclMid :: s -> LogicRule tType s sE o
    SimpL :: s -> LogicRule tType s sE o
    SimpR :: s -> LogicRule tType s sE o
    Adj :: s -> s -> LogicRule tType s sE o
    ContraF:: s -> LogicRule tType s sE o
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
             maybe (return ())   (throwError . LogicErrExclMidSanityErr s) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state))s)
             let prop = s .||. neg s
             return (Just prop, Nothing, PrfStdStepStep prop "EXMID" [])
        SimpL aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just a, Nothing, PrfStdStepStep a "SIMP_L" [aAndBIndex])
        SimpR aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just b, Nothing, PrfStdStepStep b "SIMP_R" [aAndBIndex])
        Adj a b -> do
            leftIndex <- maybe ((throwError . LogicErrAdjLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            rightIndex <- maybe ((throwError . LogicErrAdjRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            let aAndB = a .&&. b
            return (Just aAndB, Nothing, PrfStdStepStep aAndB "ADJ" [leftIndex,rightIndex])
        ContraF p -> do
            let notP = neg p
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
            maybe (return ())   (throwError . LogicErrDisjIntroLRightNotSane b) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state)) b)
            let aOrB = a .||. b
            return (Just aOrB, Nothing, PrfStdStepStep aOrB "DISJ_INTRO_L" [leftIndex])
        DisjIntroR a b -> do
            rightIndex <- maybe ((throwError . LogicErrDisjIntroRRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            maybe (return ())   (throwError . LogicErrDisjIntroRLeftNotSane a) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state)) a)
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
    fakeProp :: [s] -> s -> [LogicRule tType s sE o]
    fakeProp deps s = [BaseRule . REM.FakeProp deps $ s]
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
    contraF :: s -> [LogicRule tType s sE o]
    contraF s = [ContraF s]
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
       peircesLawM, contraFM ::
       (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType, Typeable eL, Show eL )
          => s -> ProofGenTStd tType r s o m (s,[Int])

adjM, disjIntroLM, disjIntroRM,  bicondIntroM  ::
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

data MetaRuleError s where
    MetaRuleErrNotImp :: s -> MetaRuleError s
    MetaRuleErrNotModusTollens :: s -> MetaRuleError s  
    MetaRuleErrNotAdj :: s -> MetaRuleError s
    MetaRuleErrNotNeg :: s -> MetaRuleError s
    MetaRuleErrNotDisj :: s -> MetaRuleError s
    MetaRuleErrNotNegBicond :: s -> MetaRuleError s
    MetaRuleErrNotBicond :: s -> MetaRuleError s
    MetaRuleErrDisjSyllNotDisj :: s -> MetaRuleError s
    deriving (Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)

-- | Given a proven implication 's' (of the form A → B), this function
-- | derives and proves its equivalent disjunctive form: ¬A ∨ B.
-- | This transformation is known as Material Implication.
-- |
-- | The proof strategy is as follows:
-- | 1. Given s: A → B.
-- | 2. Parse 's' to identify the antecedent A (term `a`) and consequent B (term `b`).
-- | 3. Prove A ∨ ¬A using the Law of Excluded Middle (`exclMidM`).
-- | 4. Case 1 (Subproof 1): Assume A.
-- |    a. From the assumed A and the given A → B, derive B using Modus Ponens (`mpM`).
-- |    b. From the derived B, introduce the disjunction ¬A ∨ B using `disjIntroRM`.
-- |    This subproof concludes A → (¬A ∨ B).
-- | 5. Case 2 (Subproof 2): Assume ¬A.
-- |    a. From the assumed ¬A, introduce the disjunction ¬A ∨ B using `disjIntroLM`.
-- |    This subproof concludes ¬A → (¬A ∨ B).
-- | 6. Apply Disjunction Elimination (`disjElimM`) using:
-- |    - The proven A ∨ ¬A (from step 3).
-- |    - The proven A → (¬A ∨ B) (from step 4).
-- |    - The proven ¬A → (¬A ∨ B) (from step 5).
-- |    The result is ¬A ∨ B.
-- |
-- | Note on Naming: The name 'imp2ConjM' is misleading for this function,
-- | as it transforms an implication into a disjunction.
-- | A more appropriate name would be 'impToDisjM' or 'materialImplicationM'.
imp2DisjM :: (SubproofRule r1 s, MonadThrow m, Monoid r1,  TypedSent o tType sE s, LogicRuleClass r1 s tType sE o,
  StdPrfPrintMonad s o tType m,  StdPrfPrintMonad s o tType (Either SomeException),  LogicSent s tType,
  Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
  Show eL, Show o, Show s, Show sE, Show tType, Typeable eL,
  Typeable o, Typeable s, Typeable sE, Typeable tType) =>
            s -- ^ A proven proposition 's' of the form (A → B).
            -> ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int]) -- ^ Returns the proven proposition (¬A ∨ B) and its proof index.
imp2DisjM s_imp_ab = do
    -- 1. Parse the input implication s_imp_ab = (a -> b) to extract antecedent 'a' and consequent 'b'.
    (a_term, b_term) <- maybe (throwM $ MetaRuleErrNotImp s_imp_ab) return (parse_implication s_imp_ab)

    -- The target proposition we want to prove directly.
    let target_disjunction = neg a_term .||. b_term

    -- 2. Prove A ∨ ¬A using Excluded Middle.
    (a_or_not_a_proven, _) <- exclMidM a_term

    -- 3. Case 1 Subproof: Prove A → (¬A ∨ B)
    (a_implies_target, _) <- runProofByAsmM a_term $ do
        -- 'a_term' is assumed.
        -- Use the original proven implication 's_imp_ab' (A → B) and the assumed 'a_term' (A)
        -- to derive 'b_term' (B) by Modus Ponens.
        (b_derived, _) <- mpM s_imp_ab
        -- From the derived 'b_derived' (B), introduce the disjunction (¬A ∨ B).
        disjIntroRM (neg a_term) b_derived
        return () -- Subproof concludes with (¬A ∨ B)

    -- 4. Case 2 Subproof: Prove ¬A → (¬A ∨ B)
    (not_a_implies_target, _) <- runProofByAsmM (neg a_term) $ do
        -- 'neg a_term' (¬A) is assumed.
        -- From the assumed 'neg a_term' (¬A), introduce the disjunction (¬A ∨ B).
        disjIntroLM (neg a_term) b_term
        return () -- Subproof concludes with (¬A ∨ B)

    -- 5. Apply Disjunction Elimination.
    --    We have proven:
    --      1. a_or_not_a_proven:      A ∨ ¬A
    --      2. a_implies_target:        A → (¬A ∨ B)
    --      3. not_a_implies_target:    ¬A → (¬A ∨ B)
    --    The result will be (¬A ∨ B).
    disjElimM a_or_not_a_proven a_implies_target not_a_implies_target


-- | Given a proven disjunction 's_notA_or_B' (of the form ¬A ∨ B),
-- | this function derives and proves its equivalent implicative form: A → B.
-- | This transformation is the reverse of Material Implication.
-- |
-- | The proof strategy is:
-- | 1. Given s: ¬A ∨ B.
-- | 2. To prove A → B, assume A.
-- | 3. Under the assumption of A, we need to derive B. This is done by assuming ¬B
-- |    for a proof by contradiction (RAA) to derive B.
-- |    a. Assume ¬B.
-- |    b. From the assumed A and assumed ¬B, form A ∧ ¬B using Adjunction.
-- |    c. Transform A ∧ ¬B into ¬(¬A ∨ B) using De Morgan's laws and Double Negation.
-- |       (Specifically, A ∧ ¬B  ⇔  ¬¬A ∧ ¬B  ⇔  ¬(¬(¬¬A) ∨ ¬(¬B))  ⇔  ¬(A ∨ B) - no, this is wrong.
-- |        A ∧ ¬B  ⇔  ¬(¬(A ∧ ¬B)) ⇔ ¬(¬A ∨ ¬(¬B)) ⇔ ¬(¬A ∨ B) )
-- |       The direct De Morgan for this is ¬(P → Q) ⇔ P ∧ ¬Q.
-- |       We need to show that (A ∧ ¬B) contradicts (¬A ∨ B).
-- |       (A ∧ ¬B) is true. (¬A ∨ B) is true.
-- |       If (¬A ∨ B) is true:
-- |           Case i: ¬A is true. This contradicts A (from A ∧ ¬B). So False.
-- |           Case ii: B is true. This contradicts ¬B (from A ∧ ¬B). So False.
-- |       Since both disjuncts of (¬A ∨ B) lead to a contradiction if (A ∧ ¬B) is also true,
-- |       then (A ∧ ¬B) and (¬A ∨ B) are contradictory.
-- |    d. A formal derivation of False from (A ∧ ¬B) and (¬A ∨ B):
-- |       i.   A (from A ∧ ¬B)
-- |       ii.  ¬B (from A ∧ ¬B)
-- |       iii. ¬A ∨ B (original premise)
-- |       iv.  Subproof 1: Assume ¬A. Contradiction with (i). So False. (¬A → False)
-- |       v.   Subproof 2: Assume B. Contradiction with (ii). So False. (B → False)
-- |       vi.  DisjElim on (iii), (iv), (v) yields False.
-- |    e. So, assuming ¬B (in context of A and ¬A ∨ B) led to False. (¬B → False)
-- | 4. By RAA (absurdM), from (¬B → False), derive ¬¬B.
-- | 5. By Double Negation Elimination, from ¬¬B, derive B.
-- | 6. Since assuming A led to B, conclude A → B.
disj2ImpM :: (SubproofRule r1 s, MonadThrow m, Monoid r1,  TypedSent o tType sE s, LogicRuleClass r1 s tType sE o,
  StdPrfPrintMonad s o tType m,  StdPrfPrintMonad s o tType (Either SomeException),  LogicSent s tType,
  Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
  Show eL, Show o, Show s, Show sE, Show tType, Typeable eL,
  Typeable o, Typeable s, Typeable sE, Typeable tType) =>
            s -- ^ A proven proposition 's' of the form (¬A ∨ B).
            -> ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int]) -- ^ Returns the proven proposition (A → B) and its proof index.
disj2ImpM s_notA_or_B_proven = do
    -- 1. Parse the input disjunction s_notA_or_B_proven = (¬A ∨ B)
    --    to get terms ¬A (not_a_term_parsed), B (b_term_parsed), and A (a_term_parsed).
    (not_a_term_parsed, b_term_parsed) <- maybe (throwM $ MetaRuleErrNotDisj s_notA_or_B_proven)
                                              return (parseDisj s_notA_or_B_proven)
    a_term_parsed <- maybe (throwM $ MetaRuleErrNotNeg not_a_term_parsed)
                           return (parseNeg not_a_term_parsed)

    -- 2. Goal: Prove A → B. Start a subproof assuming A ('a_term_parsed').
    runProofByAsmM a_term_parsed $ do
        -- Current assumption in this scope: 'a_term_parsed' (A) is proven.
        -- We also have 's_notA_or_B_proven' (¬A ∨ B) from the outer scope.
        -- Goal: Derive 'b_term_parsed' (B).

        -- To derive B, we use RAA: assume ¬B ('not_b_to_assume') and derive a contradiction.
        let not_b_to_assume = neg b_term_parsed
        (not_b_implies_false, _) <- runProofByAsmM not_b_to_assume $ do
            -- Current assumptions:
            --   'a_term_parsed' (A) - from parent subproof scope
            --   'not_b_to_assume' (¬B) - current subproof assumption
            --   's_notA_or_B_proven' (¬A ∨ B) - from outermost scope

            -- We need to show that these three together lead to False.
            -- We'll use Disjunction Elimination on 's_notA_or_B_proven' (¬A ∨ B).
            -- Case 1: Assume ¬A (which is 'not_a_term_parsed')
            (case1_notA_implies_false, _) <- runProofByAsmM not_a_term_parsed $ do
                -- We have 'a_term_parsed' (A) and 'not_a_term_parsed' (¬A). Contradiction.
                contraFM a_term_parsed -- Derives False
                return ()

            -- Case 2: Assume B (which is 'b_term_parsed')
            (case2_B_implies_false, _) <- runProofByAsmM b_term_parsed $ do
                -- We have 'b_term_parsed' (B) and 'not_b_to_assume' (¬B). Contradiction.
                contraFM b_term_parsed-- Derives False
                return ()

            -- Apply DisjElim: from (¬A ∨ B), (¬A → False), (B → False), conclude False.
            (falsity_derived, _) <- disjElimM s_notA_or_B_proven case1_notA_implies_false case2_B_implies_false
            return () -- Innermost subproof (Assume ¬B) concludes False.

        -- We have now proven (¬B → False).
        (not_not_b_derived, _) <- absurdM not_b_implies_false -- Derives ¬¬B

        -- Use Double Negation Elimination to get B from ¬¬B.
        (b_final_derived, _) <- doubleNegElimM not_not_b_derived
        
        -- The middle subproof (which assumed A) now has B ('b_final_derived') as its last proven statement.
        return ()

    -- The outermost 'runProofByAsmM a_term_parsed ...' will construct and prove:
    --   a_term_parsed → b_final_derived
    -- which is A → B.





-- Helper to transform a proven Neg(A && Neg B) into a proven (Neg A || B)
-- Uses DeMorgan, Double Negation Elimination, and Proof by Cases (DisjElim).
negAndNotToOrM :: (MonadThrow m, Monoid r1,
                   ProofStd s eL1 r1 o tType,
                   LogicSent s tType,         -- From PropLogic
                   TypedSent o tType sE s,    -- From Internal.StdPattern
                   LogicRuleClass r1 s tType sE o,
                   SubproofRule r1 s,
                   StdPrfPrintMonad s o tType m,
                   StdPrfPrintMonad s o tType (Either SomeException),
                   Show s, Typeable s, Show sE, Typeable sE, Show eL1, Typeable eL1,
                   Show o, Typeable o, Show tType, Typeable tType, Ord o
                  )
               => s -- ^ The proven proposition of the form Neg (a :&&: Neg b)
               -> ProofGenTStd tType r1 s o m (s, [Int]) -- Returns (Neg a :||: b, its_index)
negAndNotToOrM provenNegAAndNotB = do
    -- 1. Parse the input to get the terms A and B.
    innerConjunction <- maybe (throwM $ MetaRuleErrNotNeg provenNegAAndNotB)
                              return (parseNeg provenNegAAndNotB)
    (a_term, not_b_term) <- maybe (throwM $ MetaRuleErrNotAdj innerConjunction)
                                 return (parseAdj innerConjunction)
    b_term <- maybe (throwM $ MetaRuleErrNotNeg not_b_term)
                    return (parseNeg not_b_term)

    -- The target proposition we want to prove is (Neg a_term :||: b_term)
    let target_disjunction = neg a_term .||. b_term

    -- 2. Apply De Morgan's Law to provenNegAAndNotB.
    --    Input: Neg (A && Neg B)
    --    Output (s_or_form_proven): (Neg A) || (Neg (Neg B))
    (s_or_form_proven, _) <- deMorganConjM provenNegAAndNotB
    -- s_or_form_proven has the structure: (neg a_term) :||: (neg not_b_term)
    -- which is equivalent to (neg a_term) :||: (neg (neg b_term))

    -- For Disjunction Elimination, we need two implications:
    --   I1: (Neg A) -> (Neg A || B)
    --   I2: (Neg (Neg B)) -> (Neg A || B)

    -- 3. Prove I1: (Neg A) -> (Neg A || B)
    (neg_a_implies_target, _) <- runProofByAsmM (neg a_term) $ do
        -- Assume (Neg A) - this is 'neg a_term', which is proven by assumption here.
        -- We want to derive 'target_disjunction' which is (Neg A || B).
        disjIntroLM (neg a_term) b_term -- Uses the assumed (Neg A) and term B
        return () -- Subproof concludes with (Neg A || B)

    -- 4. Prove I2: (Neg (Neg B)) -> (Neg A || B)
    let not_not_b_assumption_term = neg not_b_term -- This is term Neg(Neg B)
    (not_not_b_implies_target, _) <- runProofByAsmM not_not_b_assumption_term $ do
        -- Assume (Neg (Neg B)) - this is 'not_not_b_assumption_term', proven by assumption.
        -- First, derive B using Double Negation Elimination.
        (b_proven_from_dne, _) <- doubleNegElimM not_not_b_assumption_term

        -- Now we have B (b_proven_from_dne). We want to derive (Neg A || B).
        disjIntroRM (neg a_term) b_proven_from_dne -- Uses term (Neg A) and proven B
        return () -- Subproof concludes with (Neg A || B)

    -- 5. Apply Disjunction Elimination.
    --    We have:
    --      s_or_form_proven:         (Neg A) || (Neg (Neg B))
    --      neg_a_implies_target:     (Neg A) -> (Neg A || B)
    --      not_not_b_implies_target: (Neg (Neg B)) -> (Neg A || B)
    --    The result will be (Neg A || B).
    disjElimM s_or_form_proven neg_a_implies_target not_not_b_implies_target




-- Ensure all necessary imports are present, including:
-- MetaRuleErrNotImp, MetaRuleErrNotNeg, MetaRuleErrNotAdj (or similar)
-- parse_implication, parseNeg, parseAdj, neg, (.&&.), (.->.), (.||.)
-- runProofByAsmM, contraFM, absurdM, doubleNegElimM,
-- negAndNotToOrM, disj2ImpM (the helpers we discussed)
-- And all necessary type classes and ProofGenTStd etc.

-- | Derives (A ∧ ¬B) from a proven ¬(A → B).
-- | This demonstrates one direction of the equivalence ¬(A → B) ⇔ (A ∧ ¬B).
-- | It uses previously defined helpers 'negAndNotToOrM' and 'disj2ImpM'
-- | within a proof by contradiction structure.
-- |
-- | Proof Strategy:
-- | 1. Given ¬(A → B) as 's_input'.
-- | 2. To prove (A ∧ ¬B), assume its negation ¬(A ∧ ¬B) for Reductio Ad Absurdum (RAA).
-- |    a. From the assumption ¬(A ∧ ¬B), use 'negAndNotToOrM' to derive (¬A ∨ B).
-- |    b. From (¬A ∨ B), use 'disj2ImpM' to derive (A → B).
-- |    c. Now we have derived (A → B) (from step 2b) and we were given ¬(A → B) ('s_input').
-- |       This is a contradiction, so derive False using `contraFM`.
-- | 3. The subproof (assuming ¬(A ∧ ¬B)) has led to False.
-- |    Thus, by RAA (via `absurdM`), we conclude ¬(¬(A ∧ ¬B)).
-- | 4. Apply Double Negation Elimination (`doubleNegElimM`) to get (A ∧ ¬B).
negImpToConjViaEquivM :: (SubproofRule r1 s, MonadThrow m, Monoid r1,  TypedSent o tType sE s, LogicRuleClass r1 s tType sE o,
  StdPrfPrintMonad s o tType m,  StdPrfPrintMonad s o tType (Either SomeException),  LogicSent s tType,
  Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
  Show eL, Show o, Show s, Show sE, Show tType, Typeable eL,
  Typeable o, Typeable s, Typeable sE, Typeable tType, ShowableSent s, REM.LogicRuleClass r1 s o tType sE) =>
            s -- ^ A proven proposition 's_input' of the form ¬(A → B).
            -> ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int]) -- ^ Returns the proven proposition (A ∧ ¬B) and its proof index.
negImpToConjViaEquivM s_input_neg_A_implies_B = do
    -- 1. Parse the input s_input_neg_A_implies_B = ¬(A → B) to get terms A and B.
    --    These terms are needed to construct the assumption for RAA: ¬(A ∧ ¬B).
    a_implies_b_term <- maybe (throwM $ MetaRuleErrNotNeg s_input_neg_A_implies_B)
                              return (parseNeg s_input_neg_A_implies_B)
    (a_term, b_term) <- maybe (throwM $ MetaRuleErrNotImp a_implies_b_term)
                              return (parse_implication a_implies_b_term)

    -- 2. Construct the assumption for RAA: ¬(A ∧ ¬B)
    let assumption_for_raa = neg (a_term .&&. neg b_term)

    x <- showSentM assumption_for_raa

    remarkM x

    -- 3. Start the RAA subproof: Assume ¬(A ∧ ¬B) and derive False.
    --    This will prove (¬(A ∧ ¬B) → False).
    (raa_antecedent_implies_false, _) <- runProofByAsmM assumption_for_raa $ do
        -- Inside this subproof, 'assumption_for_raa' (¬(A ∧ ¬B)) is proven by assumption.

        -- 3a. From ¬(A ∧ ¬B), derive (¬A ∨ B) using 'negAndNotToOrM'.
        (not_a_or_b_derived, _) <- negAndNotToOrM assumption_for_raa

        -- 3b. From (¬A ∨ B), derive (A → B) using 'disj2ImpM'.
        (a_implies_b_derived, _) <- disj2ImpM not_a_or_b_derived

        -- 3c. We have 'a_implies_b_derived' (A → B) and the original 's_input_neg_A_implies_B' (¬(A → B)).
        --     This is a contradiction. Derive False using `contraFM`.
        (falsity, _) <- contraFM a_implies_b_derived
        
        -- The subproof (assuming ¬(A ∧ ¬B)) concludes with 'falsity' (False).
        return ()

    -- 4. Apply AbsurdM to (¬(A ∧ ¬B) → False) to get ¬(¬(A ∧ ¬B)).
    (double_negated_target, _) <- absurdM raa_antecedent_implies_false

    -- 5. Apply Double Negation Elimination to ¬(¬(A ∧ ¬B)) to get (A ∧ ¬B).
    doubleNegElimM double_negated_target




modusTollensM :: (Monoid r1,
                  MonadThrow m, LogicSent s tType,
                Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                 Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType, TypedSent o tType sE s, StdPrfPrintMonad s o tType m,
                 REM.SubproofRule r1 s, Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                 StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o, REM.LogicRuleClass r1 s o tType sE, ShowableSent s)
    => s
    -> ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int])
modusTollensM s = do
    -- Parse (P → Q) and ¬Q from the input statement s
    (p,q) <- maybe (throwM $ MetaRuleErrNotModusTollens s) return (parse_implication s)
    let negQ = neg q


    repM s -- We are assuming P → Q is already proven in the context and we reiterate it for emphasis.
    -- Derive ¬P from ¬Q and P → Q (Modus Tollens)
    repM negQ -- We are assuming ¬Q is already proven in the context and we reiterate it for emphasis.
    (negPImpNegQ,_) <- runProofByAsmM negQ $ do

        (absurdity,_) <- runProofByAsmM p $ do
                (q,_) <- mpM s
                -- Use contraFM to derive False from q and negQ    
                contraFM q
                --False now derived
        absurdM absurdity
        -- proves ¬P
    mpM negPImpNegQ
    -- this will prove neg p

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
        contraFM p -- Derive False (⊥)

    -- Use the Absurd rule: (¬P → ⊥) ⊢ ¬¬P
    (negNegP, negNegPIdx) <- absurdM negP_imp_False
    return (negNegP, negNegPIdx)


-- | Proves an arbitrary proposition from a contradiction (Ex Falso Quodlibet).
-- | Theorem: False ⊢ P
-- |
-- | This helper function implements the principle of explosion. It takes a target
-- | proposition 'p' to be proven. It requires that the proposition 'false' has
-- | already been proven in the current proof context.
-- |
-- | The proof strategy is a standard Reductio Ad Absurdum (RAA):
-- | 1. Assume ¬P (the negation of the target).
-- | 2. Reiterate the proven 'false' into this subproof using 'repM false'.
-- | 3. The subproof concludes, having proven ¬P → False.
-- | 4. Apply 'absurdM' to get ¬¬P.
-- | 5. Apply 'doubleNegElimM' to get P.
exFalsoM :: (Monoid r1, MonadThrow m, LogicSent s tType,
                   Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                   Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType,
                   TypedSent o tType sE s, StdPrfPrintMonad s o tType m, REM.SubproofRule r1 s,
                   Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                   StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o,
                   REM.LogicRuleClass r1 s o tType sE) =>
    s -> -- ^ s_target: The arbitrary proposition 'p' to be proven.
    ProofGenTStd tType r1 s o m (s, [Int])
exFalsoM s_target = do
    (s_target_proven,idx,_) <- runProofBySubArgM $ do
        -- Step 1: Start a subproof assuming the negation of our target.
        -- This will prove (¬P → False).
        (not_p_implies_false, _) <- runProofByAsmM (neg s_target) $ do
            -- Inside this subproof, ¬P is an assumption.
            -- We assume 'false' is proven in the outer context and reiterate it.
            repM false
            return () -- The subproof concludes 'false'.

        -- Step 2: From (¬P → False), derive ¬¬P using the absurd rule (RAA).
        (not_not_p, _) <- absurdM not_p_implies_false

        -- Step 3: From ¬¬P, derive P using Double Negation Elimination.
        doubleNegElimM not_not_p
        return ()
    return (s_target_proven,idx)



 
-- | Takes P ∨ Q as an argument.
-- | For this function to succeed, the following must be already proven
-- | in the current context:
-- | 1. P ∨ Q
-- | 2. ¬Q
-- | If the required sentences are already proven then P will be derived.
-- | This is a fundamental tautology of classical logic.
disjunctiveSyllogismM :: (Monoid r1, MonadThrow m, LogicSent s tType,
                   Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                   Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType,
                   TypedSent o tType sE s, StdPrfPrintMonad s o tType m, REM.SubproofRule r1 s,
                   Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                   StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o,
                   REM.LogicRuleClass r1 s o tType sE) =>
    s -> -- ^ The proposition P ∨ Q
    ProofGenTStd tType r1 s o m (s, [Int])
disjunctiveSyllogismM pOrQ = do
    (p,q) <- maybe (throwM $ MetaRuleErrDisjSyllNotDisj pOrQ) return (parseDisj pOrQ)
    let negQ = neg q
    (result_sent, idx, _) <- runProofBySubArgM $ do
        repM pOrQ -- Re-assert P ∨ Q to emphasize that it should already be proven
        repM negQ -- Re-Assert ¬Q to emphasize that it should already be proven.
        -- Prove the goal P by using Disjunction Elimination (Proof by Cases) on P ∨ Q.
            
        -- Case 1: Assume P. The goal is to derive P.
        (p_implies_p, _) <- runProofByAsmM p $ do
            -- We assumed P, so we can reiterate it as the conclusion of this subproof.
            repM p
            return ()

        -- Case 2: Assume Q. The goal is to derive P.
        (q_implies_p, _) <- runProofByAsmM q $ do
            -- We assumed Q, but we also have ¬Q from the parent assumption.
            -- This is a contradiction.
            (falsity, _) <- contraFM q
                
            -- From the proven 'falsity', derive the target 'p' using Ex Falso Quodlibet.
            exFalsoM p
            return ()

        -- Apply Disjunction Elimination.
        -- We have proven:
        --   1. P ∨ Q
        --   2. P → P
        --   3. Q → P
        -- Therefore, we can conclude P.
        disjElimM pOrQ p_implies_p q_implies_p
        return ()
    return (result_sent, idx)






-- | From P ↔ Q, derive ¬P ↔ ¬Q 
posBicondToNegBicondM :: (Monoid r1, MonadThrow m, LogicSent s tType,
                   Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                   Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType,
                   TypedSent o tType sE s, StdPrfPrintMonad s o tType m, REM.SubproofRule r1 s,
                   Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                   StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o,
                   REM.LogicRuleClass r1 s o tType sE, ShowableSent s) =>
    s -> -- ^ The proposition P ↔ Q
    ProofGenTStd tType r1 s o m (s, [Int])
posBicondToNegBicondM s = do
    -- The goal is to prove the proposition (¬P ↔ ¬Q).
    -- We prove this by assuming the antecedent and deriving the consequent.
    (p,q) <- maybe (throwM $ MetaRuleErrNotBicond s) return (parseIff s)
    let negP = neg p
    let negQ = neg q

    repM s -- We are assuming P ↔ Q is already proven in the context and we reiterate it for emphasis.
    
    (target,subarg_idx,_) <- runProofBySubArgM $ do
        (notP_implies_notQ, _) <- runProofByAsmM negP $ do
            -- Assume ¬P.
            -- From P ↔ Q, we can derive Q → P.
            (q_implies_p, _) <- bicondElimRM s
            
            -- We have the implication Q → P and the premise ¬P.
            -- This is a direct application of Modus Tollens.
            -- modusTollensM takes Q → P and uses the proven assumption ¬P`
            -- to derive ¬Q.

            modusTollensM q_implies_p
            -- Now eliminate the double negation to get ¬Q.
            
            -- The subproof concludes ¬Q.

        -- Part B: Prove Q → P (symmetric proof)
        (notQ_implies_notP, _) <- runProofByAsmM negQ $ do
            -- Assume ¬Q.
            -- From P ↔ Q, we can derive P → Q.
            (p_implies_q, _) <- bicondElimLM s
            
            -- Apply Modus Tollens to P → Q. It uses the proven assumption ¬Q
            -- to derive ¬P.
            modusTollensM p_implies_q


            -- The subproof concludes P.
        -- Combine the two implications into the biconditional P ↔ Q.
        bicondIntroM notP_implies_notQ notQ_implies_notP
        return ()
    return (target, subarg_idx)



-- | From ¬P ↔ ¬Q, derive P ↔ Q.
negBicondToPosBicondM :: (Monoid r1, MonadThrow m, LogicSent s tType,
                   Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                   Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType,
                   TypedSent o tType sE s, StdPrfPrintMonad s o tType m, REM.SubproofRule r1 s,
                   Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                   StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o,
                   REM.LogicRuleClass r1 s o tType sE, ShowableSent s) =>
    s -> -- ^ The proposition ¬P ↔ ¬Q
    ProofGenTStd tType r1 s o m (s, [Int])
negBicondToPosBicondM s = do
    -- The goal is to derive the proposition P ↔ Q.
    -- We prove this by assuming the antecedent and deriving the consequent.
    (negP,negQ) <- maybe (throwM $ MetaRuleErrNotNegBicond s) return (parseIff s)
    p <- maybe (throwM $ MetaRuleErrNotNegBicond s) return (parseNeg negP)
    q <- maybe (throwM $ MetaRuleErrNotNegBicond s) return (parseNeg negQ)
    let negBicond = neg p .<->. neg q
    
    (target,subarg_idx,_) <- runProofBySubArgM $ do
        (posBicondPre,_) <- posBicondToNegBicondM negBicond
        (negNegP_imp_negNegQ,_) <- bicondElimLM posBicondPre
        (p_implies_q, _) <- runProofByAsmM p $ do
            -- Assume P.

            (negNegP,_) <- doubleNegIntroM p --prove ¬(¬P).
            (negNegQderived, _) <- mpM negNegP_imp_negNegQ 
            -- Now eliminate the double negation to get Q.
            doubleNegElimM negNegQderived

            -- The subproof concludes Q.

        -- Part B: Prove Q → P (symmetric proof)
        (negNegQ_imp_negNegP, _) <- bicondElimRM posBicondPre
        (q_implies_p, _) <- runProofByAsmM q $ do
            -- Assume Q.
            (negNegQ,_) <- doubleNegIntroM q --prove ¬(¬Q).
            (negNegPderived, _) <- mpM negNegQ_imp_negNegP
            -- Now eliminate the double negation to get P.
            doubleNegElimM negNegPderived

            -- The subproof concludes P.
        -- Combine the two implications into the biconditional P ↔ Q.
        bicondIntroM p_implies_q q_implies_p
        return ()
    return (target, subarg_idx)


-- | From P ∧ Q, derive both P and Q.
deconstructAdjM :: (Monoid r1, MonadThrow m, LogicSent s tType,
                   Proof eL r1 (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s,
                   Show eL, Show s, Show tType, Typeable eL, Typeable s, Typeable tType,
                   TypedSent o tType sE s, StdPrfPrintMonad s o tType m, REM.SubproofRule r1 s,
                   Show sE, Typeable sE, SubproofRule r1 s, LogicRuleClass r1 s tType sE o,
                   StdPrfPrintMonad s o tType (Either SomeException), Show o, Typeable o,
                   REM.LogicRuleClass r1 s o tType sE, ShowableSent s) =>
    s -> -- ^ The proposition ¬P ↔ ¬Q
    ProofGenTStd tType r1 s o m ((s, [Int]), (s, [Int]))
deconstructAdjM s = do
    adjunct1_data <- simpLM s
    adjunct2_data <- simpRM s
    return (adjunct1_data, adjunct2_data)

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
         let sc = checkSanity mempty frVarTypeStack constdict assumption
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
        let sc = checkSanity mempty frVarTypeStack constdict asm
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
