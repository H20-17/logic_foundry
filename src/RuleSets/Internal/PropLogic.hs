module RuleSets.Internal.PropLogic 
(
    LogicError, LogicRule(..), runProofAtomic, mpM, simpLM, adjM, 
    LogicRuleClass(..), SubproofRule(..),
    ProofByAsmSchema(..), SubproofError, runProofByAsm, runProofByAsmM, LogicSent(..),
    SubproofMException(..), contraFM, absurdM
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
    LogicErrPrfByAsmErr :: SubproofError s sE (LogicError s sE o tType) -> LogicError s sE o tType
    LogicErrPrfBySubArgErr :: REM.SubproofError s sE (LogicError s sE o tType) -> LogicError s sE o tType
    LogicErrExclMidSanityErr :: s -> sE -> LogicError s sE o tType
    LogicErrSimpLAdjNotProven :: s -> LogicError s sE o tType
    LogicErrAdjLeftNotProven :: s -> LogicError s sE o tType
    LogicErrAdjRightNotProven :: s -> LogicError s sE o tType
    LogicErrRepOriginNotProven :: s -> LogicError s sE o tType
    LogicErrFakeSanityErr :: s -> sE -> LogicError s sE o tType
    LogicErrBasic :: REM.LogicError s sE o -> LogicError s sE o tType
    LogicErrContraNotProven :: s -> LogicError s sE o tType
    LogicErrAbsurdityNotProven :: s -> LogicError s sE o tType
    deriving(Show)

data LogicRule tType s sE o where
    BaseRule :: REM.LogicRule tType s sE o -> LogicRule tType s sE o
    MP :: s -> LogicRule tType s sE o
    ProofByAsm :: ProofByAsmSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ExclMid :: s -> LogicRule tType s sE o
    SimpL :: s -> LogicRule tType s sE o
    SimpR :: s -> s ->  LogicRule tType s sE o
    Adj :: s -> s -> LogicRule tType s sE o
    ContraF:: s -> LogicRule tType s sE o
    Absurd :: s -> LogicRule tType s sE o

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
        Adj a b -> do
            leftIndex <- maybe ((throwError . LogicErrAdjLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            rightIndex <- maybe ((throwError . LogicErrAdjRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            let aAndB = a .&&. b
            return (Just aAndB, Nothing, PrfStdStepStep aAndB "ADJ" [leftIndex,rightIndex])
        ContraF p -> do
            let pAndNotP = p .&&. neg p
            idx <- maybe ((throwError . LogicErrContraNotProven) pAndNotP) return (Data.Map.lookup pAndNotP (provenSents state))
            return (Just false, Nothing, PrfStdStepStep false "CONTRA" [idx])
          
        Absurd s ->do
            let sImpF = s .->. false
            idx <- maybe ((throwError . LogicErrAbsurdityNotProven) sImpF) return (Data.Map.lookup sImpF (provenSents state))
            let negation = neg s
            return (Just negation , Nothing, PrfStdStepStep negation "ABSURD" [idx])








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
    adj :: s -> s -> r
    contraF :: s -> r
    absurd :: s -> r

instance LogicRuleClass [LogicRule tType s sE o] s tType sE o where
    mp :: s -> [LogicRule tType s sE o]
    mp s = [MP s]
    exclMid :: s -> [LogicRule tType s sE o]
    exclMid s = [ExclMid s]
    simpL :: s -> [LogicRule tType s sE o]
    simpL s = [SimpL s]
    adj :: s -> s -> [LogicRule tType s sE o]
    adj a b = [Adj a b]
    contraF :: s -> [LogicRule tType s sE o]
    contraF s = [ContraF s]
    absurd :: s -> [LogicRule tType s sE o]
    absurd s = [Absurd s]




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


mpM :: (Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
       LogicRuleClass r s tType sE o, Monoid r,
       ProofStd s eL r o tType, Typeable eL, Show eL )
          => s -> ProofGenTStd tType r s o m (s,[Int])
mpM impl = standardRuleM (mp impl)
      


simpLM :: (Monad m, Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
         LogicRuleClass r s  tType sE o, Monoid r, ProofStd s eL r o tType, Typeable eL, Show eL) =>
            s -> ProofGenTStd tType r s o m (s,[Int])
simpLM aAndB = standardRuleM (simpL aAndB)


adjM :: (Monad m, Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
         LogicRuleClass r s  tType sE o, Monoid r, ProofStd s eL r o tType, Typeable eL, Show eL)
         => s -> s-> ProofGenTStd tType r s o m (s,[Int])
adjM a b = standardRuleM (adj a b)


contraFM :: (Monad m, Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
         LogicRuleClass r s  tType sE o, Monoid r, ProofStd s eL r o tType, Typeable eL, Show eL)
         => s -> ProofGenTStd tType r s o m (s,[Int])
contraFM a = standardRuleM (contraF a)


absurdM :: (Monad m, Monad m, LogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType),
         LogicRuleClass r s  tType sE o, Monoid r, ProofStd s eL r o tType, Typeable eL, Show eL)
         => s -> ProofGenTStd tType r s o m (s,[Int])
absurdM a = standardRuleM (absurd a)

 
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
                            -> ProofGenTStd tType r1 s o m (s, [Int], x)
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
        return (asm .->. consequent,idx,extraData)




class (Ord s, Eq tType) 
              => LogicSent s tType | s -> tType where
     (.&&.) :: s -> s -> s
     parseAdj :: s -> Maybe(s,s)
     (.->.) :: s->s->s
     parse_implication:: s -> Maybe (s,s)
     neg :: s -> s
     parseNeg :: s -> Maybe s
     (.||.) :: s -> s -> s
     parseDis :: s -> Maybe (s,s)
     false :: s



infixr 3 .&&.
infixr 2 .||.
infixr 0 .->.
--infixr 0 .<->.
--infix  4 .==.
--infix  4 .<-.
--infix  4 .>=.