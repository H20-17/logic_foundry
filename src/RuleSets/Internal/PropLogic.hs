module RuleSets.Internal.PropLogic 
(
    LogicError, LogicRule(..), runProofAtomic, mpM, fakePropM, simpLM, adjM,
    runProofByAsmM, runProofBySubArgM, remarkM

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
      PrfStdContext(stepIdxPrefix, freeVarTypeStack),
      Proof,
      ProofBySubArgError,
      ProofBySubArgSchema(argPrfConsequent),
      ProofByAsmError,
      ProofByAsmSchema,
      StdPrfPrintMonad,
      PropLogicSent((.&&.), parse_implication, neg, (.||.), parseAdj),
      TypedSent(..),
      PrfStdStep(PrfStdStepStep),
      ProofStd,
      ProofGenTStd,
      monadifyProofStd,
      proofByAsm,
      proofBySubArg,
      modifyPS)
import qualified StdPatternDevel as StdP ( runProofByAsmM, runProofBySubArgM, runProofOpen )
import qualified RuleSets.RemarkLogic as REM (LogicRule(..),remarkM)
import qualified RuleSets.RemarkLogicDevel as REM(runProofAtomic)



data LogicError s sE o tType where
    LogicErrMPImplNotProven :: s-> LogicError s sE o tType
    LogicErrMPAnteNotProven :: s-> LogicError s sE o tType
    LogicErrSentenceNotImp :: s -> LogicError s sE o tType
    LogicErrSentenceNotAdj :: s -> LogicError s sE o tType
    LogicErrPrfByAsmErr :: ProofByAsmError s sE (LogicError s sE o tType) -> LogicError s sE o tType
    LogicErrPrfBySubArgErr :: ProofBySubArgError s sE (LogicError s sE o tType) -> LogicError s sE o tType
    LogicErrExclMidSanityErr :: s -> sE -> LogicError s sE o tType
    LogicErrSimpLAdjNotProven :: s -> LogicError s sE o tType
    LogicErrAdjLeftNotProven :: s -> LogicError s sE o tType
    LogicErrAdjRightNotProven :: s -> LogicError s sE o tType
    LogicErrRepOriginNotProven :: s -> LogicError s sE o tType
    LogicErrFakeSanityErr :: s -> sE -> LogicError s sE o tType
    deriving(Show)


data LogicRule tType s sE o where
    MP :: s -> LogicRule tType s sE o
    ProofByAsm :: ProofByAsmSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    ExclMid :: s -> LogicRule tType s sE o
    SimpL :: s -> LogicRule tType s sE o
    SimpR :: s -> s ->  LogicRule tType s sE o
    Adj :: s -> s -> LogicRule tType s sE o
    Rep :: s -> LogicRule tType s sE o
    PropRemark :: REM.LogicRule tType s sE o -> LogicRule tType s sE o
    FakeProp :: s -> LogicRule tType s sE o
    deriving(Show)



runProofAtomic :: (ProofStd s (LogicError s sE o tType) [LogicRule tType s sE o] o tType,
               PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
               Show o, Typeable o, Typeable tType, Show tType, StdPrfPrintMonad s o tType (Either SomeException)) =>
                            LogicRule tType s sE o -> PrfStdContext tType -> PrfStdState s o tType 
                                      -> Either (LogicError s sE o tType) (Maybe s,PrfStdStep s o tType)
runProofAtomic rule context state = 
      case rule of
        MP implication -> do
             (antecedant, conseq) <- maybe ((throwError . LogicErrSentenceNotImp) implication) return (parse_implication implication)
             impIndex <- maybe ((throwError . LogicErrMPImplNotProven) implication) return (Data.Map.lookup implication (provenSents state))
             anteIndex <- maybe ((throwError . LogicErrMPAnteNotProven) antecedant) return (Data.Map.lookup antecedant (provenSents state))
             return (Just conseq, PrfStdStepStep conseq "MP" [impIndex,anteIndex])
        ProofByAsm schema -> do
             (imp, step) <- left LogicErrPrfByAsmErr (proofByAsm schema context state)
             return (Just imp, step)
        ProofBySubArg schema -> do
             step <- left LogicErrPrfBySubArgErr (proofBySubArg schema context state)
             return (Just $ argPrfConsequent schema, step)
        ExclMid s -> do
             maybe (return ())   (throwError . LogicErrExclMidSanityErr s) (checkSanity (freeVarTypeStack context) s (fmap fst (consts state)))
             let prop = s .||. neg s
             return (Just prop,PrfStdStepStep prop "EXMID" [])
        SimpL aAndB -> do
            (a,b) <- maybe ((throwError . LogicErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . LogicErrSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (Just a, PrfStdStepStep a "SIMP_L" [aAndBIndex])
        Adj a b -> do
            leftIndex <- maybe ((throwError . LogicErrAdjLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            rightIndex <- maybe ((throwError . LogicErrAdjRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            let aAndB = a .&&. b
            return (Just aAndB, PrfStdStepStep aAndB "ADJ" [leftIndex,rightIndex])
        Rep a -> do
            originIndex <- maybe ((throwError . LogicErrRepOriginNotProven) a) return (Data.Map.lookup a (provenSents state))
            return (Just a, PrfStdStepStep a "REP" [originIndex])
        FakeProp s -> do
            maybe (return ())   (throwError . LogicErrFakeSanityErr s) (checkSanity (freeVarTypeStack context) s (fmap fst (consts state)))
            return (Just s, PrfStdStepStep s "FAKE_PROP" [])
        PropRemark rem -> do
            return (Nothing, REM.runProofAtomic rem)

             
instance (PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
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
  runProofOpen :: (PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s,
               Ord o, TypedSent o tType sE s, Typeable o, Show o, Typeable tType,
               Show tType, Monoid (PrfStdState s o tType)) =>
                 [LogicRule tType s sE o] -> 
                 PrfStdContext tType  -> PrfStdState s o tType
                        -> Either (LogicError s sE o tType) (PrfStdState s o tType, [PrfStdStep s o tType],Last s) 
    
  runProofOpen rs context oldState = foldM f (PrfStdState mempty mempty 0,[], Last Nothing) rs
        where
            f :: (PrfStdState s o tType, [PrfStdStep s o tType], Last s) -> LogicRule tType s sE o 
                     -> Either (LogicError s sE o tType) (PrfStdState s o tType, [PrfStdStep s o tType], Last s)
            f (newState,newSteps, mayLastProp) r 
                       =  fmap g (runProofAtomic r context (oldState <> newState))
               where
                   g (mayS, step) = (newState <> PrfStdState newSentDict mempty 1,
                                    newSteps <> [step], Last mayS )
                      where
                        newSentDict = maybe mempty (\s -> Data.Map.insert s newLineIndex mempty) mayS
                        newStepCount = stepCount newState + 1
                        newLineIndex = stepIdxPrefix context <> [stepCount oldState + newStepCount-1]


runProofByAsmM :: (ProofStd s (LogicError s sE o tType) [LogicRule tType s sE o] o tType, Monad m,
                       PropLogicSent s tType, MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o)
                 =>   s -> ProofGenTStd tType [LogicRule tType s sE o] s o m x
                            -> ProofGenTStd tType [LogicRule tType s sE o] s o m (s, [Int], x)
runProofByAsmM = StdP.runProofByAsmM (\schm -> [ProofByAsm schm])


runProofBySubArgM :: (ProofStd s (LogicError s sE o tType) [LogicRule tType s sE o] o tType, Monad m,
                       PropLogicSent s tType, MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o)
                 =>   ProofGenTStd tType [LogicRule tType s sE o] s o m x
                            -> ProofGenTStd tType [LogicRule tType s sE o] s o m (s, [Int], x)
runProofBySubArgM = StdP.runProofBySubArgM (\schm -> [ProofBySubArg schm])  



standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex


mpM :: (Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType))
          => s -> ProofGenTStd tType [LogicRule tType s sE o] s o m (s,[Int])
mpM impl = standardRuleM [MP impl]
      

fakePropM :: (Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType))
          => s -> ProofGenTStd tType [LogicRule tType s sE o] s o m (s,[Int])
fakePropM s = standardRuleM [FakeProp s]


simpLM :: (Monad m, Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType) ) =>
            s -> ProofGenTStd tType [LogicRule tType s sE o] s o m (s,[Int])
simpLM aAndB = standardRuleM [SimpL aAndB]


adjM :: (Monad m, Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType))
         => s -> s-> ProofGenTStd tType [LogicRule tType s sE o] s o m (s,[Int])
adjM a b = standardRuleM [Adj a b]

remarkM :: (Monad m,  Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType) )
                    => 
                     Text -> ProofGenTStd tType  [LogicRule tType s sE o] s o m [Int]
remarkM = modifyPS (fmap PropRemark) . REM.remarkM      

