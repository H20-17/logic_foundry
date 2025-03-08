module RuleSets.Internal.PredLogic 
(
    LogicError(..), LogicRule(..), fakePropM, fakeConstM, mp, fakeProp,
    simpL, adj, runProofAtomic, uiM, eiM,
    propRuleM, mpM, simpLM, adjM, runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM,
    remarkM
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
import Data.Maybe ( isNothing )
import StdPattern
    ( PrfStdState(..),
      PrfStdContext(stepIdxPrefix, freeVarTypeStack),
      Proof,
      modifyPS,
      ProofByUGError,
      PredLogicSent(..),
      ProofByUGSchema,
      ProofBySubArgError,
      ProofBySubArgSchema(argPrfConsequent),
      ProofByAsmError,
      ProofByAsmSchema,
      EstTmMError,
      StdPrfPrintMonad,
      TmSchemaSilentM,
      ChkTheoremError,
      TheoremSchema(theorem),
      TypedSent,
      TypeableTerm(getTypeTerm, const2Term),
      PrfStdStep(PrfStdStepFakeConst, PrfStdStepStep),
      ProofStd,
      ProofGenTStd,
      establishTheorem,
      monadifyProofStd,
      establishTmSilentM,
      proofByAsm,
      proofBySubArg,
      proofByUG, TheoremSchemaMT )
import qualified StdPatternDevel as StdP(runProofBySubArgM, runProofByAsmM, runTheoremM, runTmSilentM, runProofByUGM,
                                        runProofOpen)
import qualified RuleSets.PropLogic as PL
import qualified RuleSets.PropLogicDevel as PL


data LogicError s sE o t tType where
    LogicErrPrfByAsm :: ProofByAsmError s sE (LogicError s sE o t tType) -> LogicError s sE o t tType
    LogicErrPrfBySubArg :: ProofBySubArgError s sE (LogicError s sE o t tType ) -> LogicError s sE o t tType 
    LogicErrTheorem :: ChkTheoremError s sE (LogicError s sE o t tType ) o tType -> LogicError s sE o t tType 
    LogicErrTheoremM :: EstTmMError s o tType -> LogicError s sE o t tType 
    LogicErrPL ::  PL.LogicError s sE o tType -> LogicError s sE o t tType 
    LogicErrUG :: ProofByUGError s sE  (LogicError s sE o t tType ) -> LogicError s sE o t tType 
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
    LogicErrFakeConstDefined :: o -> LogicError s sE o t tType 
   deriving (Show)

data LogicRule s sE o t tType  where
   -- t is a term
    PropRule :: PL.LogicRule tType s sE o -> LogicRule s sE o t tType 
    ProofByAsm :: ProofByAsmSchema s [LogicRule s sE o t tType ] -> LogicRule s sE o t tType 
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule s sE o t tType ] -> LogicRule s sE o t tType 
    ProofByUG :: ProofByUGSchema s [LogicRule s sE o t tType ] -> LogicRule s sE o t tType 
    EI :: s -> o -> LogicRule s sE o t tType 
       -- sentence of form E x . P, and a constant
    EG :: t -> s -> LogicRule s sE o t tType 
        -- a free term,
        -- a sentence of the form E x . P
        -- Instantiate s using term t,
        -- If the resulting sentence is already proven, then the generalization is OK, and that is sentence s.BErrAsmSanity
    UI :: t -> s -> LogicRule s sE o t tType 

    Theorem :: TheoremSchema s [LogicRule s sE o t tType ] o tType -> LogicRule s sE o t tType 
    TheoremM :: TmSchemaSilentM tType [LogicRule s sE o t tType ] s o () -> 
                             LogicRule s sE o t tType 
    FakeConst :: o -> tType -> LogicRule s sE o t tType 
    deriving(Show)






fakeConstM :: (Monad m, PredLogicSent s t tType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                        => o -> tType -> ProofGenTStd tType  [LogicRule s sE o t tType] s o m ()
fakeConstM name tType = do
     monadifyProofStd [FakeConst name tType]
     return ()


mp :: s -> LogicRule s sE o t tType 
mp a = PropRule  (PL.MP a)



fakeProp :: s -> LogicRule s sE o t tType 
fakeProp a = PropRule (PL.FakeProp a)


simpL :: s -> LogicRule s sE o t tType 
simpL a = PropRule  (PL.SimpL a)
adj :: s -> s -> LogicRule s sE o t tType 
adj a b = PropRule  (PL.Adj a b)


runProofAtomic :: (PredLogicSent s t tType ,
               ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType ] o tType,
               Show sE, Typeable sE, Show s, Typeable s, TypeableTerm t o tType sE, TypedSent o tType sE s,
               Typeable o, Show o,Typeable tType, Show tType, Show t, Typeable t,
               StdPrfPrintMonad s o tType (Either SomeException)) =>
                            LogicRule s sE o t tType  ->
                            PrfStdContext tType -> 
                            PrfStdState s o tType -> 
                            Either (LogicError s sE o t tType ) (Maybe s,Maybe (o,tType),PrfStdStep s o tType)
runProofAtomic rule context state  = 
      case rule of
          PropRule propR -> do
               (maySent,step) <- left  LogicErrPL (PL.runProofAtomic propR context state)
               return (maySent, Nothing, step)
          ProofByAsm schema -> do
               (implication,step) <- left LogicErrPrfByAsm (proofByAsm schema context state)
               return (Just implication, Nothing, step)
          ProofBySubArg schema -> do
               step <- left LogicErrPrfBySubArg (proofBySubArg schema context state)
               return (Just $ argPrfConsequent schema, Nothing, step)
          Theorem schema -> do
               step <- left LogicErrTheorem (establishTheorem schema context state)
               return (Just $ theorem schema, Nothing, step)
          TheoremM schema -> do
               (theorem,step) <- left LogicErrTheoremM (establishTmSilentM schema context state)
               return (Just theorem,Nothing, step)
          ProofByUG schema -> do
               (generalized,step) <- left LogicErrUG (proofByUG schema context state)
               return (Just generalized,Nothing, step)
          EI existsSent const -> do 
               let mayExistsParse = parseExists existsSent
               (f,tType) <- maybe ((throwError . LogicErrEINotExists) existsSent) return mayExistsParse
               let mayExistsSentIdx = Data.Map.lookup existsSent (provenSents state)
               existsSentIdx <- maybe ((throwError . LogicErrEINotProven) existsSent) return mayExistsSentIdx
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . LogicErrEIConstDefined) const)
               let eIResultSent = (f . const2Term) const
               return (Just eIResultSent,Just (const,tType), PrfStdStepStep eIResultSent "EI" [existsSentIdx])
          EG term generalization -> do
               let eitherTermType = getTypeTerm term varStack constDict
               termType <- left PredProofTermSanity eitherTermType
               let mayParse = parseExists generalization
               (f,tType) <- maybe ((throwError . LogicErrEGNotExists) generalization) return mayParse
               unless (tType == termType) ((throwError .  LogicErrEGTermTypeMismatch term termType) generalization)
               let sourceSent = f term
               let maySourceSentIdx = Data.Map.lookup sourceSent (provenSents state)
               sourceSentIdx <- maybe ((throwError . LogicErrEGNotGeneralization term) generalization) return maySourceSentIdx
               return (Just generalization,Nothing, PrfStdStepStep sourceSent "EG" [sourceSentIdx])
          UI term forallSent -> do
               let mayForallSentIdx = Data.Map.lookup forallSent (provenSents state)
               forallSentIdx <- maybe ((throwError . LogicErrUINotProven) forallSent) return mayForallSentIdx
               let mayForallParse = parseForall forallSent
               (f,tType) <- maybe ((throwError . LogicErrUINotForall) forallSent) return mayForallParse
               let eitherTermType = getTypeTerm term varStack constDict
               termType <- left PredProofTermSanity eitherTermType
               unless (tType == termType) ((throwError .  LogicErrUITermTypeMismatch term termType forallSent) tType)
               return (Just $ f term,Nothing, PrfStdStepStep (f term) "UI" [forallSentIdx])
          FakeConst const tType -> do
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . LogicErrFakeConstDefined) const)
               return (Nothing,Just (const, tType), PrfStdStepFakeConst const tType)
    where
        proven = (keysSet . provenSents) state
        constDict = fmap fst (consts state)
        varStack = freeVarTypeStack context




instance (PredLogicSent s t tType, Show sE, Typeable sE, Show s, Typeable s, TypedSent o tType sE s,
             TypeableTerm t o tType sE, Typeable o, Show o, Typeable tType, Show tType,
             Monoid (PrfStdState s o tType), Show t, Typeable t,
             StdPrfPrintMonad s o tType (Either SomeException),
             Monoid (PrfStdContext tType)) 
          => Proof (LogicError s sE o t tType ) 
             [LogicRule s sE o t tType ] 
             (PrfStdState s o tType) 
             (PrfStdContext tType)
             [PrfStdStep s o tType]
               s 
                 where

    runProofOpen :: (PredLogicSent s t tType , Show sE, Typeable sE, Show s, Typeable s,
                 TypedSent o tType sE s, TypeableTerm t o tType sE, Typeable o,
                 Show o, Typeable tType, Show tType) =>
                    [LogicRule s sE o t tType ]
                     -> PrfStdContext tType 
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





runProofByAsmM :: (ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType ] o tType, Monad m,
                       PredLogicSent s t tType , MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o,
                       Typeable t, Show t)
                 =>   s -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m x
                            -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s, [Int], x)
runProofByAsmM = StdP.runProofByAsmM (\schm -> [ProofByAsm schm])


runProofBySubArgM :: (ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType ] o tType, Monad m,
                       PredLogicSent s t tType , MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o,
                       Typeable t, Show t)
                 =>   ProofGenTStd tType [LogicRule s sE o t tType ] s o m x
                            -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s, [Int], x)
runProofBySubArgM = StdP.runProofBySubArgM (\schm -> [ProofBySubArg schm])

runTheoremM :: (ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType ] o tType, Monad m,
                       PredLogicSent s t tType , MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o,
                       Typeable t, Show t)
                 =>   TheoremSchemaMT tType [LogicRule s sE o t tType ] s o m x
                            -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s, [Int], x)
runTheoremM = StdP.runTheoremM (\schm -> [Theorem schm])

runTmSilentM :: (ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType ] o tType, Monad m,
                       PredLogicSent s t tType , MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o,
                       Typeable t, Show t, StdPrfPrintMonad s o tType (Either SomeException))
                 =>   TmSchemaSilentM tType [LogicRule s sE o t tType ] s o x
                            -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s, [Int], x)
runTmSilentM = StdP.runTmSilentM (\schm -> [TheoremM schm])

runProofByUGM :: (ProofStd s (LogicError s sE o t tType ) [LogicRule s sE o t tType ] o tType, Monad m,
                       PredLogicSent s t tType , MonadThrow m,
                       Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, Typeable tType, Show tType, Show o, Typeable o,
                       Typeable t, Show t)
                 =>   tType -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m x
                            -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s, [Int], x)
runProofByUGM tt = StdP.runProofByUGM tt (\schm -> [ProofByUG schm])   


standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex




uiM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
               StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                   => t -> s -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s,[Int])
uiM term sent = standardRuleM [UI term sent]




eiM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m,
                StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType)        )
                   => s -> o -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s,[Int])
eiM sent const = standardRuleM [EI sent const]


propRuleM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                    => ProofGenTStd tType  [PL.LogicRule tType s sE o] s o m x ->
                     ProofGenTStd tType  [LogicRule s sE o t tType ] s o m x
propRuleM = modifyPS (fmap PropRule)         

mpM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                   => s -> ProofGenTStd tType  [LogicRule s sE o t tType ] s o m (s,[Int])
mpM = propRuleM . PL.mpM

simpLM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException),
                 Monoid (PrfStdContext tType)        )
                   => s -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s,[Int])
simpLM = propRuleM . PL.simpLM

adjM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m,
                StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                   => s -> s -> ProofGenTStd tType [LogicRule s sE o t tType ] s o m (s,[Int])
adjM a b = propRuleM $ PL.adjM a b

fakePropM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                   => s -> ProofGenTStd tType  [LogicRule s sE o t tType ] s o m (s,[Int])
fakePropM = propRuleM . PL.fakePropM

remarkM :: (Monad m, PredLogicSent s t tType , TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException), 
                Monoid (PrfStdContext tType)        )
                   => Text -> ProofGenTStd tType  [LogicRule s sE o t tType ] s o m [Int]
remarkM = propRuleM . PL.remarkM
