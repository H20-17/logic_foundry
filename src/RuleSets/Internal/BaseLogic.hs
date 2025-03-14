{-# LANGUAGE UndecidableInstances #-}



module RuleSets.Internal.BaseLogic 
(
    LogicRule(..), runProofAtomic, remarkM, BaseLogRule(..), LogicError(..), fakePropM, fakeConstM,
    ProofBySubArgSchema(..), ProofBySubArgError(..), proofBySubArg, runProofBySubArgM,
    BaseLogSchemaRule(..)
) where

import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
import Data.Text (Text, unpack)
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import Data.Data (Typeable)
import Data.Map(lookup,insert)
import StdPattern
    ( PrfStdState(..),
      PrfStdContext(..),
      Proof,
      StdPrfPrintMonad,
      PropLogicSent((.&&.), parse_implication, neg, (.||.), parseAdj),
      TypedSent(..),
      PrfStdStep(..),
      ProofStd,
      ProofGenTStd,
      monadifyProofStd,
      getProofState,
      freeVarTypeStack,
      checkSanity,
      TestSubproofErr,
      testSubproof,
      RuleInject (..))
import StdPatternDevel (runProofOpen, runSubproofM )
import Control.Monad.RWS (MonadReader(ask))
import Data.Maybe ( isNothing )
import Control.Arrow (left)
import Control.Monad.Trans ( MonadTrans(lift) )

data LogicError s sE o where
    LogicErrRepOriginNotProven :: s -> LogicError s sE o
    LogicErrFakeSanityErr :: s -> sE -> LogicError s sE o
    LogicErrFakeConstDefined :: o -> LogicError s sE o
    LogicErrPrfBySubArgErr :: ProofBySubArgError s sE (LogicError s sE o) -> LogicError s sE o
    deriving (Show)

data LogicRule tType s sE o where
    Remark :: Text -> LogicRule tType s sE o
    Rep :: s -> LogicRule tType s sE o
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o]-> LogicRule tType s sE o
    FakeProp:: s -> LogicRule tType s sE o
    FakeConst :: o -> tType -> LogicRule tType s sE o
    deriving(Show)



runProofAtomic :: (Ord s, TypedSent o tType sE s,Typeable s, Show s, Typeable o, Show o,
                    Typeable tType, Show tType, StdPrfPrintMonad s o tType (Either SomeException)
                    
                     ) =>
               LogicRule tType s sE o ->  PrfStdContext tType -> PrfStdState s o tType
                -> Either (LogicError s sE o) (Maybe s, Maybe (o,tType), PrfStdStep s o tType)
runProofAtomic rule context state =
    case rule of
        Remark remark -> return (Nothing, Nothing, PrfStdStepRemark remark)
        Rep s -> do
            originIndex <- maybe ((throwError . LogicErrRepOriginNotProven) s) return (Data.Map.lookup s (provenSents state))
            return (Just s, Nothing, PrfStdStepStep s "REP" [originIndex])
        FakeProp s -> do
            maybe (return ())   (throwError . LogicErrFakeSanityErr s) (checkSanity (freeVarTypeStack context) s (fmap fst (consts state)))
            return (Just s, Nothing, PrfStdStepStep s "FAKE_PROP" [])
        FakeConst const tType -> do
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . LogicErrFakeConstDefined) const)
               return (Nothing,Just (const, tType), PrfStdStepFakeConst const tType)
        ProofBySubArg schema -> do
             step <- left LogicErrPrfBySubArgErr (proofBySubArg schema context state)
             return (Just $ argPrfConsequent schema, Nothing, step)
    where
        constDict = fmap fst (consts state)




             
instance ( Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType),
          StdPrfPrintMonad s o tType (Either SomeException),
          Monoid (PrfStdContext tType))
             => Proof (LogicError s sE o)
                 [LogicRule tType s sE o] 
                 (PrfStdState s o tType) 
                 (PrfStdContext tType)
                 [PrfStdStep s o tType]
                 s
                    where
  runProofOpen :: (Show s, Typeable s,
               Ord o, TypedSent o tType sE s, Typeable o, Show o, Typeable tType,
               Show tType, Monoid (PrfStdState s o tType)) =>
                 [LogicRule tType s sE o] -> 
                 PrfStdContext tType  -> PrfStdState s o tType
                        -> Either (LogicError s sE o) (PrfStdState s o tType, [PrfStdStep s o tType],Last s) 

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

instance RuleInject [LogicRule tType s sE o] [LogicRule tType s sE o] where
    injectRule = id




class BaseLogRule r s o tType sE | r -> s, r->o, r->tType, r -> sE where
    remark :: Text -> r
    rep :: s -> r
    fakeProp :: s -> r
    fakeConst:: o -> tType -> r
   

instance BaseLogRule [LogicRule tType s sE o] s o tType sE where
    remark :: Text -> [LogicRule tType s sE o]
    remark text = [Remark text]
    rep :: s -> [LogicRule tType s sE o]
    rep s = [Rep s]
    fakeProp :: s -> [LogicRule tType s sE o]
    fakeProp s = [FakeProp s]
    fakeConst :: o -> tType -> [LogicRule tType s sE o]
    fakeConst o t = [FakeConst o t]





instance BaseLogSchemaRule [LogicRule tType s sE o] s where
    proofBySubArgSchemaRule :: ProofBySubArgSchema s [LogicRule tType s sE o] -> [LogicRule tType s sE o]
    proofBySubArgSchemaRule schema = [ProofBySubArg schema]



data ProofBySubArgSchema s r where
   ProofBySubArgSchema :: {
                       argPrfConsequent :: s,
                       argPrfProof :: r
                    } -> ProofBySubArgSchema s r
    deriving Show



data ProofBySubArgError senttype sanityerrtype logcicerrtype where
   ProofBySubArgErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> ProofBySubArgError senttype sanityerrtype logcicerrtype
    deriving(Show)


proofBySubArg :: (ProofStd s eL1 r1 o tType,  TypedSent o tType sE s) => 
                       ProofBySubArgSchema s r1 ->  
                        PrfStdContext tType -> 
                        PrfStdState s o tType ->
                        Either (ProofBySubArgError s sE eL1) (PrfStdStep s o tType)
proofBySubArg (ProofBySubArgSchema consequent subproof) context state  =
      do
         let frVarTypeStack = freeVarTypeStack context
         let constdict = fmap fst (consts state)
         let alreadyProven = provenSents state
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames
         let newState = PrfStdState mempty mempty 0
         let preambleSteps = []
         let eitherTestResult = testSubproof newContext state newState preambleSteps (Last Nothing) consequent subproof
         finalSteps <- either (throwError . ProofBySubArgErrSubproofFailedOnErr) return eitherTestResult
         return (PrfStdStepSubproof consequent "PRF_BY_SUBARG" finalSteps)









class BaseLogSchemaRule r s where
   proofBySubArgSchemaRule :: ProofBySubArgSchema s r -> r




runProofBySubArgM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                        MonadThrow m,
                       Show s, Typeable s,
                       Show eL1, Typeable eL1, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m, BaseLogSchemaRule r1 s )
                 =>   ProofGenTStd tType r1 s o m x
                            -> ProofGenTStd tType r1 s o m (s, [Int], x)
runProofBySubArgM prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let constdict = fmap fst (consts state)
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContextFrames = contextFrames context <> [False]
        let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState mempty mempty 0
        let preambleSteps = []
        (extraData,consequent,subproof,newSteps) 
            <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) prog
        mayMonadifyRes <- (monadifyProofStd . proofBySubArgSchemaRule) (ProofBySubArgSchema consequent subproof)
        idx <- maybe (error "No theorem returned by monadifyProofStd on subarg schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (consequent, idx, extraData)



remarkM :: (Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType), BaseLogRule r s o tType sE, ProofStd s eL r o tType,
       Monoid r, Show eL, Typeable eL)
          => Text -> ProofGenTStd tType r s o m [Int]
          
remarkM txt = do
    monadifyProofStd (remark txt)
    -- The index will be that of the last step generated.
    state <- getProofState
    context <- ask
    let stepCnt = stepCount state
    let idxPrefix = stepIdxPrefix context
    let finalIdx = idxPrefix <> [stepCnt-1]
    return finalIdx  


standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex


fakePropM :: (Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType), BaseLogRule r s o tType sE, ProofStd s eL r o tType,
       Monoid r, Show eL, Typeable eL)
          => s -> ProofGenTStd tType r s o m (s,[Int])
fakePropM s = standardRuleM (fakeProp s)


fakeConstM :: (Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType), BaseLogRule r s o tType sE, ProofStd s eL r o tType,
       Monoid r, Show eL, Typeable eL)
          => o -> tType -> ProofGenTStd tType  r s o m ()
fakeConstM name tType = do
     monadifyProofStd (fakeConst name tType)
     return ()