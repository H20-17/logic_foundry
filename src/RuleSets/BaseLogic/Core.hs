{-# LANGUAGE UndecidableInstances #-}



module RuleSets.BaseLogic.Core
(
    LogicRule(..), runProofAtomic, LogicRuleClass(..), 
    LogicError(..),
    ProofBySubArgSchema(..), SubproofError(..), runProofBySubArg, 
    SubproofRule(..),
    HelperConstraints(..)
) where

import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless,forM )
import Data.Text (Text, unpack,null,breakOn)
import qualified Data.Text as T
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import Data.Data (Typeable)
import Data.Map(lookup,insert,singleton)

import Control.Monad.RWS (MonadReader(ask))
import Data.Maybe ( isNothing )
import Control.Arrow (left)
import Control.Monad.Trans ( MonadTrans(lift) )
import Data.Map (Map,lookup)
import Internal.StdPattern
import Kernel



data LogicError s sE o where
    LogicErrRepOriginNotProven :: s -> LogicError s sE o
    LogicErrFakeSanityErr :: s -> sE -> LogicError s sE o
    LogicErrFakeConstDefined :: o -> LogicError s sE o
    LogicErrPrfBySubArgErr :: SubproofError s sE (LogicError s sE o) -> LogicError s sE o
    LogicErrFakePropDependencyNotProven :: s -> LogicError s sE o
    deriving (Show)

data LogicRule tType s sE o q where
    Remark :: Text -> LogicRule tType s sE o q
    Rep :: s -> LogicRule tType s sE o q
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule tType s sE o q] -> LogicRule tType s sE o q
    FakeProp :: [s] -> s -> LogicRule tType s sE o q
    FakeConst :: o -> tType -> LogicRule tType s sE o q
    TagSent :: Text -> s -> LogicRule tType s sE o q
    deriving(Show)

-- Helper function to fetch proof index of a dependency
fetchProofIndexOfDependency :: (Ord s) => Map s [Int] -> s -> Either (LogicError s sE o) [Int]
fetchProofIndexOfDependency provenMap dep =
    case Data.Map.lookup dep provenMap of
        Nothing -> Left $ LogicErrFakePropDependencyNotProven dep
        Just idx -> Right idx




runProofAtomic :: (Ord s, TypedSent o tType sE s,Typeable s, Show s, Typeable o, Show o,
                    Typeable tType, Show tType, StdPrfPrintMonad q s o tType t (Either SomeException)
                    
                     ) =>
               LogicRule tType s sE o q -> PrfStdContext q s o tType t -> PrfStdState s o tType t
                -> Either (LogicError s sE o) (Maybe s, Maybe (o,tType), Maybe (Text, TagData s t), Bool, PrfStdStep s o tType t)
runProofAtomic rule context state =
    case rule of
        Remark remark -> return (Nothing, Nothing, Nothing, False, PrfStdStepRemark remark)
        Rep s -> do
            maybe ((throwError . LogicErrRepOriginNotProven) s) return (Data.Map.lookup s (provenSents state))
            return (Just s, Nothing, Nothing, False, PrfStdStepStep s "REP" Nothing [s])
        --FakeProp s -> do
        --    maybe (return ())   (throwError . LogicErrFakeSanityErr s) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state)) s)
        --    return (Just s, Nothing, PrfStdStepStep s "FAKE_PROP" [])
        FakeProp dependencies targetProp -> do
            -- Check sanity of the target proposition first
            maybe (return ()) (throwError . LogicErrFakeSanityErr targetProp) (checkSanity mempty (freeVarTypeStack context) (fmap fst (consts state)) targetProp)
            -- Check each dependency and collect their indices
            let provenMap = provenSents state
            -- Using forM (which is mapM with arguments flipped) for better flow with Either
            indices <- forM dependencies (fetchProofIndexOfDependency provenMap)

            -- If all dependencies are proven and targetProp is sane, return it
            return (Just targetProp, Nothing, Nothing, False, PrfStdStepStep targetProp "FAKE_PROP" Nothing dependencies)
        FakeConst const tType -> do
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . LogicErrFakeConstDefined) const)
               return (Nothing,Just (const, tType), Nothing, False, PrfStdStepFakeConst const tType)
        ProofBySubArg schema -> do
             step <- left LogicErrPrfBySubArgErr (runProofBySubArg schema context state)
             return (Just $ argPrfConsequent schema, Nothing, Nothing, False, step)
        TagSent tag sent -> do
            return (Nothing, Nothing, Just (tag, TagDataSent sent), True, PrfStdStepTagObject tag (TagDataSent sent))
    where
        constDict = fmap fst (consts state)




             
instance ( Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType t),
          StdPrfPrintMonad q s o tType t (Either SomeException),
          Monoid (PrfStdContext q s o tType t))
             => Proof (LogicError s sE o)
                 [LogicRule tType s sE o q] 
                 (PrfStdState s o tType t) 
                 (PrfStdContext q s o tType t)
                 [PrfStdStep s o tType t]
                 s
                    where
  runProofOpen :: (Show s, Typeable s,
               Ord o, TypedSent o tType sE s, Typeable o, Show o, Typeable tType,
               Show tType, Monoid (PrfStdState s o tType t)) =>
                 [LogicRule tType s sE o q] ->
                 PrfStdContext q s o tType t -> PrfStdState s o tType t
                        -> Either (LogicError s sE o) (PrfStdState s o tType t, [PrfStdStep s o tType t],Last s) 

  runProofOpen rs context oldState = foldM f (PrfStdState mempty mempty 0 mempty, [], Last Nothing) rs
       where
           f (newState,newSteps, mayLastProp) r =  fmap g (runProofAtomic r context (oldState <> newState))
             where
                 g ruleResult = case ruleResult of
                    (Just s,Nothing,Nothing, False, step) -> (newState <> PrfStdState (Data.Map.insert s (newLineIndex False) mempty) mempty 1 mempty,
                                         newSteps <> [step], (Last . Just) s)
                    (Just s,Just (newConst,tType), Nothing, False, step) -> (newState <> 
                            PrfStdState (Data.Map.insert s (newLineIndex False) mempty) 
                               (Data.Map.insert newConst (tType,(newLineIndex False)) mempty) 1 mempty,
                               newSteps <> [step], (Last . Just) s)
                    (Nothing,Just (newConst,tType), Nothing, False, step) -> (newState <> 
                            PrfStdState mempty
                               (Data.Map.insert newConst (tType,newLineIndex False) mempty) 1 mempty,
                               newSteps <> [step], mayLastProp)
                    (Nothing,Nothing, Nothing, False, step) -> (newState <>
                            PrfStdState mempty mempty 1 mempty,
                               newSteps <> [step], mayLastProp)
                    (Nothing, Nothing, Just (tag, tagData), True, step) -> (newState <>
                            PrfStdState {
                                provenSents = mempty,
                                consts = mempty,
                                stepCount = 0,
                                tagData = Data.Map.singleton tag tagData
                            },
                               newSteps <> [step], mayLastProp)
                    where
                        newStepCount hiddenStep = if hiddenStep then stepCount newState else stepCount newState + 1
                        newLineIndex hiddenStep = stepIdxPrefix context <> [stepCount oldState + newStepCount hiddenStep-1]

instance RuleInject [LogicRule tType s sE o q] [LogicRule tType s sE o q] where
    injectRule :: [LogicRule tType s sE o q] -> [LogicRule tType s sE o q]
    injectRule = id




class LogicRuleClass r s o tType sE | r -> s, r->o, r->tType, r -> sE where
    remark :: Text -> r
    rep :: s -> r
    fakeProp :: [s] -> s -> r
    fakeConst:: o -> tType -> r
    tagSent :: Text -> s -> r

instance LogicRuleClass [LogicRule tType s sE o q] s o tType sE where
    remark :: Text -> [LogicRule tType s sE o q]
    remark text = [Remark text]
    rep :: s -> [LogicRule tType s sE o q]
    rep s = [Rep s]
    fakeProp :: [s] -> s -> [LogicRule tType s sE o q]
    fakeProp deps s = [FakeProp deps s]
    fakeConst :: o -> tType -> [LogicRule tType s sE o q]
    fakeConst o t = [FakeConst o t]
    tagSent :: Text -> s -> [LogicRule tType s sE o q]
    tagSent tag sent = [TagSent tag sent]





instance SubproofRule [LogicRule tType s sE o q] s where
    proofBySubArg :: s -> [LogicRule tType s sE o q] -> [LogicRule tType s sE o q]
    proofBySubArg s r = [ProofBySubArg $ ProofBySubArgSchema s r]



data ProofBySubArgSchema s r where
   ProofBySubArgSchema :: {
                       argPrfConsequent :: s,
                       argPrfProof :: r
                    } -> ProofBySubArgSchema s r
    deriving Show



data SubproofError senttype sanityerrtype logcicerrtype where
   ProofBySubArgErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> SubproofError senttype sanityerrtype logcicerrtype
    deriving(Show)


runProofBySubArg :: (ProofStd s eL1 r1 o tType q t,  TypedSent o tType sE s) => 
                       ProofBySubArgSchema s r1 ->  
                        PrfStdContext q s o tType t -> 
                        PrfStdState s o tType t ->
                        Either (SubproofError s sE eL1) (PrfStdStep s o tType t)
runProofBySubArg (ProofBySubArgSchema consequent subproof) context state  =
      do
         let frVarTypeStack = freeVarTypeStack context
         let constdict = fmap fst (consts state)
         let alreadyProven = provenSents state
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames (Just state)
         let newState = PrfStdState mempty mempty 0 mempty
         let preambleSteps = []
         let eitherTestResult = testSubproof newContext state newState preambleSteps (Last Nothing) consequent subproof
         finalSteps <- either (throwError . ProofBySubArgErrSubproofFailedOnErr) return eitherTestResult
         return (PrfStdStepSubproof consequent "PRF_BY_SUBARG" finalSteps)





class SubproofRule r s where
   proofBySubArg :: s -> r -> r


type HelperConstraints r s o tType sE eL q t m = (Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType t), StdPrfPrintMonad q s o tType t m, ShowableSent s,
       StdPrfPrintMonad q s o tType t (Either SomeException), Monoid (PrfStdContext q s o tType t), LogicRuleClass r s o tType sE, ProofStd s eL r o tType q t,
       Monoid r, Show eL, Typeable eL, SubproofRule r s)