{-# LANGUAGE UndecidableInstances #-}
module RuleSets.Internal.RemarkLogic 
(
    LogicRule(..), runProofAtomic, remarkM,
) where

import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
import Data.Text (Text, unpack)
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import Data.Data (Typeable)

import StdPattern
    ( PrfStdState(..),
      PrfStdContext(stepIdxPrefix),
      Proof,
      StdPrfPrintMonad,
      PropLogicSent((.&&.), parse_implication, neg, (.||.), parseAdj),
      TypedSent(..),
      PrfStdStep(PrfStdStepRemark),
      ProofStd,
      ProofGenTStd,
      monadifyProofStd,
      proofByAsm,
      proofBySubArg,
      getProofState)
import StdPatternDevel as StdP (runProofOpen )
import Control.Monad.RWS (MonadReader(ask))


data LogicRule tType s sE o where
    Remark :: Text -> LogicRule tType s sE o
    deriving(Show)



runProofAtomic :: LogicRule tType s sE o -> PrfStdStep s o tType
runProofAtomic (Remark remark) = PrfStdStepRemark remark


             
instance ( Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType),
          StdPrfPrintMonad s o tType (Either SomeException),
          Monoid (PrfStdContext tType))
             => Proof ()
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
                        -> Either () (PrfStdState s o tType, [PrfStdStep s o tType],Last s) 
    
  runProofOpen rs context oldState = foldM f (PrfStdState mempty mempty 0,[], Last Nothing) rs
        where
            f :: (PrfStdState s o tType, [PrfStdStep s o tType], Last s) -> LogicRule tType s sE o
                     -> Either () (PrfStdState s o tType, [PrfStdStep s o tType], Last s)
            f (newState,newSteps, mayLastProp) r 
                       =  Right $ g (runProofAtomic r)
               where
                   g step = (newState <> PrfStdState mempty mempty 1,
                                    newSteps <> [step], Last Nothing )
                      where
                        newStepCount = stepCount newState + 1
                        newLineIndex = stepIdxPrefix context <> [stepCount oldState + newStepCount-1]






remarkM :: (Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m,
       StdPrfPrintMonad s o tType (Either SomeException), Monoid (PrfStdContext tType))
          => Text -> ProofGenTStd tType [LogicRule tType s sE o] s o m [Int]
          
remarkM txt = do
    monadifyProofStd [Remark txt]
    -- The index will be that of the last step generated.
    state <- getProofState
    context <- ask
    let stepCnt = stepCount state
    let idxPrefix = stepIdxPrefix context
    let finalIdx = idxPrefix <> [stepCnt-1]
    return finalIdx  
