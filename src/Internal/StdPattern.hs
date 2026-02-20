{-# LANGUAGE UndecidableInstances #-}


module Internal.StdPattern(
    PrfStdContext(..), PrfStdState(..), PrfStdStep(..), TestSubproofErr,
    TestSubproofMException(..), 
    ProofStd,
    TypeableTerm(..), TypedSent(..), StdPrfPrintMonadFrame(..), StdPrfPrintMonad(..),
    getTopFreeVar,
    getTopFreeVars,
    testSubproof, monadifyProofStd,
    runSubproofM,
    ProofGenTStd,
    LogicConst(..),
    newConstM,
    getFreeVarCount,
    getFreeVars,
    showTermM, showSentM,
    ShowableSent(..),
    ShowableTerm(..),
    QuantifiableTerm(..),
    printStepsFull,
    TagData(..)


) where


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
import Kernel
    ( getProofState,
      monadifyProof,
      runProofGeneratorTOpen,
      runProofGeneratorT,
      runProof,
      Proof(..),
      ProofGeneratorT,
      modifyPS )
import Control.Arrow ( left )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Reader ( MonadReader(ask) )
import Control.Monad.State ( MonadState(get) )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.Monoid ( Monoid(mempty, mappend),Last(..), Sum(..), getSum )
import IndexTracker
import Control.Monad.IO.Class(MonadIO,liftIO)



default(Text)

data PrfStdContext q s o tType t where
    PrfStdContext :: {
        freeVarTypeStack :: [q],
        stepIdxPrefix :: [Int],
        contextFrames :: [Bool],
        mayParentState :: Maybe (PrfStdState s o tType t)
    } -> PrfStdContext q s o tType t
    deriving Show


data TagData s t where
    TagDataTerm :: t -> TagData s t
    TagDataSent :: s -> TagData s t
    TagDataRemark :: TagData s t
    -- There is no data associated with a remark tag,
    -- but we want to be able to distinguish it from the other tag types.
    TagDataRawText :: Text -> TagData s t
  deriving Show


data PrfStdState s o tType t where
   PrfStdState :: {
      provenSents :: Map s [Int],
      consts :: Map o (tType, [Int]),
      stepCount :: Int,
      tagData :: Map Text (TagData s t),
      remarkTagIdxs :: Map Text [Int]
      
   } -> PrfStdState s o tType t
   deriving Show





instance Semigroup (PrfStdContext q s o tType t) where
     (<>) :: PrfStdContext q s o tType t -> PrfStdContext q s o tType t -> PrfStdContext q s o tType t
     (<>) (PrfStdContext v1 prf1 frames1 mayParentState1) 
             (PrfStdContext v2 prf2 frames2 mayParentState2) 
         =
            PrfStdContext (v1 <> v2) (prf1 <> prf2) (frames1 <> frames2) mayParentState1

instance Monoid (PrfStdContext q s o tType t) where
    mempty :: PrfStdContext q s o tType t
    mempty = PrfStdContext [] [] [] Nothing


instance (Ord s, Ord o) => Semigroup (PrfStdState s o tType t ) where
    (<>) :: PrfStdState s o tType t
              -> PrfStdState s o tType t -> PrfStdState s o tType t
    (<>) (PrfStdState proven1 consts1 count1 tagDict1 tagIdxs1) (PrfStdState proven2 consts2 count2 tagDict2 tagIdxs2)
            = PrfStdState (proven2 <> proven1) (consts1 <> consts2) (count1 + count2) (tagDict2 <> tagDict1) (tagIdxs2 <> tagIdxs1)


instance (Ord s, Ord o) => Monoid (PrfStdState s o tType t) where
     mempty :: (Ord s, Ord o) => PrfStdState s o tType t
     mempty = PrfStdState {
        provenSents = mempty,
        consts = mempty,
        stepCount = 0,
        tagData = mempty,
        remarkTagIdxs = mempty
     }






type ProofGenTStd tType r s o q t m 
               = ProofGeneratorT s [PrfStdStep s o tType t] (PrfStdContext q s o tType t) r (PrfStdState s o tType t) (Sum Int,Sum Int) m





type ProofStd s eL r o tType q t = Proof eL r (PrfStdState s o tType t) (PrfStdContext q s o tType t) [PrfStdStep s o tType t] s



data PrfStdStep s o tType t where
    PrfStdStepStep :: s -> Text -> Maybe o -> [s] -> PrfStdStep s o tType t
    PrfStdStepLemma :: s -> PrfStdStep s o tType t
    PrfStdStepConst :: o -> tType -> PrfStdStep s o tType t
    PrfStdStepTheorem :: s -> [PrfStdStep s o tType t] -> PrfStdStep s o tType t
    PrfStdStepSubproof :: s -> Text -> [PrfStdStep s o tType t] ->  PrfStdStep s o tType t
    PrfStdStepTheoremM :: s -> PrfStdStep s o tType t
    PrfStdStepFreevar :: Int -> tType -> PrfStdStep s o tType t
    PrfStdStepFakeConst :: o ->tType -> PrfStdStep s o tType t
    PrfStdStepRemark :: Text -> Maybe Text -> PrfStdStep s o tType t
    PrfStdStepTagObject :: Text -> TagData s t -> PrfStdStep s o tType t
  deriving Show


-- class MonadIO m => PrintableStdStep s o tType m where
--    printSteps :: [PrdStdStep s o tType] -> m ()


class (Eq tType, Ord o) => TypeableTerm t o tType sE q | t -> o, t ->tType, t -> sE, t -> q where
    getTypeTerm :: Map Int tType -> [q] -> Map o tType -> t -> Either sE tType
    -- get term type using a list of template variable types, a list of
    -- free variable types and a const dictionary
    const2Term :: o -> t
    free2Term :: Int -> t
    extractConstsTerm :: t -> Set o


class QuantifiableTerm q tType | q -> tType where
    qTypeToTType :: q -> tType




class LogicConst o where
    newConst :: Set o -> o

class (Ord s, Eq tType, Ord o) => TypedSent o tType sE s | s-> tType, s-> sE, s -> o where
    -- check the sanity of a sentence using a map of template variable indices to types,
    -- a list of free variable types and a const dictionary
    checkSanity :: Map Int tType -> [q] -> Map o tType -> s -> Maybe sE
    extractConstsSent :: s -> Set o





class ShowableSent s where
    showSent :: Map s [Int] -> s -> Text
    -- show a sentence using a map of proven sentences to indices, and a sentence
    -- to show. The map is used to determine hilbert shorthands for certain terms,
    -- A term introduced via the EI_hilbert rule can be identified by the index
    -- of the sentence whereby it was introduced.

class ShowableTerm s t | s -> t where
    showTerm :: Map s [Int] -> t -> Text
    -- show a term using a map of proven sentences to indices, and a term
    -- to show. The map is used to determine hilbert shorthands for certain terms,
    -- A term introduced via the EI_hilbert rule can be identified by the index
    -- of the sentence whereby it was introduced.

data TestSubproofErr s sE eL where
   TestSubproofErrResultNotSane :: s -> sE -> TestSubproofErr s sE eL
   TestSubproofErrorSubproofFailedOnErr :: eL
                                    -> TestSubproofErr s sE eL
   TestSubproofErrorNothingProved :: TestSubproofErr s sE eL                    
   TestSubproofErrorResultNotProved :: s -> TestSubproofErr s sE eL
   deriving(Show)


testSubproof :: (ProofStd s eL1 r1 o tType q t, TypedSent o tType sE s    )
                       => PrfStdContext q s o tType t -> PrfStdState s o tType t -> PrfStdState s o tType t -> 
                          [PrfStdStep s o tType t] -> Last s -> s -> r1 
                             -> Either (TestSubproofErr s sE eL1) [PrfStdStep s o tType t]
testSubproof context baseState preambleState preambleSteps mayPreambleLastProp targetProp subproof =
      --either return (const Nothing) eitherResult
      do
             let frVarTypeStack = freeVarTypeStack context
             let baseStateZero = PrfStdState {
                 provenSents = provenSents baseState,
                 consts = consts baseState,
                 stepCount = 0,
                 tagData = tagData baseState,
                 remarkTagIdxs = remarkTagIdxs baseState
             }
             let startState = baseStateZero <> preambleState
             let constdict = fmap fst (consts startState)
             let sc = checkSanity mempty frVarTypeStack constdict targetProp
             maybe (return ()) (throwError . TestSubproofErrResultNotSane targetProp) sc
             (newState,newSteps, mayLastProp) <- 
                   left TestSubproofErrorSubproofFailedOnErr (runProofOpen subproof context startState)
             let mayFinalProp = getLast $ mayPreambleLastProp <> mayLastProp
             finalProp <- maybe (throwError TestSubproofErrorNothingProved) return mayFinalProp
             let endState = preambleState <> newState
             unless (finalProp == targetProp) (throwError $ TestSubproofErrorResultNotProved targetProp)
             let finalSteps = preambleSteps <> newSteps
             return finalSteps



data TestSubproofMException s sE where
   BigExceptResNotProven :: s -> TestSubproofMException s sE
   BigExceptResultSanity :: s -> sE -> TestSubproofMException s sE
   BigExceptNothingProved :: TestSubproofMException s sE
   BigExceptEmptyVarStack :: TestSubproofMException s sE
   BigExceptNotNFreeVars :: Int -> TestSubproofMException s sE

   deriving(Show)


instance (
              Show sE, Typeable sE, 
              Show s, Typeable s)
           => Exception (TestSubproofMException s sE)




class Monad m => StdPrfPrintMonadFrame m where
    printStartFrame :: [Bool] -> m()

class (Monad m, StdPrfPrintMonadFrame m) => StdPrfPrintMonad q s o tType t m |  s -> o, s-> tType, s->q, s->t where
     printSteps :: 
           PrfStdContext q s o tType t
        ->  PrfStdState s o tType t
        -> Bool        -- printSubsteps
        -> [PrfStdStep s o tType t] --steps
        -> m ()

printStepsFull :: (StdPrfPrintMonad q s o tType t m, Ord s, Ord o) => [PrfStdStep s o tType t] -> m ()
printStepsFull = printSteps 
                   PrfStdContext {
                    freeVarTypeStack =  [],
                    stepIdxPrefix = [],
                    contextFrames = [],
                    mayParentState = Nothing

                   }
                   mempty
                   True



instance (ProofStd s eL r o tType q t, Monoid r, Monad m, StdPrfPrintMonadFrame m) 
          => StdPrfPrintMonadFrame (ProofGenTStd tType r s o q t m) where
    printStartFrame :: [Bool] -> ProofGenTStd tType r s o q t m ()
    printStartFrame contextFrames = lift $ printStartFrame contextFrames
    


instance (StdPrfPrintMonad q s o tType t m, 
          ProofStd s eL r o tType q t, 
          Monoid r, 
          StdPrfPrintMonadFrame (ProofGenTStd tType r s o q t m))
             => StdPrfPrintMonad q s o tType t (ProofGenTStd tType r s o q t m) where

  printSteps :: (StdPrfPrintMonad q s o tType t m, ProofStd s eL r o tType q t, Monoid r,
                StdPrfPrintMonadFrame (ProofGenTStd tType r s o q t m)) =>
                PrfStdContext q s o tType t
            -> PrfStdState s o tType t
            -> Bool
            -> [PrfStdStep s o tType t]
            -> ProofGenTStd tType r s o q t m ()
  printSteps context state printSubsteps steps 
     = lift $ printSteps context state printSubsteps steps







monadifyProofStd :: (MonadThrow m, ProofStd s eL r o tType q t, Monoid r,
                    Show eL, Typeable eL, StdPrfPrintMonad q s o tType t m, Ord s)
           => r -> ProofGenTStd tType r s o q t m (Maybe s)
monadifyProofStd p = do
     context <- ask
     -- PrfStdContext fvStack idx contextFrames maybeParentState <- ask
     state <- getProofState
     (addedState,steps, mayLastProp) <- monadifyProof p
     --printSteps contextFrames idx (stepCount state) (provenSents state) typelessConstDict False (Just (provenSents state, typelessConstDict, stepCount state)) steps
     printSteps context state False steps
     return mayLastProp
   where
       f state prop = Just (prop, provenSents state!prop )
          
newConstM :: (MonadThrow m, ProofStd s eL r o tType q t, Monoid r,
                    LogicConst o)
           => ProofGenTStd tType r s o q t m o
newConstM = do
    context <- ask
    state <- getProofState
    let constDict = consts state
    let constSet = keysSet constDict
    let c = newConst constSet
    return c




getTopFreeVar :: (Monoid r1, ProofStd s eL1 r1 o tType q t, Monad m,
                       Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad q s o tType t m, TypeableTerm t o tType sE q)
                 =>  ProofGenTStd tType r1 s o q t m t
getTopFreeVar =  do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        if null frVarTypeStack then throwM BigExceptEmptyVarStack
            else return (free2Term $ length frVarTypeStack - 1)


getTopFreeVars :: (Monoid r1, ProofStd s eL1 r1 o tType q t, Monad m,
                       Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad q s o tType t m, TypeableTerm t o tType sE q)
                 =>  Int -> ProofGenTStd tType r1 s o q t m [t]
getTopFreeVars n =  do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        unless (length frVarTypeStack >= n) (throwM (BigExceptNotNFreeVars n))
        let topIdx = length frVarTypeStack - 1
        let topVars = [topIdx - i | i <- [0..n-1]]
        return (fmap free2Term topVars)


getFreeVars :: (Monoid r1, ProofStd s eL1 r1 o tType q t, Monad m,
                       Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad q s o tType t m, TypeableTerm t Text tType sE q)
                 =>  ProofGenTStd tType r1 s o q t m [t]
getFreeVars = do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let stackHeight = length frVarTypeStack
        let topIdx = stackHeight - 1

        let allVars = [topIdx - i | i <- [0..stackHeight-1]]
        return (fmap free2Term allVars)

-- The types on the context freevar type stack should come out in this order (in theory): t2,t1,t0
-- where t0 is the first free variable introduced, t1 the second and so on. Everytime we enter a new
-- universal generalization context, we push a new type onto the stack.
    


getFreeVarCount :: (Monoid r1, ProofStd s eL1 r1 o tType q t, Monad m,
                        Show eL1, Typeable eL1,
                    Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                        StdPrfPrintMonad q s o tType t m)
                 =>  ProofGenTStd tType r1 s o q t m Int
getFreeVarCount = do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        return $ length frVarTypeStack



runSubproofM :: ( Monoid r1, ProofStd s eL1 r1 o tType q t, Monad m,
                        Show eL1, Typeable eL1, Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, StdPrfPrintMonad q s o tType t m )
                 =>    PrfStdContext q s o tType t -> PrfStdState s o tType t -> PrfStdState s o tType t
                          -> [PrfStdStep s o tType t] -> Last s -> ProofGenTStd tType r1 s o q t m x
                          -> (Sum Int, Sum Int)
                          ->  m (x,s,r1,[PrfStdStep s o tType t])
runSubproofM context baseState preambleState preambleSteps mayPreambleLastProp prog vIdx = do
          printStartFrame (contextFrames context)
          --let newParentStateData = case mayParentState context of
          --     Just (PrfStdState provenSents consts stepCount tagDict remTagIdxs) -> Just (provenSents, fmap snd consts, stepCount) 
          --     Nothing -> Nothing
          let baseStateZero = PrfStdState {
                 provenSents = provenSents baseState,
                 consts = consts baseState,
                 stepCount = 0,
                 tagData = tagData baseState,
                 remarkTagIdxs = remarkTagIdxs baseState
          }
          unless (Prelude.null preambleSteps) 
                 --   (printSteps (contextFrames context) (stepIdxPrefix context) 0
                 --       (provenSents baseState) (fmap snd (consts baseState)) False newParentStateData preambleSteps)
                    (printSteps context baseStateZero False preambleSteps)
          
          let startState = baseStateZero <> preambleState
          (extraData,newState,r,newSteps, mayLastProp) <- runProofGeneratorTOpen prog context startState vIdx
          let constdict = fmap fst (consts startState)
          let mayPrfResult = getLast $ mayPreambleLastProp <> mayLastProp
          prfResult <- maybe (throwM BigExceptNothingProved) return mayPrfResult
          let sc = checkSanity mempty (freeVarTypeStack context) constdict prfResult
          maybe (return ()) (throwM . BigExceptResultSanity prfResult) sc
          let endState = preambleState <> newState
          let finalSteps = preambleSteps <> newSteps
          return (extraData, prfResult, r,finalSteps)


showTermM :: (Monad m, Monoid r,
             Proof eL r (PrfStdState s o tType t) (PrfStdContext q s o tType t) [PrfStdStep s o tType t] s, ShowableTerm s t)
                     => t -> ProofGenTStd tType r s o q t m Text
showTermM obj = 
    do
      state <- getProofState
      let dict = provenSents state
      return $ showTerm dict obj

showSentM :: (Monad m, Monoid r,
             Proof eL r (PrfStdState s o tType t) (PrfStdContext q s o tType t) [PrfStdStep s o tType t] s, ShowableSent s)
                     => s -> ProofGenTStd tType r s o q t m Text
showSentM obj =
    do
      state <- getProofState
      let dict = provenSents state
      return $ showSent dict obj

      