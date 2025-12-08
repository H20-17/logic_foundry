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
    dynamicIndex


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

data PrfStdContext q s where
    PrfStdContext :: {
        freeVarTypeStack :: [q],
        stepIdxPrefix :: [Int],
        contextFrames :: [Bool]
    } -> PrfStdContext q s
    deriving Show

data PrfStdState s o tType where
   PrfStdState :: {
      provenSents :: Map s [Int],
      consts :: Map o (tType, [Int]),
      stepCount :: Int
   } -> PrfStdState s o tType
   deriving Show





instance Semigroup (PrfStdContext q s) where
     (<>) :: PrfStdContext q s -> PrfStdContext q s -> PrfStdContext q s
     (<>) (PrfStdContext v1 prf1 frames1) (PrfStdContext v2 prf2 frames2) =
            PrfStdContext (v1 <> v2) (prf1 <> prf2) (frames1 <> frames2)

instance Monoid (PrfStdContext q s) where
    mempty :: PrfStdContext q s 
    mempty = PrfStdContext [] [] []


instance (Ord s, Ord o) => Semigroup (PrfStdState s o tType ) where
    (<>) :: PrfStdState s o tType
              -> PrfStdState s o tType -> PrfStdState s o tType
    (<>) (PrfStdState proven1 consts1 count1) (PrfStdState proven2 consts2 count2)
            = PrfStdState (proven2 <> proven1) (consts1 <> consts2) (count1 + count2)


instance (Ord s, Ord o) => Monoid (PrfStdState s o tType ) where
     mempty :: (Ord s, Ord o) => PrfStdState s o tType
     mempty = PrfStdState mempty mempty 0






type ProofGenTStd tType r s o q m 
               = ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext q s) r (PrfStdState s o tType) (Sum Int) m





type ProofStd s eL r o tType q = Proof eL r (PrfStdState s o tType) (PrfStdContext q s) [PrfStdStep s o tType] s

data PrfStdStep s o tType where
    PrfStdStepStep :: s -> Text -> [[Int]] -> PrfStdStep s o tType
    PrfStdStepLemma :: s -> Maybe [Int] -> PrfStdStep s o tType
    PrfStdStepConst :: o -> tType -> Maybe [Int] -> PrfStdStep s o tType
    PrfStdStepTheorem :: s -> [PrfStdStep s o tType] -> PrfStdStep s o tType
    PrfStdStepSubproof :: s -> Text -> [PrfStdStep s o tType] ->  PrfStdStep s o tType
    PrfStdStepTheoremM :: s -> PrfStdStep s o tType
    PrfStdStepFreevar :: Int -> tType -> PrfStdStep s o tType
    PrfStdStepFakeConst :: o ->tType -> PrfStdStep s o tType
    PrfStdStepRemark :: Text -> PrfStdStep s o tType
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

dynamicIndex :: [Int] -> Text
dynamicIndex idxs = "{%I" <> Data.Text.concat (intersperse "." (Prelude.map (pack . show) idxs)) <> "%}"



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


testSubproof :: (ProofStd s eL1 r1 o tType q, TypedSent o tType sE s    )
                       => PrfStdContext q s -> PrfStdState s o tType -> PrfStdState s o tType -> 
                          [PrfStdStep s o tType] -> Last s -> s -> r1 
                             -> Either (TestSubproofErr s sE eL1) [PrfStdStep s o tType]
testSubproof context baseState preambleState preambleSteps mayPreambleLastProp targetProp subproof =
      --either return (const Nothing) eitherResult
      do
             let frVarTypeStack = freeVarTypeStack context
             let baseStateZero = PrfStdState (provenSents baseState) (consts baseState) 0
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

class (Monad m, StdPrfPrintMonadFrame m) => StdPrfPrintMonad s o tType m |  s -> o, s-> tType where
     printSteps :: [Bool] -> [Int] -> Int -> Map s [Int] -> Bool -> [PrfStdStep s o tType] -> m ()

printStepsFull :: (StdPrfPrintMonad s o tType m, Ord s) => [PrfStdStep s o tType] -> m ()
printStepsFull = printSteps [] [] 0 mempty True



instance (ProofStd s eL r o tType q, Monoid r, Monad m, StdPrfPrintMonadFrame m) 
          => StdPrfPrintMonadFrame (ProofGenTStd tType r s o q m) where
    printStartFrame :: [Bool] -> ProofGenTStd tType r s o q m ()
    printStartFrame contextFrames = lift $ printStartFrame contextFrames
    


instance (StdPrfPrintMonad s o tType m, 
          ProofStd s eL r o tType q, 
          Monoid r, 
          StdPrfPrintMonadFrame (ProofGenTStd tType r s o q m))
             => StdPrfPrintMonad s o tType (ProofGenTStd tType r s o q m) where
  printSteps :: [Bool] -> [Int] -> Int -> Map s [Int] -> Bool -> [PrfStdStep s o tType] -> ProofGenTStd tType r s o q m ()
  printSteps contextFrames idx stepStart dictMap printSubsteps steps = lift $ printSteps contextFrames idx stepStart dictMap printSubsteps steps







monadifyProofStd :: (MonadThrow m, ProofStd s eL r o tType q, Monoid r,
                    Show eL, Typeable eL, StdPrfPrintMonad s o tType m, Ord s)
           => r -> ProofGenTStd tType r s o q m (Maybe (s,[Int]))
monadifyProofStd p = do
     PrfStdContext fvStack idx contextFrames <- ask
     state <- getProofState
     (addedState,steps, mayLastProp) <- monadifyProof p
     printSteps contextFrames idx (stepCount state) (provenSents state) False steps
     let stuff = f addedState =<< mayLastProp
     return stuff
   where
       f state prop = Just (prop, provenSents state!prop )
          
newConstM :: (MonadThrow m, ProofStd s eL r o tType q, Monoid r,
                    LogicConst o)
           => ProofGenTStd tType r s o q m o
newConstM = do
    context <- ask
    state <- getProofState
    let constDict = consts state
    let constSet = keysSet constDict
    let c = newConst constSet
    return c




getTopFreeVar :: (Monoid r1, ProofStd s eL1 r1 o tType q, Monad m,
                       Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m, TypeableTerm t o tType sE q)
                 =>  ProofGenTStd tType r1 s o q m t
getTopFreeVar =  do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        if null frVarTypeStack then throwM BigExceptEmptyVarStack
            else return (free2Term $ length frVarTypeStack - 1)


getTopFreeVars :: (Monoid r1, ProofStd s eL1 r1 o tType q, Monad m,
                       Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m, TypeableTerm t o tType sE q)
                 =>  Int -> ProofGenTStd tType r1 s o q m [t]
getTopFreeVars n =  do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        unless (length frVarTypeStack >= n) (throwM (BigExceptNotNFreeVars n))
        let topIdx = length frVarTypeStack - 1
        let topVars = [topIdx - i | i <- [0..n-1]]
        return (fmap free2Term topVars)


getFreeVars :: (Monoid r1, ProofStd s eL1 r1 o tType q, Monad m,
                       Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m, TypeableTerm t Text tType sE q)
                 =>  ProofGenTStd tType r1 s o q m [t]
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
    


getFreeVarCount :: (Monoid r1, ProofStd s eL1 r1 o tType q, Monad m,
                        Show eL1, Typeable eL1,
                    Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                        StdPrfPrintMonad s o tType m)
                 =>  ProofGenTStd tType r1 s o q m Int
getFreeVarCount = do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        return $ length frVarTypeStack



runSubproofM :: ( Monoid r1, ProofStd s eL1 r1 o tType q, Monad m,
                        Show eL1, Typeable eL1, Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, StdPrfPrintMonad s o tType m )
                 =>    PrfStdContext q s -> PrfStdState s o tType -> PrfStdState s o tType
                          -> [PrfStdStep s o tType] -> Last s -> ProofGenTStd tType r1 s o q m x
                          -> Sum Int
                          ->  m (x,s,r1,[PrfStdStep s o tType])
runSubproofM context baseState preambleState preambleSteps mayPreambleLastProp prog vIdx = do
          printStartFrame (contextFrames context)


          unless (Prelude.null preambleSteps) 
                    (printSteps (contextFrames context) (stepIdxPrefix context) 0 (provenSents baseState) False preambleSteps)
          let baseStateZero = PrfStdState (provenSents baseState) (consts baseState) 0
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
             Proof eL r (PrfStdState s o tType) (PrfStdContext q s) [PrfStdStep s o tType] s, ShowableTerm s t)
                     => t -> ProofGenTStd tType r s o q m Text
showTermM obj = 
    do
      state <- getProofState
      let dict = provenSents state
      return $ showTerm dict obj

showSentM :: (Monad m, Monoid r,
             Proof eL r (PrfStdState s o tType) (PrfStdContext q s) [PrfStdStep s o tType] s, ShowableSent s)
                     => s -> ProofGenTStd tType r s o q m Text
showSentM obj =
    do
      state <- getProofState
      let dict = provenSents state
      return $ showSent dict obj

      