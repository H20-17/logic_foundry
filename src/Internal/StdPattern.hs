{-# LANGUAGE UndecidableInstances #-}


module Internal.StdPattern(
    PrfStdContext(..), PrfStdState(..), PrfStdStep(..), TestSubproofErr, TheoremSchema(..), TheoremSchemaMT(..), BigException, ChkTheoremError, EstTmMError, ExpTmMError,
    ProofByAsmSchema(..), ProofByAsmError,  ProofByUGSchema(..), ProofByUGError,
    ProofGenTStd, ProofStd, TmSchemaSilentM,
    TypeableTerm(..), TypedSent(..), PropLogicSent(..), PredLogicSent(..), StdPrfPrintMonadFrame(..), StdPrfPrintMonad(..),
    checkTheorem, establishTheorem, constDictTest, testSubproof, monadifyProofStd,
    checkTheoremM, establishTmSilentM, expandTheoremM, proofByAsm, proofByUG,
    runTheoremM, runTmSilentM, runProofByAsmM,  runProofByUGM,getTopFreeVar,
    PredLogSchemaRule (..), PropLogSchemaRule(..), runSubproofM, RuleInject(..)

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
import Data.Monoid ( Monoid(mempty, mappend),Last(..) )

default(Text)

data PrfStdContext tType where
    PrfStdContext :: {
        freeVarTypeStack :: [tType],
        stepIdxPrefix :: [Int],
        contextFrames :: [Bool]
        -- Because theorems are self-contained, it makes sense to use a thick box frame for a theorem, and a thin frame from every other
        -- type of context. When contextFrames !! i is False this means use a thin box frame. Otherwise, if True that means that the context
        -- is the outermost context of a theorem so we should use a thick box frame. 
    } -> PrfStdContext tType
    deriving Show

data PrfStdState s o tType where
   PrfStdState :: {
      provenSents :: Map s [Int],
      consts :: Map o (tType, [Int]),
      stepCount :: Int 
   } -> PrfStdState s o tType
   deriving Show

instance Semigroup (PrfStdContext tType) where
     (<>) :: PrfStdContext tType -> PrfStdContext tType -> PrfStdContext tType
     (<>) (PrfStdContext v1 prf1 frames1) (PrfStdContext v2 prf2 frames2) =
            PrfStdContext (v1 <> v2) (prf1 <> prf2) (frames1 <> frames2)

instance Monoid (PrfStdContext tType) where
    mempty :: PrfStdContext tType
    mempty = PrfStdContext [] [] []


instance (Ord s, Ord o) => Semigroup (PrfStdState s o tType ) where
    (<>) :: PrfStdState s o tType
              -> PrfStdState s o tType -> PrfStdState s o tType
    (<>) (PrfStdState proven1 consts1 count1) (PrfStdState proven2 consts2 count2)
            = PrfStdState (proven1 <> proven2) (consts1 <> consts2) (count1 + count2)


instance (Ord s, Ord o) => Monoid (PrfStdState s o tType ) where
     mempty :: (Ord s, Ord o) => PrfStdState s o tType
     mempty = PrfStdState mempty mempty 0



type ProofGenTStd tType r s o m 
               = ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r (PrfStdState s o tType) m








type ProofStd s eL r o tType = Proof eL r (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType] s

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




class (Eq tType, Ord o) => TypeableTerm t o tType sE | t -> o, t ->tType, t -> sE where
    getTypeTerm :: t -> [tType] -> Map o tType -> Either sE tType
    -- get term type using a varstack and a const dictionary
    const2Term :: o -> t
    free2Term :: Int -> t
        



class (Ord s, Eq tType, Ord o) => TypedSent o tType sE s | s-> tType, s-> sE, s -> o where
    checkSanity :: [tType] -> s -> Map o tType -> Maybe sE

class (Ord s, Eq tType) 
              => PropLogicSent s tType | s -> tType where
     (.&&.) :: s -> s -> s
     parseAdj :: s -> Maybe(s,s)
     (.->.) :: s->s->s
     parse_implication:: s -> Maybe (s,s)
     neg :: s -> s
     parseNeg :: s -> Maybe s
     (.||.) :: s -> s -> s
     parseDis :: s -> Maybe (s,s)

infixr 3 .&&.
infixr 2 .||.
infixr 0 .->.
--infixr 0 .<->.
--infix  4 .==.
--infix  4 .<-.
--infix  4 .>=.


data TestSubproofErr senttype sanityerrtype logicerrtype where
   TestSubproofErrResultNotSane :: senttype -> sanityerrtype -> TestSubproofErr senttype sanityerrtype logicerrtype
   TestSubproofErrorSubproofFailedOnErr :: logicerrtype
                                    -> TestSubproofErr senttype sanityerrtype logicerrtype
   TestSubproofErrorNothingProved :: TestSubproofErr senttype sanityerrtype logicerrtype                          
   TestSubproofErrorResultNotProved :: senttype -> TestSubproofErr senttype sanityerrtype logicerrtype
   deriving(Show)


testSubproof :: (ProofStd s eL1 r1 o tType, TypedSent o tType sE s    )
                       => PrfStdContext tType -> PrfStdState s o tType -> PrfStdState s o tType -> 
                          [PrfStdStep s o tType] -> Last s -> s -> r1 
                             -> Either (TestSubproofErr s sE eL1) [PrfStdStep s o tType]
testSubproof context baseState preambleState preambleSteps mayPreambleLastProp targetProp subproof =
      --either return (const Nothing) eitherResult
      do
             let frVarTypeStack = freeVarTypeStack context
             let baseStateZero = PrfStdState (provenSents baseState) (consts baseState) 0
             let startState = baseStateZero <> preambleState
             let constdict = fmap fst (consts startState)
             let sc = checkSanity frVarTypeStack targetProp constdict
             maybe (return ()) (throwError . TestSubproofErrResultNotSane targetProp) sc
             (newState,newSteps, mayLastProp) <- 
                   left TestSubproofErrorSubproofFailedOnErr (runProofOpen subproof context startState)
             let mayFinalProp = getLast $ mayPreambleLastProp <> mayLastProp
             finalProp <- maybe (throwError TestSubproofErrorNothingProved) return mayFinalProp
             let endState = preambleState <> newState
             unless (finalProp == targetProp) (throwError $ TestSubproofErrorResultNotProved targetProp)
             let finalSteps = preambleSteps <> newSteps
             return finalSteps


data TheoremSchema s r o tType where
   TheoremSchema :: {
                       constDict :: [(o,tType)],
                       lemmas :: [s],
                       theorem :: s,
                       theoremProof :: r               
                    } -> TheoremSchema s r o tType
    deriving Show





constDictTest :: (Ord o, Eq tType) => Map o tType -> Map o tType ->  Maybe (o, Maybe (tType,tType))
constDictTest envDict = Data.Map.foldrWithKey f Nothing
     where         
         f k aVal Nothing = case Data.Map.lookup k envDict of
                                              Just bVal -> if 
                                                              aVal /= bVal 
                                                           then
                                                              Just (k,Just (aVal,bVal))
                                                           else
                                                               Nothing -- we good
                                              Nothing -> Just (k,Nothing)
         f k aVal (Just x) = Just x



data ChkTheoremError senttype sanityerrtype logcicerrtype o tType where
   ChkTheoremErrLemmaNotEstablished :: senttype -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrLemmaSanity :: senttype -> sanityerrtype -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   --The lemma is insane or not closed
   ChkTheoremErrSubproofErr :: TestSubproofErr senttype sanityerrtype logcicerrtype -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrConstNotDefd :: o -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrConstTypeConflict :: o -> tType -> tType -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   ChkTheoremErrSchemaDupConst :: o -> ChkTheoremError senttype sanityerrtype logcicerrtype o tType
   deriving(Show)


assignSequentialSet :: Ord s => Int -> [s] -> (Int, Map s [Int])
assignSequentialSet base ls = Prelude.foldr (\el (i, m) -> 
    (i + 1, Data.Map.insert el [length ls + base - i] m)) (base, mempty) ls



assignSequentialMap :: Ord o => Int -> [(o,tType)] -> Either o (Int,Map o (tType,[Int]))
assignSequentialMap base ls = Prelude.foldr f (Right (base,mempty)) ls
   where 
      f (k, v) foldObj = case foldObj of
                           Left o -> Left o
                           Right (count,m) ->
                             case Data.Map.lookup k m of
                                Nothing -> Right (count+1, Data.Map.insert k (v,[length ls + base - count]) m)
                                Just _ -> Left k


checkTheoremOpen :: (ProofStd s eL1 r1 o tType, TypedSent o tType sE s    )
                            => Maybe (PrfStdState s o tType,PrfStdContext tType) -> TheoremSchema s r1 o tType 
                                       -> Either (ChkTheoremError s sE eL1 o tType) [PrfStdStep s o tType]
                                       
checkTheoremOpen mayPrStateCxt (TheoremSchema constdict lemmas theorem subproof)  =
  do
       let eitherConstDictMap = assignSequentialMap 0 constdict
       (newStepCountA, newConsts) <- either (throwError . ChkTheoremErrSchemaDupConst) return eitherConstDictMap
       let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
       let constdictPure = Data.Map.map fst newConsts
       maybe (return ()) throwError (maybe (g1 constdictPure) (g2 constdictPure) mayPrStateCxt)
       let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
       let newState = PrfStdState newProven newConsts newStepCountB
       let preambleSteps = conststeps <> lemmasteps
       let mayPreambleLastProp = if Prelude.null lemmas then Last Nothing else (Last . Just . last) lemmas  
       left ChkTheoremErrSubproofErr (
                                      testSubproof newContext mempty newState preambleSteps mayPreambleLastProp theorem subproof)
      where
         conststeps = Prelude.foldr h1 [] constdict
         lemmasteps = Prelude.foldr h2 [] lemmas
         h1 (const,constType) accumList =  PrfStdStepConst const constType (q mayPrStateCxt) : accumList
            where
                 q Nothing = Nothing
                 q (Just (state,_)) = fmap snd (Data.Map.lookup const (consts state)) 
         h2 lemma accumList = PrfStdStepLemma lemma (q mayPrStateCxt) : accumList
            where
                 q Nothing = Nothing
                 q (Just (state,_)) = Data.Map.lookup lemma (provenSents state) 

         g2 constdictPure (PrfStdState alreadyProven alreadyDefinedConsts stepCount, 
                 PrfStdContext freeVarTypeStack stepIdfPrefix contextDepth) 
               = fmap constDictErr (constDictTest (fmap fst alreadyDefinedConsts) constdictPure)
                                               <|> Prelude.foldr f1 Nothing lemmas
           where
             constDictErr (k,Nothing) = ChkTheoremErrConstNotDefd k
             constDictErr (k, Just (a,b)) = ChkTheoremErrConstTypeConflict k a b
             f1 a = maybe (maybeLemmaMissing <|> maybeLemmaInsane) Just 
               where
                  maybeLemmaMissing = if not (a `Set.member` Data.Map.keysSet alreadyProven)
                                          then (Just . ChkTheoremErrLemmaNotEstablished) a else Nothing
                  maybeLemmaInsane = fmap (ChkTheoremErrLemmaSanity a) (checkSanity mempty a constdictPure)
         g1 constdictPure = Prelude.foldr f1 Nothing lemmas
           where
             f1 a = maybe maybeLemmaInsane Just 
               where
                  maybeLemmaInsane = fmap (ChkTheoremErrLemmaSanity a) (checkSanity mempty a constdictPure)

checkTheorem :: (ProofStd s eL1 r1 o tType, TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType
                                       -> Either (ChkTheoremError s sE eL1 o tType) [PrfStdStep s o tType]
checkTheorem  = checkTheoremOpen Nothing


establishTheorem :: (ProofStd s eL1 r1 o tType,  TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType -> PrfStdContext tType -> PrfStdState s o tType 
                                       -> Either (ChkTheoremError s sE eL1 o tType) (PrfStdStep s o tType)
establishTheorem schema context state = do
    steps <- checkTheoremOpen (Just (state,context)) schema
    let tm = theorem schema
    return (PrfStdStepTheorem tm steps)




data TheoremSchemaMT tType r s o m x where
   TheoremSchemaMT :: {
                       constDictM :: [(o,tType)],
                       lemmasM :: [s],
                       proofM :: ProofGenTStd tType r s o m x

                     } -> TheoremSchemaMT tType r s o m x


instance (Show s, Show o, Show tType) => Show (TheoremSchemaMT tType r s o m x) where
    show :: (Show s, Show o, Show tType) => TheoremSchemaMT tType r s o m x -> String
    show (TheoremSchemaMT constDict ls prog) =
        "TheoremSchemaMT " <> show ls <> " <<Monadic subproof>> " <> show constDict


-- TheoremSchemaM

type TmSchemaSilentM tType r s o x = TheoremSchemaMT tType r s o (Either SomeException) x

data BigException s sE o tType where
   BigExceptLemmaSanityErr :: s -> sE -> BigException s sE o tType
   BigExceptResNotProven :: s -> BigException s sE o tType
   BigExceptResultSanity :: s -> sE -> BigException s sE o tType
   BigExceptConstNotDefd :: o ->  BigException s sE o tType
   BigExceptConstTypeConflict :: o -> tType -> tType -> BigException s sE o tType
   BigExceptLemmaNotEstablished :: s -> BigException s sE o tType
   BigExceptAsmSanity :: s -> sE -> BigException s sE o tType
   BigExceptSchemaConstDup :: o -> BigException s sE o tType
   BigExceptNothingProved :: BigException s sE o tType
   BigExceptEmptyVarStack :: BigException s sE o tType


   deriving(Show)


instance (
              Show sE, Typeable sE, 
              Show s, Typeable s,
              Show o, Typeable o,
              Show tType, Typeable tType)
           => Exception (BigException s sE o tType)




class Monad m => StdPrfPrintMonadFrame m where
    printStartFrame :: [Bool] -> m()

class (Monad m, StdPrfPrintMonadFrame m) => StdPrfPrintMonad s o tType m |  s -> o, s-> tType where
     printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep s o tType] -> m ()





instance (ProofStd s eL r o tType, Monoid r, Monad m, StdPrfPrintMonadFrame m) 
          => StdPrfPrintMonadFrame (ProofGenTStd tType r s o m) where
    printStartFrame :: [Bool] -> ProofGenTStd tType r s o m ()
    printStartFrame contextFrames = lift $ printStartFrame contextFrames
    


instance (StdPrfPrintMonad s o tType m, 
          ProofStd s eL r o tType, 
          Monoid r, 
          StdPrfPrintMonadFrame (ProofGenTStd tType r s o m))
             => StdPrfPrintMonad s o tType (ProofGenTStd tType r s o m) where
  printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep s o tType] -> ProofGenTStd tType r s o m ()
  printSteps contextFrames idx stepStart steps = lift $ printSteps contextFrames idx stepStart steps







monadifyProofStd :: (MonadThrow m, ProofStd s eL r o tType, Monoid r,
                    Show eL, Typeable eL, StdPrfPrintMonad s o tType m, Ord s)
           => r -> ProofGenTStd tType r s o m (Maybe (s,[Int]))
monadifyProofStd p = do
     PrfStdContext fvStack idx contextFrames <- ask
     state <- getProofState
     (addedState,steps, mayLastProp) <- monadifyProof p
     printSteps contextFrames idx (stepCount state) steps
     let stuff = f addedState =<< mayLastProp
     return stuff
   where
       f state prop = Just (prop, provenSents state!prop )
          
       

checkTheoremMOpen :: (Show s, Typeable s, Monoid r1, ProofStd s eL1 r1 o tType, Monad m, MonadThrow m,
                      TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType,
                      Show eL1, Typeable eL1,
                      Typeable o, Show o, StdPrfPrintMonad s o tType m )
                 =>  Maybe (PrfStdState s o tType,PrfStdContext tType) ->  TheoremSchemaMT tType r1 s o m x
                              -> m (s, r1, x, [PrfStdStep s o tType])
checkTheoremMOpen mayPrStateCxt (TheoremSchemaMT constdict lemmas prog) =  do
    let eitherConstDictMap = assignSequentialMap 0 constdict
    (newStepCountA, newConsts) <- either (throwM . BigExceptSchemaConstDup) return eitherConstDictMap
    let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
    let constdictPure = Data.Map.map fst newConsts
    maybe (maybe (return ()) throwM (g1 constdictPure)) (maybe (return ()) throwM . g2 constdictPure) mayPrStateCxt
    let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
    let preambleSteps = conststeps <> lemmasteps
    let newState = PrfStdState newProven newConsts newStepCountB
    let mayPreambleLastProp = if Prelude.null lemmas then Last Nothing else (Last . Just . last) lemmas
    (extra,tm,proof,newSteps) 
               <- runSubproofM newContext mempty newState preambleSteps mayPreambleLastProp prog
    return (tm,proof,extra,newSteps) 
       where
            conststeps = Prelude.foldr h1 [] constdict
            lemmasteps = Prelude.foldr h2 [] lemmas
            h1 (const,constType) accumList = PrfStdStepConst const constType (q mayPrStateCxt) : accumList
              where
                 q Nothing = Nothing
                 q (Just (state,_)) = fmap snd (Data.Map.lookup const (consts state)) 
            h2 lemma accumList = PrfStdStepLemma lemma (q mayPrStateCxt) : accumList
              where
                 q Nothing = Nothing
                 q (Just (state,_)) = Data.Map.lookup lemma (provenSents state) 

            g2 constdictPure (PrfStdState alreadyProven alreadyDefinedConsts stepCount, PrfStdContext freeVarTypeStack stepIdfPrefix contextDepth) 
                 = fmap constDictErr (constDictTest (fmap fst alreadyDefinedConsts) constdictPure)
                                               <|> Prelude.foldr f1 Nothing lemmas
             where
                constDictErr (k,Nothing) = BigExceptConstNotDefd k
                constDictErr (k, Just (a,b)) = BigExceptConstTypeConflict k a b
                f1 a = maybe (maybeLemmaInsane <|> maybeLemmaMissing) Just 
                  where
                     maybeLemmaMissing = if not (a `Set.member` Data.Map.keysSet alreadyProven)
                                          then (Just . BigExceptLemmaNotEstablished) a else Nothing
                     maybeLemmaInsane = fmap (BigExceptLemmaSanityErr a) (checkSanity mempty a constdictPure)
            g1 constdictPure = Prelude.foldr f1 Nothing lemmas
              where
                 f1 a = maybe maybeLemmaInsane Just 
                   where
                      maybeLemmaInsane = fmap (BigExceptLemmaSanityErr a) (checkSanity mempty a constdictPure)
  


checkTheoremM :: (Show s, Typeable s, Monoid r1, ProofStd s eL1 r1 o tType, Monad m, MonadThrow m,
                      TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType,
                      Show eL1, Typeable eL1,
                      Typeable o, Show o, StdPrfPrintMonad s o tType m )
                 =>  TheoremSchemaMT tType r1 s o m x
                              -> m (s, r1, x, [PrfStdStep s o tType])
checkTheoremM = checkTheoremMOpen Nothing


data EstTmMError s o tType where
    EstTmMErrMExcept :: SomeException -> EstTmMError s o tType
    deriving (Show)
   




establishTmSilentM :: (Monoid r1, ProofStd s eL1 r1 o tType ,
                     Show s, Typeable s, Ord o, TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType, Typeable o,
                     Show o, Show eL1, Typeable eL1, StdPrfPrintMonad s o tType (Either SomeException))
                            =>  TmSchemaSilentM tType r1 s o () -> 
                                PrfStdContext tType ->
                                PrfStdState s o tType -> 
                                    Either (EstTmMError s o tType) (s, PrfStdStep s o tType)
establishTmSilentM (schema :: TmSchemaSilentM tType r1 s o ()) context state = 
    do
        (tm, prf, (),_) <-  left EstTmMErrMExcept $ checkTheoremMOpen  (Just (state,context)) schema
        return (tm, PrfStdStepTheoremM tm)



data ExpTmMError where
    ExpTmMErrMExcept :: SomeException -> ExpTmMError
    deriving (Show)


expandTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType ,
                     Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE,
                     Show eL1, Typeable eL1,
                     Typeable tType, Show tType, Typeable o, Show o, StdPrfPrintMonad s o tType (Either SomeException))
                            => TmSchemaSilentM tType r1 s o () -> Either ExpTmMError (TheoremSchema s r1 o tType)
expandTheoremM ((TheoremSchemaMT constdict lemmas proofprog):: TmSchemaSilentM tType r1 s o ()) =
      do
          (tm,r1,(),_) <- left ExpTmMErrMExcept (checkTheoremMOpen Nothing (TheoremSchemaMT constdict lemmas proofprog))
          return $ TheoremSchema constdict lemmas tm r1



data ProofByAsmSchema s r where
   ProofByAsmSchema :: {
                       asmPrfAsm :: s,
                       asmPrfConsequent :: s,
                       asmPrfProof :: r
                    } -> ProofByAsmSchema s r
    deriving Show



data ProofByAsmError senttype sanityerrtype logcicerrtype where
   ProofByAsmErrAsmNotSane :: senttype -> sanityerrtype -> ProofByAsmError senttype sanityerrtype logcicerrtype
   ProofByAsmErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> ProofByAsmError senttype sanityerrtype logcicerrtype
    deriving(Show)


proofByAsm :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s) => 
                       ProofByAsmSchema s r1 ->  
                        PrfStdContext tType -> 
                        PrfStdState s o tType ->
                        Either (ProofByAsmError s sE eL1) (s,PrfStdStep s o tType)
proofByAsm (ProofByAsmSchema assumption consequent subproof) context state  =
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







data ProofByUGSchema s r where
   ProofByUGSchema :: {
                       ugGeneralization :: s,
                       ugPrfProof :: r
                    } -> ProofByUGSchema s r
    deriving (Show)


class (PropLogicSent s tType) => PredLogicSent s t tType | s ->tType, s ->t, s->t where
    parseExists :: s -> Maybe (t->s,tType)
    parseForall :: s -> Maybe (t->s,tType)
    -- create generalization from sentence, var type, and free var index.
    createForall ::s -> tType -> Int -> s
 








data ProofByUGError senttype sanityerrtype logicerrtype where
   ProofByUGErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logicerrtype 
                                    -> ProofByUGError senttype sanityerrtype logicerrtype
   ProofByUGErrGenNotForall :: senttype -> ProofByUGError senttype sanityerrtype logicerrtype


 
     deriving(Show)

proofByUG :: ( ProofStd s eL1 r1 o tType, PredLogicSent s t tType, TypedSent o tType sE s,
                  TypeableTerm t o tType sE)
                        => ProofByUGSchema s r1
                            -> PrfStdContext tType 
                            -> PrfStdState s o tType
                          -> Either (ProofByUGError s sE eL1) (s, PrfStdStep s o tType)
proofByUG (ProofByUGSchema generalization subproof) context state =
      do
         let varstack = freeVarTypeStack context
         let mayParse = parseForall generalization
         (f,tType) <- maybe ((throwError . ProofByUGErrGenNotForall) generalization) return mayParse
         let newVarstack = tType : varstack
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]

         let newContext = PrfStdContext newVarstack
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext newVarstack newStepIdxPrefix newContextFrames
         let newState = PrfStdState mempty mempty 1
         let newFreeTerm = free2Term $ length varstack
         let generalizable = f newFreeTerm
         let preambleSteps = [PrfStdStepFreevar (length varstack) tType]
         let eitherTestResult = testSubproof newContext state newState preambleSteps (Last Nothing) generalizable subproof
         finalSteps <- either (throwError . ProofByUGErrSubproofFailedOnErr) return eitherTestResult
         return  (generalization, PrfStdStepSubproof generalization "PRF_BY_UG" finalSteps)







runSubproofM :: ( Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                        Show eL1, Typeable eL1, Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, StdPrfPrintMonad s o tType m )
                 =>    PrfStdContext tType -> PrfStdState s o tType -> PrfStdState s o tType
                          -> [PrfStdStep s o tType] -> Last s -> ProofGenTStd tType r1 s o m x
                          ->  m (x,s,r1,[PrfStdStep s o tType])
runSubproofM context baseState preambleState preambleSteps mayPreambleLastProp prog =  do
          printStartFrame (contextFrames context)
          unless (Prelude.null preambleSteps) (printSteps (contextFrames context) (stepIdxPrefix context) 0 preambleSteps)
          let baseStateZero = PrfStdState (provenSents baseState) (consts baseState) 0
          let startState = baseStateZero <> preambleState
          (extraData,newState,r,newSteps, mayLastProp) <- runProofGeneratorTOpen prog context startState
          let constdict = fmap fst (consts startState)
          let mayPrfResult = getLast $ mayPreambleLastProp <> mayLastProp
          prfResult <- maybe (throwM BigExceptNothingProved) return mayPrfResult
          let sc = checkSanity (freeVarTypeStack context) prfResult constdict
          maybe (return ()) (throwM . BigExceptResultSanity prfResult) sc
          let endState = preambleState <> newState
          let finalSteps = preambleSteps <> newSteps
          return (extraData, prfResult, r,finalSteps)



class PredLogSchemaRule r s o tType | r->o, r -> tType where
   theoremSchemaRule :: TheoremSchema s r o tType -> r
   theoremSchemaSilentMRule :: TmSchemaSilentM tType r s o () -> r
   proofByUGSchemaRule :: ProofByUGSchema s r -> r




runTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                      MonadThrow m, Show tType, Typeable tType,
                      Show o, Typeable o, Show s, Typeable s,
                      Show eL1, Typeable eL1, Ord o, TypedSent o tType sE s, Show sE, Typeable sE,
                      StdPrfPrintMonad s o tType m, PredLogSchemaRule r1 s o tType)
                 =>   TheoremSchemaMT tType r1 s o m x ->
                               ProofGenTStd tType r1 s o m (s, [Int], x)
runTheoremM (TheoremSchemaMT constDict lemmas prog) =  do
        state <- getProofState
        context <- ask
        (tm, proof, extra, newSteps) <- lift $ checkTheoremMOpen (Just (state,context)) (TheoremSchemaMT constDict lemmas prog)
        mayMonadifyRes <- monadifyProofStd (theoremSchemaRule $ TheoremSchema constDict lemmas tm proof)
        idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (tm, idx, extra)


runTmSilentM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                      MonadThrow m, Show tType, Typeable tType,
                      Show o, Typeable o, Show s, Typeable s,
                      Show eL1, Typeable eL1, Ord o, TypedSent o tType sE s, Show sE, Typeable sE,
                      StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException),
                      PredLogSchemaRule r1 s o tType)
                 =>   TmSchemaSilentM tType r1 s o x ->
                               ProofGenTStd tType r1 s o m (s, [Int], x)
-- runTmSilentM f (TheoremSchemaMT constDict lemmas prog) =  do
runTmSilentM (TheoremSchemaMT constDict lemmas prog) =  do
        state <- getProofState
        context <- ask
        let eitherResult = checkTheoremMOpen 
                     (Just (state,context)) 
                     (TheoremSchemaMT constDict lemmas prog)
        (tm, proof, extra, newSteps) <- either throwM return eitherResult
        mayMonadifyRes <- monadifyProofStd (theoremSchemaSilentMRule $ TheoremSchemaMT constDict lemmas newProg)
        idx <- maybe (error "No theorem returned by monadifyProofStd on theorem schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (tm, idx, extra)
    where
        newProg = do
             prog
             return ()

class PropLogSchemaRule r s  where
   proofByAsmSchemaRule :: ProofByAsmSchema s r -> r

runProofByAsmM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PropLogicSent s tType, MonadThrow m,
                       Show s, Typeable s,
                       Show eL1, Typeable eL1, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m, PropLogSchemaRule r1 s )
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
        mayMonadifyRes <- (monadifyProofStd . proofByAsmSchemaRule) (ProofByAsmSchema asm consequent subproof)
        idx <- maybe (error "No theorem returned by monadifyProofStd on asm schema. This shouldn't happen") (return . snd) mayMonadifyRes
        return (asm .->. consequent,idx,extraData)





runProofByUGM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PredLogicSent s t tType, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m,PredLogSchemaRule r1 s o tType)
                 =>  tType -> ProofGenTStd tType r1 s o m x
                            -> ProofGenTStd tType r1 s o m (s, [Int], x)
runProofByUGM tt prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let newFrVarTypStack = tt : frVarTypeStack
        let newContextFrames = contextFrames context <> [False]
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContext = PrfStdContext newFrVarTypStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState mempty mempty 1
        let preambleSteps = [PrfStdStepFreevar (length frVarTypeStack) tt]
        (extraData,generalizable,subproof, newSteps) 
                 <- lift $ runSubproofM newContext state newState preambleSteps (Last Nothing) prog
        let resultSent = createForall generalizable tt (Prelude.length frVarTypeStack)
        mayMonadifyRes <- (monadifyProofStd . proofByUGSchemaRule) (ProofByUGSchema resultSent subproof)
        idx <- maybe (error "No theorem returned by monadifyProofStd on ug schema. This shouldn't happen") (return . snd) mayMonadifyRes       
        return (resultSent,idx,extraData)


getTopFreeVar :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PredLogicSent s t tType, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE,
                       StdPrfPrintMonad s o tType m, TypeableTerm t Text tType sE)
                 =>  ProofGenTStd tType r1 s o m t
getTopFreeVar =  do
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        if null frVarTypeStack then throwM BigExceptEmptyVarStack
            else return (free2Term $ length frVarTypeStack - 1)


class RuleInject r1 r2 where
    injectRule :: r1 -> r2