{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}




module Main where



import Data.Monoid
import Data.Functor.Identity ( Identity(runIdentity) )
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.RWS
import Text.XHtml (vspace, name, abbr, p, table, rules)
import Data.Set (Set, fromList)
import Data.List (mapAccumL)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.List (intersperse)
import Data.Map
import Distribution.Simple (ProfDetailLevel(ProfDetailExportedFunctions), KnownExtension (ListTuplePuns))
import Data.Text.Internal.Encoding.Utf8 (ord2)
import Data.Maybe
import GHC.RTS.Flags (MiscFlags(linkerMemBase))
import Control.Applicative
import Control.Monad.Reader
import Control.Arrow
import Control.Monad.Except


import Control.Monad.Catch
    ( SomeException, MonadCatch(..), MonadThrow(..), Exception )
import qualified GHC.Stack.Types
import Data.Data (Typeable)
import Distribution.PackageDescription (TestType)
import Distribution.Backpack.LinkedComponent (extendLinkedComponentMap)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))


default(Text)


class ErrorEmbed e1 e2 where
     errEmbed:: e1-> e2



class (Monoid s, Monoid stpT) => Proof e r s c stpT | r -> s, r->e, r->c, r -> stpT  where
      runProof :: c -> r -> s -> Either e (s , stpT)



data ProofGeneratorT stpT eL c r s m x where
  ProofGenInternalT  :: {runProofGenTInternal :: RWST c (r,stpT) s m x}
                   -> ProofGeneratorT stpT eL c r s m x


runProofGeneratorT ::  (Monad m, MonadThrow m, Proof eL r s c stpT) => ProofGeneratorT stpT eL c r s m x -> c -> s -> m (x,s, r,stpT)
runProofGeneratorT ps context state = do
           (x, s, (r,stpT)) <- runRWST (runProofGenTInternal ps) context state
           return (x,s,r,stpT)



type ProofGenerator stpT eL c r s x = ProofGeneratorT stpT eL c r s (Either SomeException) x


runProofGenerator :: (Proof eL r s c stpT) => ProofGenerator stpT eL c r s x -> c -> s-> Either SomeException (x, s, r, stpT)
runProofGenerator = runProofGeneratorT



instance (Monad m) => Functor (ProofGeneratorT stpT eL c r s m) where
     fmap :: Monad m =>
              (a -> b) -> ProofGeneratorT stpT eL c r s m a -> ProofGeneratorT stpT eL c r s m b
     fmap f (ProofGenInternalT  g) = ProofGenInternalT  $ fmap f g





instance (Monoid r, Monad m, Proof eL r s c stpT) => Applicative (ProofGeneratorT stpT eL c r s m) where
   pure :: (Monad m, Proof eL r s c stpT) => a -> ProofGeneratorT stpT eL c r s m a
   (<*>) :: (Monad m, Proof eL r s c stpT) => ProofGeneratorT stpT eL c r s m (a -> b)
                                        -> ProofGeneratorT stpT eL c r s m a -> ProofGeneratorT stpT eL c r s m b
   ProofGenInternalT  a <*> ProofGenInternalT  b = ProofGenInternalT  $ a <*> b
   pure x = ProofGenInternalT  $ pure x



instance (Monoid r,Proof eL r s c stpT, Monad m) => Monad (ProofGeneratorT stpT eL c r s m) where
   (>>=) :: (Proof eL r s c stpT, Monad m) => ProofGeneratorT stpT eL c r s m a
                                         -> (a -> ProofGeneratorT stpT eL c r s m b)
                                     -> ProofGeneratorT stpT eL c r s m b
   ProofGenInternalT  y >>= g = ProofGenInternalT  (y >>= runProofGenTInternal . g)



instance (Monoid r,Proof eL r s c stpT) =>  MonadTrans (ProofGeneratorT stpT eL c r s) where
      lift :: (Monoid r, Monad m) => m a -> ProofGeneratorT stpT eL c r s m a
      lift = ProofGenInternalT  . lift


getProofState :: (Monoid r, Proof eL r s c stpT, Monad m) => ProofGeneratorT stpT eL c r s m s
getProofState = ProofGenInternalT  get




instance (Monoid r,Proof eL r s c stpT, Monad m, MonadThrow m) => MonadThrow (ProofGeneratorT stpT eL c r s m) where
  throwM :: (Monoid r, Proof eL r s c stpT, Monad m, MonadThrow m, GHC.Stack.Types.HasCallStack, Exception e) =>
                 e -> ProofGeneratorT stpT eL c r s m a
  throwM = ProofGenInternalT  . lift . throwM

instance (Proof eL r s c stpT, Monoid r, MonadThrow m, MonadCatch m) 
                   => MonadCatch (ProofGeneratorT stpT eL c r s m) where
       catch :: (Proof eL r s c stpT, GHC.Stack.Types.HasCallStack, MonadThrow m, MonadCatch m,Exception e) =>
            ProofGeneratorT stpT eL c r s m a -> (e -> ProofGeneratorT stpT eL c r s m a) 
                   -> ProofGeneratorT stpT eL c r s m a
       catch z errhandler = ProofGenInternalT  (RWST \c s -> do
            (a,b,c,d)<-catch (runProofGeneratorT z c s) (\err -> runProofGeneratorT (errhandler err) c s)
            return (a,b,(c,d))
            )


instance (Monad m, Monoid r, Monad (ProofGeneratorT stpT eL c r s m), Monoid stpT) 
            => MonadReader c (ProofGeneratorT stpT eL c r s m) where
   ask ::  ProofGeneratorT stpT eL c r s m c
   ask = ProofGenInternalT  ask
   local :: (c->c) -> ProofGeneratorT stpT eL c r s m a -> ProofGeneratorT stpT eL c r s m a
   local f (ProofGenInternalT  g) = ProofGenInternalT  $ local f g

data MonadifyProofException eL where
  MonadifyProofException :: eL -> MonadifyProofException eL
  deriving (Typeable, Show)


instance (Show eL,Typeable eL) => Exception (MonadifyProofException eL)
monadifyProof :: (Monoid r, Proof eL r s c stpT, Monad m,  MonadThrow m, 
                 Show eL, Typeable eL) => r -> ProofGeneratorT stpT eL c r s m (s,stpT)
monadifyProof p = ProofGenInternalT  $ do
                        c <- ask
                        u <- get
                        let proofResult = runProof c p u
                        (resultState, newSteps) <- either (lift . throwM . MonadifyProofException) return proofResult
                        put (u <> resultState)
                        tell (p,newSteps)
                        return (resultState,newSteps)


modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c stpT, 
             Proof eL2 r2 s c stpT,  MonadThrow m, Typeable eL2, Show eL2)
             =>  (r1 -> r2) -> ProofGeneratorT stpT eL1 c r1 s m a
                       -> ProofGeneratorT stpT eL2 c r2 s m a
modifyPS g m1 = do
    c <- ask
    ps <- getProofState
    (datum,_,rules,steps) <- lift $ runProofGeneratorT m1 c ps
    monadifyProof $ g rules
    return datum





---------------------- END KERNEL --------------------------------------------------------------

-------------- SUBPROOFABLE-----------------------------------------------------------------------



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



type ProofGenTStd tType eL r s o m 
               = ProofGeneratorT [PrfStdStep s o tType] eL (PrfStdContext tType) r (PrfStdState s o tType) m




type ProofStd s eL r o tType = Proof eL r (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType]

data PrfStdStep s o tType where
    PrfStdStepStep :: s -> Text -> [[Int]] -> PrfStdStep s o tType
    PrfStdStepLemma :: s -> Maybe [Int] -> PrfStdStep s o tType
    PrfStdStepConst :: o -> tType -> Maybe [Int] -> PrfStdStep s o tType
    PrfStdTheorem :: s -> [PrfStdStep s o tType] -> PrfStdStep s o tType
    PrfStdPrfBySubproof :: s -> Text -> [PrfStdStep s o tType] ->  PrfStdStep s o tType
    PrfStdTheoremM :: s -> PrfStdStep s o tType
    PrfStdStepFreevar :: Int -> tType -> PrfStdStep s o tType






class (Eq tType, Ord o) => TypeableTerm t o tType sE | t -> o, t ->tType, t -> sE where
    getTypeTerm :: t -> [tType] -> Map o tType -> Either sE tType
    const2Term :: o -> t
    free2Term :: Int -> t
        -- get term type using a varstack and a const dictionary



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
   TestSubproofErrorResultNotProved :: senttype -> TestSubproofErr senttype sanityerrtype logicerrtype
   deriving(Show)


testSubproof :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s    )
                       => PrfStdContext tType -> PrfStdState s o tType -> PrfStdState s o tType -> 
                          [PrfStdStep s o tType] -> s -> r1 
                             -> Either (TestSubproofErr s sE eL1) ([PrfStdStep s o tType],[Int])
testSubproof context baseState preambleState preambleSteps targetProp subproof =
      --either return (const Nothing) eitherResult
      do
             let frVarTypeStack = freeVarTypeStack context
             let baseStateZero = PrfStdState (provenSents baseState) (consts baseState) 0
             let startState = baseStateZero <> preambleState
             let constdict = fmap fst (consts startState)
             let sc = checkSanity frVarTypeStack targetProp constdict
             maybe (return ()) (throwError . TestSubproofErrResultNotSane targetProp) sc
             (newState,newSteps) <- left TestSubproofErrorSubproofFailedOnErr (runProof context subproof startState)
             let endState = preambleState <> newState
             let mayResultIndex = Data.Map.lookup targetProp (provenSents endState)
             resultIndex <- maybe (throwError $ TestSubproofErrorResultNotProved targetProp) return mayResultIndex
             let resultLine = last resultIndex
             let finalSteps = preambleSteps <> newSteps
             let stepsNeeded = Prelude.take (resultLine + 1) finalSteps
             return (stepsNeeded,resultIndex)


data TheoremSchema s r o tType where
   TheoremSchema :: {
                       constDict :: [(o,tType)],
                       lemmas :: [s],
                       theoremProof :: r,
                       theorem :: s
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


checkTheorem :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType -> Maybe (PrfStdState s o tType,PrfStdContext tType)
                                       -> Either (ChkTheoremError s sE eL1 o tType) ([PrfStdStep s o tType],[Int])
checkTheorem (TheoremSchema constdict lemmas subproof theorem) mayPrStateCxt =
  do
       let eitherConstDictMap = assignSequentialMap 0 constdict
       (newStepCountA, newConsts) <- either (throwError . ChkTheoremErrSchemaDupConst) return eitherConstDictMap
       let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
       let constdictPure = Data.Map.map fst newConsts
       maybe (return ()) throwError (maybe (g1 constdictPure) (g2 constdictPure) mayPrStateCxt)
       let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
       let newState = PrfStdState newProven newConsts newStepCountB
       let preambleSteps = conststeps <> lemmasteps

       (newSteps,resultIndex) <- left ChkTheoremErrSubproofErr (
                                      testSubproof newContext mempty newState preambleSteps theorem subproof)
       return (preambleSteps <> newSteps,resultIndex)
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


establishTheorem :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType -> PrfStdState s o tType -> PrfStdContext tType
                                       -> Either (ChkTheoremError s sE eL1 o tType) (PrfStdStep s o tType)
establishTheorem schema state context = do
    (steps,resultIndex) <- checkTheorem schema (Just (state,context))
    let tm = theorem schema
    return (PrfStdTheorem tm steps)




data TheoremSchemaMT tType eL r s o m x where
   TheoremSchemaMT :: {
                       lemmasM :: [s],
                       proofM :: ProofGenTStd tType eL r s o m (s,x),
                       constDictM :: [(o,tType)]
                     } -> TheoremSchemaMT tType eL r s o m x


instance (Show s, Show o, Show tType) => Show (TheoremSchemaMT tType eL r s o m x) where
    show :: (Show s, Show o, Show tType) => TheoremSchemaMT tType eL r s o m x -> String
    show (TheoremSchemaMT ls prog constDict) =
        "TheoremSchemaMT " <> show ls <> " <<Monadic subproof>> " <> show constDict




type TheoremSchemaM tType eL r s o = TheoremSchemaMT tType eL r s o (Either SomeException) ()

data BigException s sE o tType where
   BigExceptLemmaSanityErr :: s -> sE -> BigException s sE o tType
   BigExceptResNotProven :: s -> BigException s sE o tType
   BigExceptResultSanity :: s -> sE -> BigException s sE o tType
   BigExceptConstNotDefd :: o ->  BigException s sE o tType
   BigExceptConstTypeConflict :: o -> tType -> tType -> BigException s sE o tType
   BigExceptLemmaNotEstablished :: s -> BigException s sE o tType
   BigExceptAsmSanity :: s -> sE -> BigException s sE o tType
   BigExceptSchemaConstDup :: o -> BigException s sE o tType


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
     printMReturn :: [Bool] -> s -> [Int] -> m ()




instance (ProofStd s eL r o tType, Monoid r, Monad m, StdPrfPrintMonadFrame m) 
          => StdPrfPrintMonadFrame (ProofGenTStd tType eL r s o m) where
    printStartFrame :: [Bool] -> ProofGenTStd tType eL r s o m ()
    printStartFrame contextFrames = lift $ printStartFrame contextFrames



instance (StdPrfPrintMonad s o tType m, 
          ProofStd s eL r o tType, 
          Monoid r, 
          StdPrfPrintMonadFrame (ProofGenTStd tType eL r s o m))
             => StdPrfPrintMonad s o tType (ProofGenTStd tType eL r s o m) where
  printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep s o tType] -> ProofGenTStd tType eL r s o m ()
  printSteps contextFrames idx stepStart steps = lift $ printSteps contextFrames idx stepStart steps
  printMReturn :: [Bool] -> s -> [Int] -> ProofGenTStd tType eL r s o m ()
  printMReturn contextFrames returnSent idx = lift $ printMReturn contextFrames returnSent idx






monadifyProofStd :: (MonadThrow m, ProofStd s eL r o tType, Monoid r,
                    Show eL, Typeable eL, StdPrfPrintMonad s o tType m) 
           => r -> ProofGenTStd tType eL r s o m (PrfStdState s o tType,[PrfStdStep s o tType])
monadifyProofStd p = do
     PrfStdContext fvStack idx contextFrames <- ask
     state <- getProofState
     (addedState,steps) <- monadifyProof p
     
     printSteps contextFrames idx (stepCount state) steps
     return (addedState, steps)



checkTheoremM :: (Show s, Typeable s, Monoid r1, ProofStd s eL1 r1 o tType, Monad m, MonadThrow m,
                      PropLogicSent s tType, TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType,
                      Show eL1, Typeable eL1,
                      Typeable o, Show o, StdPrfPrintMonad s o tType m )
                 =>  Maybe (PrfStdState s o tType,PrfStdContext tType) ->  TheoremSchemaMT tType eL1 r1 s o m x
                              -> m (s, r1, x, [PrfStdStep s o tType], Int)
checkTheoremM mayPrStateCxt (TheoremSchemaMT lemmas prog constdict) =  do
    let eitherConstDictMap = assignSequentialMap 0 constdict
    (newStepCountA, newConsts) <- either (throwM . BigExceptSchemaConstDup) return eitherConstDictMap
    let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
    let constdictPure = Data.Map.map fst newConsts
    maybe (maybe (return ()) throwM (g1 constdictPure)) (maybe (return ()) throwM . g2 constdictPure) mayPrStateCxt
    let newContext = PrfStdContext [] [] (maybe []  ((<>[True]) . contextFrames . snd) mayPrStateCxt)
    let preambleSteps = conststeps <> lemmasteps
    let newState = PrfStdState newProven newConsts newStepCountB
    (extra,tm,proof,newSteps, resultIndex) <- runSubproofM newContext mempty newState preambleSteps prog
    return (tm,proof,extra,newSteps, head resultIndex) 
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
  

checkTheoremMConsistency :: (Show s, Typeable s, Monoid r1, ProofStd s eL1 r1 o tType, Monad m, MonadThrow m,
                      PropLogicSent s tType, TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType,
                      Show eL1, Typeable eL1,
                      Typeable o, Show o, StdPrfPrintMonad s o tType m )
                 =>  TheoremSchemaMT tType eL1 r1 s o m x
                              -> m (s, r1, x, [PrfStdStep s o tType], Int)
checkTheoremMConsistency schema = do
                        (tm, prf, extra, steps, index) <- checkTheoremM Nothing schema
                        return (tm, prf, extra, steps, index)

data EstTmMError s o tType where
    EstTmMErrMExcept :: SomeException -> EstTmMError s o tType
    deriving (Show)
   




establishTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType ,
                     PropLogicSent s tType,
                     Show s, Typeable s, Ord o, TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType, Typeable o,
                     Show o, Show eL1, Typeable eL1, StdPrfPrintMonad s o tType (Either SomeException))
                            => PrfStdState s o tType -> PrfStdContext tType ->
                                  TheoremSchemaM tType eL1 r1 s o -> Either (EstTmMError s o tType) (s, PrfStdStep s o tType)
establishTheoremM state context (schema :: TheoremSchemaM tType eL1 r1 s o) = 
    do
        (tm, prf, (),_,_) <-  left EstTmMErrMExcept $ checkTheoremM  (Just (state,context)) schema
        return (tm, PrfStdTheoremM tm)



data ExpTmMError where
    ExpTmMErrMExcept :: SomeException -> ExpTmMError
    deriving (Show)


expandTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType ,
                     PropLogicSent s tType, Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE,
                     Show eL1, Typeable eL1,
                     Typeable tType, Show tType, Typeable o, Show o, StdPrfPrintMonad s o tType (Either SomeException))
                            => TheoremSchemaM tType eL1 r1 s o -> Either ExpTmMError (TheoremSchema s r1 o tType)
expandTheoremM ((TheoremSchemaMT lemmas proofprog constdict):: TheoremSchemaM tType eL1 r1 s o) =
      do
          (tm,r1,(),_,_) <- left ExpTmMErrMExcept (checkTheoremM Nothing (TheoremSchemaMT lemmas proofprog constdict))
          return $ TheoremSchema constdict lemmas r1 tm



data ProofByAsmSchema s r where
   ProofByAsmSchema :: {
                       asmPrfAsm :: s,
                       asmPrfProof :: r,
                       asmPrfConsequent :: s
                    } -> ProofByAsmSchema s r
    deriving Show



data ProofByAsmError senttype sanityerrtype logcicerrtype where
   ProofByAsmErrAsmNotSane :: senttype -> sanityerrtype -> ProofByAsmError senttype sanityerrtype logcicerrtype
   ProofByAsmErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> ProofByAsmError senttype sanityerrtype logcicerrtype
    deriving(Show)


proofByAsm :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s) => 
                       PrfStdState s o tType -> PrfStdContext tType -> 
                        ProofByAsmSchema s r1 -> Either (ProofByAsmError s sE eL1) (s,PrfStdStep s o tType)
proofByAsm state context (ProofByAsmSchema assumption subproof consequent) =
      do
         let frVarTypeStack = freeVarTypeStack context
         let constdict = fmap fst (consts state)
         let sc = checkSanity frVarTypeStack consequent constdict
         maybe (return ()) (throwError .  ProofByAsmErrAsmNotSane assumption) sc
         let alreadyProven = provenSents state
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
         let newSents = Data.Map.insert assumption (newStepIdxPrefix ++ [0]) mempty
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames
         let newState = PrfStdState newSents mempty 1
         let preambleSteps = [PrfStdStepStep assumption "ASM" []]
         let eitherTestResult = testSubproof newContext state newState preambleSteps consequent subproof
         (finalSteps,resultIndex) <- either (throwError . ProofByAsmErrSubproofFailedOnErr) return eitherTestResult
         let implication = assumption .->. consequent
         return (implication, PrfStdPrfBySubproof implication "PRF_BY_ASM" finalSteps)


data ProofByUGSchema lType r where
   ProofByUGSchema :: {
                       ugPrfLambda :: lType,
                       ugPrfProof :: r
                    } -> ProofByUGSchema lType r
    deriving (Show)


class (PropLogicSent s tType) => PredLogicSent s t tType lType | lType -> s, lType->tType, lType->t, s->t, s-> lType where
    parseExists :: s -> Maybe lType
    parseForall :: s -> Maybe lType
    -- create generalization from sentence, var type, and free var index.
    createLambda ::s -> tType -> Int -> lType
    lType2Func :: lType -> (t -> s)
    lType2Forall :: lType -> s
    lType2Exists :: lType -> s
    lTypeTType :: lType -> tType








data ProofByUGError senttype sanityerrtype logicerrtype where
   ProofByUGErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logicerrtype 
                                    -> ProofByUGError senttype sanityerrtype logicerrtype
 
     deriving(Show)

proofByUG :: ( ProofStd s eL1 r1 o tType, PredLogicSent s t tType lType, TypedSent o tType sE s,
                  TypeableTerm t o tType sE)
                        => PrfStdState s o tType -> PrfStdContext tType -> 
                         ProofByUGSchema lType r1 -> Either (ProofByUGError s sE eL1) (s, PrfStdStep s o tType)
proofByUG state context (ProofByUGSchema lambda subproof) =
      do
         let varstack = freeVarTypeStack context
         let newVarstack = lTypeTType lambda : varstack
         let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]

         let newContext = PrfStdContext newVarstack
         let newContextFrames = contextFrames context <> [False]
         let newContext = PrfStdContext newVarstack newStepIdxPrefix newContextFrames
         let newState = PrfStdState mempty mempty 1
         let newFreeTerm = free2Term $ length varstack
         let generalizable = lType2Func lambda newFreeTerm
         let preambleSteps = [PrfStdStepFreevar (length varstack) (lTypeTType lambda)]
         let eitherTestResult = testSubproof newContext state newState preambleSteps generalizable subproof
         (finalSteps,resultIndex) <- either (throwError . ProofByUGErrSubproofFailedOnErr) return eitherTestResult
         let generalized = lType2Forall lambda
         return  (generalized, PrfStdPrfBySubproof generalized "PRF_BY_UG" finalSteps)







runSubproofM :: ( Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                        PropLogicSent s tType, Show eL1, Typeable eL1, Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, StdPrfPrintMonad s o tType m )
                 =>    PrfStdContext tType -> PrfStdState s o tType -> PrfStdState s o tType
                          -> [PrfStdStep s o tType] -> ProofGenTStd tType eL1 r1 s o m (s, x) ->
                          m (x,s,r1,[PrfStdStep s o tType],[Int])
runSubproofM context baseState preambleState preambleSteps prog =  do
          printStartFrame (contextFrames context)
          printSteps (contextFrames context) (stepIdxPrefix context) 0 preambleSteps
          let baseStateZero = PrfStdState (provenSents baseState) (consts baseState) 0
          let startState = baseStateZero <> preambleState
          ((prfResult,extraData),newState,r,newSteps) <- runProofGeneratorT prog context startState
          let constdict = fmap fst (consts startState)
          let sc = checkSanity (freeVarTypeStack context) prfResult constdict
          maybe (return ()) (throwM . BigExceptResultSanity prfResult) sc
          let endState = preambleState <> newState
          let mayResultIndex = Data.Map.lookup prfResult (provenSents endState)
          resultIndex <- maybe ((throwM . BigExceptResNotProven) prfResult) return mayResultIndex
          let resultLine = last resultIndex
          let finalSteps = preambleSteps <> newSteps
          let newStepsNeeded = Prelude.take (resultLine + 1) finalSteps
          printMReturn (contextFrames context) prfResult resultIndex
          return (extraData, prfResult, r,newStepsNeeded,resultIndex)



runTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                      PropLogicSent s tType, MonadThrow m, Show tType, Typeable tType,
                      Show o, Typeable o, Show s, Typeable s,
                      Show eL1, Typeable eL1, Ord o, TypedSent o tType sE s, Show sE, Typeable sE,
                      StdPrfPrintMonad s o tType m)
                 =>   (TheoremSchema s r1 o tType -> r1) -> TheoremSchemaMT tType eL1 r1 s o m x ->
                               ProofGenTStd tType eL1 r1 s o m (s, x)
runTheoremM f (TheoremSchemaMT lemmas prog constDict) =  do
        state <- getProofState
        context <- ask
        (tm, proof, extra, newSteps, _) <- lift $ checkTheoremM (Just (state,context)) (TheoremSchemaMT lemmas prog constDict)
        monadifyProofStd (f $ TheoremSchema constDict lemmas proof tm)
        return (tm, extra)


runProofByAsmM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PropLogicSent s tType, MonadThrow m,
                       Show s, Typeable s,
                       Show eL1, Typeable eL1, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m )
                 =>   (ProofByAsmSchema s r1 -> r1) -> s -> ProofGenTStd tType eL1 r1 s o m (s, x)
                            -> ProofGenTStd tType eL1 r1 s o m (s, x)
runProofByAsmM f asm prog =  do
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
        (extraData,consequent,subproof,newSteps,_) <- lift $ runSubproofM newContext state newState preambleSteps prog
        (monadifyProofStd . f) (ProofByAsmSchema asm subproof consequent)
        return (asm .->. consequent,extraData)



runProofByUGM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PredLogicSent s t tType lType, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE, 
                       StdPrfPrintMonad s o tType m )
                 =>  tType -> (ProofByUGSchema lType r1 -> r1) -> ProofGenTStd tType eL1 r1 s o m (s, x)
                            -> ProofGenTStd tType eL1 r1 s o m (s, x)
runProofByUGM tt f prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let newFrVarTypStack = tt : frVarTypeStack
        let newContextFrames = contextFrames context <> [False]
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContext = PrfStdContext newFrVarTypStack newStepIdxPrefix newContextFrames
        let newState = PrfStdState mempty mempty 1
        let preambleSteps = [PrfStdStepFreevar (length frVarTypeStack) tt]
        (extraData,generalizable,subproof, newSteps,_) <- lift $ runSubproofM newContext state newState preambleSteps prog
        let lambda = createLambda generalizable tt (Prelude.length frVarTypeStack)
        (monadifyProofStd . f) (ProofByUGSchema lambda subproof)
        let resultSent = lType2Forall lambda         
        return (resultSent,extraData)


data PropLogError s sE o tType where
    PLErrMPImplNotProven :: s-> PropLogError s sE o tType
    PLErrMPAnteNotProven :: s-> PropLogError s sE o tType
    PLErrSentenceNotImp :: s -> PropLogError s sE o tType
    PLErrSentenceNotAdj :: s -> PropLogError s sE o tType
    PLErrPrfByAsmErr :: ProofByAsmError s sE (PropLogError s sE o tType) -> PropLogError s sE o tType
    PLErrTheorem :: ChkTheoremError s sE (PropLogError s sE o tType) o tType -> PropLogError s sE o tType
    PLErrTheoremM :: EstTmMError s o tType -> PropLogError s sE o tType
    PLExclMidSanityErr :: s -> sE -> PropLogError s sE o tType
    PLSimpLAdjNotProven :: s -> PropLogError s sE o tType
    PLAdjLeftNotProven :: s -> PropLogError s sE o tType
    PLAdjRightNotProven :: s -> PropLogError s sE o tType
    PLRepOriginNotProven :: s -> PropLogError s sE o tType
    deriving(Show)


data PropLogR tType s sE o where
    MP :: s -> PropLogR tType s sE o
    PLProofByAsm :: ProofByAsmSchema s [PropLogR tType s sE o]-> PropLogR tType s sE o
    PLTheorem :: TheoremSchema s [PropLogR tType s sE o] o tType -> PropLogR tType s sE o
    PLTheoremM :: TheoremSchemaM tType (PropLogError s sE o tType ) [PropLogR tType s sE o] s o -> PropLogR tType s sE o
    PLExclMid :: s -> PropLogR tType s sE o
    PLSimpL :: s -> PropLogR tType s sE o
    PLSimpR :: s -> s ->  PropLogR tType s sE o
    PLAdj :: s -> s -> PropLogR tType s sE o
    PLRep :: s -> PropLogR tType s sE o
    deriving(Show)



pLrunProof :: (ProofStd s (PropLogError s sE o tType) [PropLogR tType s sE o] o tType,
               PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
               Show o, Typeable o, Typeable tType, Show tType, StdPrfPrintMonad s o tType (Either SomeException)) =>
                            PrfStdState s o tType -> PrfStdContext tType -> PropLogR tType s sE o
                                      -> Either (PropLogError s sE o tType) (s,PrfStdStep s o tType)
pLrunProof state context rule = 
      case rule of
        MP implication -> do
             (antecedant, conseq) <- maybe ((throwError . PLErrSentenceNotImp) implication) return (parse_implication implication)
             impIndex <- maybe ((throwError . PLErrMPImplNotProven) implication) return (Data.Map.lookup implication (provenSents state))
             anteIndex <- maybe ((throwError . PLErrMPAnteNotProven) antecedant) return (Data.Map.lookup antecedant (provenSents state))
             return (conseq, PrfStdStepStep conseq "MP" [impIndex,anteIndex])
        PLProofByAsm schema ->
             left PLErrPrfByAsmErr (proofByAsm state context schema)
        PLTheorem schema -> do
              step <- left PLErrTheorem (establishTheorem schema state context)
              return (theorem schema,step)
        PLTheoremM schema ->
            left PLErrTheoremM (establishTheoremM state context schema)
        PLExclMid s -> do
             maybe (return ())   (throwError . PLExclMidSanityErr s) (checkSanity (freeVarTypeStack context) s (fmap fst (consts state)))
             let prop = s .||. neg s
             return (prop,PrfStdStepStep prop "EXMID" [])
        PLSimpL aAndB -> do
            (a,b) <- maybe ((throwError . PLErrSentenceNotAdj) aAndB) return (parseAdj aAndB)
            aAndBIndex <- maybe ((throwError . PLSimpLAdjNotProven) aAndB) return (Data.Map.lookup aAndB (provenSents state))
            return (a, PrfStdStepStep a "SIMP_L" [aAndBIndex])
        PLAdj a b -> do
            leftIndex <- maybe ((throwError . PLAdjLeftNotProven) a) return (Data.Map.lookup a (provenSents state))
            rightIndex <- maybe ((throwError . PLAdjRightNotProven) b) return (Data.Map.lookup b (provenSents state))
            let aAndB = a .&&. b
            return (aAndB, PrfStdStepStep aAndB "ADJ" [leftIndex,rightIndex])
        PLRep a -> do
            originIndex <- maybe ((throwError . PLRepOriginNotProven) a) return (Data.Map.lookup a (provenSents state))
            return (a, PrfStdStepStep a "REP" [originIndex])
             



instance (PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType),
          StdPrfPrintMonad s o tType (Either SomeException))
             => Proof (PropLogError s sE o tType)
              [PropLogR tType s sE o] 
              (PrfStdState s o tType) 
              (PrfStdContext tType)
              [PrfStdStep s o tType]
                    where
  runProof :: (PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s,
               Ord o, TypedSent o tType sE s, Typeable o, Show o, Typeable tType,
               Show tType, Monoid (PrfStdState s o tType)) =>
                 PrfStdContext tType -> [PropLogR tType s sE o] -> PrfStdState s o tType 
                        -> Either (PropLogError s sE o tType) (PrfStdState s o tType, [PrfStdStep s o tType]) 
    
--   runProof varStack rs (proven, constDict) = foldM f (mempty,mempty) rs
  runProof context rs oldState = foldM f (PrfStdState mempty mempty 0,[]) rs
        where
            f :: (PrfStdState s o tType, [PrfStdStep s o tType]) -> PropLogR tType s sE o 
                     -> Either (PropLogError s sE o tType) (PrfStdState s o tType, [PrfStdStep s o tType])
            f (newState,newSteps) r 
                       =  fmap g (pLrunProof (oldState <> newState) context r)
               where
                   g (s, step) = (newState <> PrfStdState (Data.Map.insert s newLineIndex mempty) mempty 1,
                                    newSteps <> [step])
                      where
                        newStepCount = stepCount newState + 1
                        newLineIndex = stepIdxPrefix context <> [stepCount oldState + newStepCount-1]




data PredProofError s sE o t tType lType where
    PredProofPrfByAsmErr :: ProofByAsmError s sE (PredProofError s sE o t tType lType) -> PredProofError s sE o t tType lType
    PredProofErrTheorem :: ChkTheoremError s sE (PredProofError s sE o t tType lType) o tType -> PredProofError s sE o t tType lType
    PredProofErrTheoremM :: EstTmMError s o tType -> PredProofError s sE o t tType lType
    PredProofErrPL ::  PropLogError s sE o tType -> PredProofError s sE o t tType lType
    PredProofErrUG :: ProofByUGError s sE  (PredProofError s sE o t tType lType) -> PredProofError s sE o t tType lType
    PredProofErrEINotProven :: s -> PredProofError s sE o t tType lType
    PredProofErrUINotProven :: s -> PredProofError s sE o t tType lType
    PredProofErrEINotExists :: s -> PredProofError s sE o t tType lType
    PredProofErrAddConstErr :: o -> PredProofError s sE o t tType lType
    PredProofErrEIConstDefined :: o -> PredProofError s sE o t tType lType
    PredProofErrEGNotExists :: s -> PredProofError s sE o t tType lType
    PredProofErrUINotForall :: s -> PredProofError s sE o t tType lType
    PredProofErrEGNotGeneralization :: t -> lType -> PredProofError s sE o t tType lType
    PredProofErrEGTermTypeMismatch :: t -> tType -> lType -> PredProofError s sE o t tType lType
    PredProofErrUITermTypeMismatch :: t -> tType -> s -> tType -> PredProofError s sE o t tType lType
    PredProofTermSanity :: sE ->  PredProofError s sE o t tType lType
   deriving (Show)

data PredLogR s sE o t tType lType where
   -- t is a term
    PredProofProp :: PropLogR tType s sE o -> PredLogR s sE o t tType lType
    PredProofByAsm :: ProofByAsmSchema s [PredLogR s sE o t tType lType] -> PredLogR s sE o t tType lType
    PredProofByUG :: ProofByUGSchema lType [PredLogR s sE o t tType lType] -> PredLogR s sE o t tType lType
    PredProofEI :: s -> o -> PredLogR s sE o t tType lType
       -- sentence of form E x . P, and a constant
    PredProofEG :: t -> lType -> PredLogR s sE o t tType lType
        -- a free term,
        -- a sentence of the form E x . P
        -- Instantiate s using term t,
        -- If the resulting sentence is already proven, then the generalization is OK, and that is sentence s.BErrAsmSanity
    PredProofUI :: t -> s -> PredLogR s sE o t tType lType

    PredProofTheorem :: TheoremSchema s [PredLogR s sE o t tType lType] o tType -> PredLogR s sE o t tType lType
    PredProofTheoremM :: TheoremSchemaM tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o -> 
                             PredLogR s sE o t tType lType
    deriving(Show)


standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType eL r s o m (s,[Int])
standardRuleM rule = do
     (state,steps) <- monadifyProofStd rule
     (return . head . assocs . provenSents) state

mpM :: (Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, 
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m, 
       StdPrfPrintMonad s o tType (Either SomeException))
          => s -> ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m (s,[Int])
mpM impl = standardRuleM [MP impl]
      

plSimpLM :: (Monad m, Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, 
       Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m, 
       StdPrfPrintMonad s o tType (Either SomeException)) =>
            s -> ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m (s,[Int])
plSimpLM aAndB = standardRuleM [PLSimpL aAndB]


plAdjM :: (Monad m, Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), StdPrfPrintMonad s o tType m, 
       StdPrfPrintMonad s o tType (Either SomeException))
         => s -> s-> ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m (s,[Int])
plAdjM a b = standardRuleM [PLAdj a b]


predProofUIM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), Typeable lType,
                Show lType, StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException))
                   => t -> s -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofUIM term sent = standardRuleM [PredProofUI term sent]




predProofEIM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType, StdPrfPrintMonad s o tType m, 
                StdPrfPrintMonad s o tType (Either SomeException))
                   => s -> o -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofEIM sent const = standardRuleM [PredProofEI sent const]


predProofPropM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType, StdPrfPrintMonad s o tType (Either SomeException))
                    => ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m x ->
                     ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m x
predProofPropM = modifyPS (fmap PredProofProp)         

predProofMPM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType, StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException))
                   => s -> ProofGenTStd tType  (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofMPM = predProofPropM . mpM

predProofSimpLM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType, StdPrfPrintMonad s o tType m, StdPrfPrintMonad s o tType (Either SomeException))
                   => s -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofSimpLM = predProofPropM . plSimpLM

predProofAdjM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType, StdPrfPrintMonad s o tType m, 
                StdPrfPrintMonad s o tType (Either SomeException))
                   => s -> s -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofAdjM a b = predProofPropM $ plAdjM a b




predProofMP :: s -> PredLogR s sE o t tType lType
predProofMP a = PredProofProp  (MP a)






predProofSimpL :: s -> PredLogR s sE o t tType lType
predProofSimpL a = PredProofProp  (PLSimpL a)
predProofAdj :: s -> s -> PredLogR s sE o t tType lType
predProofAdj a b = PredProofProp  (PLAdj a b)


predPrfRunProof :: (PredLogicSent s t tType lType,
               ProofStd s (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] o tType,
               Show sE, Typeable sE, Show s, Typeable s, TypeableTerm t o tType sE, TypedSent o tType sE s,
               Typeable o, Show o,Typeable tType, Show tType, Show t, Typeable t,
               Typeable lType, Show lType, StdPrfPrintMonad s o tType (Either SomeException)) =>
                            PrfStdState s o tType -> PrfStdContext tType -> PredLogR s sE o t tType lType ->
                                    Either (PredProofError s sE o t tType lType) (s,Maybe (o,tType),PrfStdStep s o tType)
predPrfRunProof state context rule = 
      case rule of
          PredProofProp propR -> do
               (sent,step) <- left  PredProofErrPL (pLrunProof state context propR)
               return (sent, Nothing, step)
          PredProofByAsm schema -> do
               (implication,step) <- left PredProofPrfByAsmErr (proofByAsm state context schema)
               return (implication, Nothing, step)
          PredProofTheorem schema -> do
               step <- left PredProofErrTheorem (establishTheorem schema state context)
               return (theorem schema, Nothing, step)
          PredProofTheoremM schema -> do
               (theorem,step) <- left PredProofErrTheoremM (establishTheoremM state context schema)
               return (theorem,Nothing, step)
          PredProofByUG schema -> do
               (generalized,step) <- left PredProofErrUG (proofByUG state context schema)
               return (generalized,Nothing, step)
          PredProofEI existsSent const -> do 
               let existsParse = parseExists existsSent
               lambda <- maybe ((throwError . PredProofErrEINotExists) existsSent) return existsParse
               let mayExistsSentIdx = Data.Map.lookup existsSent (provenSents state)
               existsSentIdx <- maybe ((throwError . PredProofErrEINotProven) existsSent) return mayExistsSentIdx
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . PredProofErrEIConstDefined) const)
               let f = lType2Func lambda
               let eIResultSent = (f . const2Term) const
               let tType = lTypeTType lambda
               return (eIResultSent,Just (const,tType), PrfStdStepStep eIResultSent "EI" [existsSentIdx])
          PredProofEG term lambda -> do
               let eitherTermType = getTypeTerm term varStack constDict
               termType <- left PredProofTermSanity eitherTermType
               let tType = lTypeTType lambda
               unless (tType == termType) ((throwError .  PredProofErrEGTermTypeMismatch term termType) lambda)
               let f = lType2Func lambda
               let sourceSent = f term
               let maySourceSentIdx = Data.Map.lookup sourceSent (provenSents state)
               sourceSentIdx <- maybe ((throwError . PredProofErrEGNotGeneralization term) lambda) return maySourceSentIdx
               let existsSent = lType2Exists lambda
               return (existsSent,Nothing, PrfStdStepStep sourceSent "EG" [sourceSentIdx])
          PredProofUI term forallSent -> do
               let mayForallSentIdx = Data.Map.lookup forallSent (provenSents state)
               forallSentIdx <- maybe ((throwError . PredProofErrUINotProven) forallSent) return mayForallSentIdx
               let forallParse = parseForall forallSent
               lambda <- maybe ((throwError . PredProofErrUINotForall) forallSent) return forallParse
               let eitherTermType = getTypeTerm term varStack constDict
               termType <- left PredProofTermSanity eitherTermType
               let tType = lTypeTType lambda
               unless (tType == termType) ((throwError .  PredProofErrUITermTypeMismatch term termType forallSent) tType)
               let f = lType2Func lambda
               return (f term,Nothing, PrfStdStepStep (f term) "UI" [forallSentIdx])
    where
        proven = (keysSet . provenSents) state
        constDict = fmap fst (consts state)
        varStack = freeVarTypeStack context




instance (PredLogicSent s t tType lType, Show sE, Typeable sE, Show s, Typeable s, TypedSent o tType sE s,
             TypeableTerm t o tType sE, Typeable o, Show o, Typeable tType, Show tType,
             Monoid (PrfStdState s o tType), Show t, Typeable t, Typeable lType, Show lType,
             StdPrfPrintMonad s o tType (Either SomeException)) 
          => Proof (PredProofError s sE o t tType lType) 
             [PredLogR s sE o t tType lType] 
             (PrfStdState s o tType) 
             (PrfStdContext tType)
             [PrfStdStep s o tType] where

    runProof :: (PredLogicSent s t tType lType, Show sE, Typeable sE, Show s, Typeable s,
                 TypedSent o tType sE s, TypeableTerm t o tType sE, Typeable o,
                 Show o, Typeable tType, Show tType) =>
                    PrfStdContext tType -> [PredLogR s sE o t tType lType]
                     -> PrfStdState s o tType
                     -> Either (PredProofError s sE o t tType lType) (PrfStdState s o tType,[PrfStdStep s o tType])
    runProof context rs oldState = foldM f (PrfStdState mempty mempty 0,[]) rs
       where
           f (newState,newSteps) r =  fmap g (predPrfRunProof (oldState <> newState) context r)
             where
                 g ruleResult = case ruleResult of
                    (s,Nothing,step) -> (newState <> PrfStdState (Data.Map.insert s newLineIndex mempty) mempty 1,
                                         newSteps <> [step])
                    (s,Just (newConst,tType), step) -> (newState <> 
                            PrfStdState (Data.Map.insert s newLineIndex mempty) 
                               (Data.Map.insert newConst (tType,newLineIndex) mempty) 1,
                               newSteps <> [step])
                    where
                        newStepCount = stepCount newState + 1
                        newLineIndex = stepIdxPrefix context <> [stepCount oldState + newStepCount-1]

                     




 
data PropDeBr where
      Neg :: PropDeBr -> PropDeBr
      (:&&:)  :: PropDeBr -> PropDeBr -> PropDeBr
      (:||:) :: PropDeBr -> PropDeBr -> PropDeBr
      (:->:)  :: PropDeBr -> PropDeBr -> PropDeBr
      (:<->:) :: PropDeBr -> PropDeBr -> PropDeBr
      (:==:) :: ObjDeBr -> ObjDeBr -> PropDeBr
      (:<-:) :: ObjDeBr -> ObjDeBr -> PropDeBr
      Forall :: PropDeBr -> PropDeBr
      Exists :: PropDeBr -> PropDeBr
      (:>=:) :: ObjDeBr -> ObjDeBr -> PropDeBr
    deriving (Eq, Ord)


infixr 3 :&&:
infixr 2 :||:
infixr 0 :->:
infixr 0 :<->:
infix  4 :==:
infix  4 :<-:
infix  4 :>=:

data SubexpParseTree where
    BinaryOp :: Text -> SubexpParseTree -> SubexpParseTree -> SubexpParseTree
    UnaryOp :: Text -> SubexpParseTree ->SubexpParseTree
    Binding :: Text -> Int -> SubexpParseTree -> SubexpParseTree
    Atom :: Text -> SubexpParseTree



class SubexpDeBr sub where
    toSubexpParseTree :: sub -> SubexpParseTree




binaryOpInData :: [(Text,(Associativity,Int))]
binaryOpInData = [("=",(NotAssociative,5)),("→",(RightAssociative,1)),("↔",(RightAssociative,1)),("∈",(NotAssociative,5)),("∧",(RightAssociative,4)),("∨",(RightAssociative,3)),
     ("≥",(NotAssociative,5))]


--The Int is it's precedence number.
binaryOpData :: Map Text (Associativity, Int)
binaryOpData = Data.Map.fromList binaryOpInData


instance SubexpDeBr ObjDeBr where
    toSubexpParseTree :: ObjDeBr -> SubexpParseTree
    toSubexpParseTree obj = case obj of
        Integ i -> (Atom . pack . show) i
        Constant c -> Atom c
        Hilbert p -> Binding "ε" (boundDepthPropDeBr p) (toSubexpParseTree p)
        Bound i -> Atom $ "𝑥" <> showIndexAsSubscript i
        Free i -> Atom $ "𝑣" <> showIndexAsSubscript i      


instance SubexpDeBr PropDeBr where
  toSubexpParseTree :: PropDeBr -> SubexpParseTree
  toSubexpParseTree p = case p of
    Neg q -> UnaryOp "¬" (toSubexpParseTree q)
    (:&&:) a b -> BinaryOp "∧" (toSubexpParseTree a) (toSubexpParseTree b)
    (:||:) a b -> BinaryOp "∨" (toSubexpParseTree a) (toSubexpParseTree b)
    (:->:)  a b -> BinaryOp "→" (toSubexpParseTree a) (toSubexpParseTree b)
    (:<->:) a b -> BinaryOp "↔"(toSubexpParseTree a) (toSubexpParseTree b)
    (:==:) a b -> BinaryOp "=" (toSubexpParseTree a) (toSubexpParseTree b)
    (:<-:) a b -> BinaryOp "∈" (toSubexpParseTree a) (toSubexpParseTree b)
    Forall a -> Binding "∀" (boundDepthPropDeBr a) (toSubexpParseTree a)
    Exists a -> Binding "∃" (boundDepthPropDeBr a) (toSubexpParseTree a)
    (:>=:) a b -> BinaryOp "≥" (toSubexpParseTree a) (toSubexpParseTree b)

showSubexpParseTree :: SubexpParseTree -> Text
showSubexpParseTree sub = case sub of
    UnaryOp opSymb sub1 ->
           opSymb
        <> case sub1 of
              UnaryOp _ _ -> showSubexpParseTree sub1
              BinaryOp {} -> "(" <>  showSubexpParseTree sub1 <> ")"
              Binding {} -> showSubexpParseTree sub1
              Atom _ -> showSubexpParseTree sub1
    BinaryOp opSymb sub1 sub2 ->
           case sub1 of
              UnaryOp _ _ -> showSubexpParseTree sub1
              BinaryOp opSymbL _ _ -> 
                 (   
                   if prec opSymb < prec opSymbL
                      || prec opSymb == prec opSymbL 
                          && assoc opSymbL == LeftAssociative && assoc opSymb == LeftAssociative
                    then
                        showSubexpParseTree sub1
                    else
                        "(" <> showSubexpParseTree sub1 <> ")"

                   )
              Binding {} -> showSubexpParseTree sub1
              Atom _ -> showSubexpParseTree sub1
          <> " " <> opSymb <> " "
          <> case sub2 of
               UnaryOp _ _-> showSubexpParseTree sub2
               BinaryOp opSymbR _ _ -> 
                 (
                  if prec opSymb < prec opSymbR
                      || prec opSymb == prec opSymbR 
                          && assoc opSymbR == RightAssociative && assoc opSymb == RightAssociative
                    then
                        showSubexpParseTree sub2
                    else
                        "(" <> showSubexpParseTree sub2 <> ")"
                   )
               Binding {} -> showSubexpParseTree sub2
               Atom _ -> showSubexpParseTree sub2
    Binding quant idx sub1 -> quant <> "𝑥" <> showIndexAsSubscript idx <> "(" <> showSubexpParseTree sub1 <> ")" 
    Atom text -> text       
  where
    assoc opSymb = fst $ binaryOpData!opSymb
    prec opSymb = snd $ binaryOpData!opSymb


instance Show ObjDeBr where
    show :: ObjDeBr -> String
    show = unpack . showSubexpParseTree . toSubexpParseTree                         


instance Show PropDeBr where
    show :: PropDeBr -> String
    show = unpack . showSubexpParseTree . toSubexpParseTree
           






data ObjDeBr where
      Integ :: Int -> ObjDeBr
      Constant :: Text -> ObjDeBr
      Hilbert :: PropDeBr -> ObjDeBr
      Bound :: Int -> ObjDeBr
      Free :: Int ->ObjDeBr
   deriving (Eq, Ord)


data LambdaDeBr where
    Lambda :: PropDeBr -> LambdaDeBr




instance Show LambdaDeBr where
    show :: LambdaDeBr -> String
    show (Lambda p) = "λ𝑥" <> (unpack . showIndexAsSubscript . boundDepthPropDeBr) p 
                           <>"(" <> show p <> ")"


data DeBrSe where
    ObjDeBrSeConstNotDefd :: Text -> DeBrSe
    ObjDeBrBoundVarIdx :: Int -> DeBrSe
    ObjDeBrFreeVarIdx :: Int -> DeBrSe
   deriving Show


boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     Integ num -> 0
     Constant name -> 0
     Hilbert prop -> boundDepthPropDeBr prop + 1
     Bound idx -> 0
     Free idx -> 0


checkSanityObjDeBr :: ObjDeBr -> Int -> Set Text -> Set Int -> Maybe DeBrSe

checkSanityObjDeBr obj varStackHeight constSet boundSet = case obj of
     Integ num -> Nothing
     Constant name -> if name `Set.member` constSet then
                           Nothing
                       else
                           (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> checkSanityPropDeBr prop varStackHeight constSet 
                            (Set.insert (boundDepthPropDeBr prop) boundSet )
     Bound idx -> 
        if idx `Set.member` boundSet then
            Nothing
        else
            (return . ObjDeBrBoundVarIdx) idx
     Free idx ->
        if idx >= 0 && idx < varStackHeight then
            Nothing
        else
            (return . ObjDeBrFreeVarIdx) idx



boundDepthPropDeBr :: PropDeBr -> Int
boundDepthPropDeBr p = case p of
    Neg p -> boundDepthPropDeBr p
    (:&&:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:||:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:->:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:<->:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:<-:) o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    (:==:) o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    Forall p -> boundDepthPropDeBr p + 1
    Exists p -> boundDepthPropDeBr p + 1
    (:>=:) o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)

checkSanityPropDeBr :: PropDeBr -> Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityPropDeBr prop freevarStackHeight consts boundVars = 
      case prop of
        Neg p -> checkSanityPropDeBr p freevarStackHeight consts boundVars
        (:&&:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:||:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:->:)  p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:<->:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:<-:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars
        (:==:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars
        Forall prop -> checkSanityPropDeBr prop freevarStackHeight consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        Exists prop -> checkSanityPropDeBr prop freevarStackHeight consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        (:>=:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars




instance TypeableTerm ObjDeBr Text () DeBrSe where
 
     getTypeTerm :: ObjDeBr -> [()] -> Map Text () -> Either DeBrSe ()
     getTypeTerm term vs constDict = 
         maybe (return ()) throwError (checkSanityObjDeBr term (Prelude.length vs) (keysSet constDict) mempty)
     const2Term :: Text -> ObjDeBr
     const2Term = Constant
     free2Term :: Int -> ObjDeBr
     free2Term = Free


instance TypedSent  Text () DeBrSe PropDeBr where
    checkSanity :: [()] -> PropDeBr -> Map Text () -> Maybe DeBrSe
    checkSanity freeVarStack prop constDict = checkSanityPropDeBr
        prop (Prelude.length freeVarStack) (keysSet constDict) mempty



instance PropLogicSent PropDeBr () where
  
  (.&&.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.&&.) = (:&&:)

  parseAdj :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseAdj p = case p of
                 (:&&:) p1 p2 -> Just (p1,p2) 
                 _ -> Nothing

  (.->.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.->.) = (:->:)

  parse_implication :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parse_implication p = case p of
                 (:->:) p1 p2 -> Just (p1,p2) 
                 _ -> Nothing


  neg :: PropDeBr -> PropDeBr
  neg = Neg

  parseNeg :: PropDeBr -> Maybe PropDeBr
  parseNeg p = case p of
    Neg p1 -> Just p1
    _ -> Nothing

  (.||.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.||.) = (:||:)
  parseDis :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseDis p = case p of
                 (:||:) p1 p2 -> Just(p1,p2)
                 _ -> Nothing

objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx =
    case obj of
        Integ num -> False
        Constant const -> False
        Hilbert p -> propDeBrBoundVarInside p idx
        Bound i -> idx == i
        Free i -> False



propDeBrBoundVarInside :: PropDeBr -> Int -> Bool
propDeBrBoundVarInside prop idx = case prop of
    Neg p -> propDeBrBoundVarInside p idx
    (:&&:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:||:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:->:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:<->:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:==:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    (:<-:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    Forall p -> propDeBrBoundVarInside p idx
    Exists p -> propDeBrBoundVarInside p idx
    (:>=:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx


objDeBrSub :: Int -> Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSub boundVarIdx boundvarOffsetThreshold obj t = case obj of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)                            
    Bound idx 
                 | idx==boundVarIdx -> t
                 | idx >= boundvarOffsetThreshold -> Bound (idx + termDepth)
                 | idx < boundVarIdx -> Bound idx

    Free idx -> Free idx
  where
        termDepth = boundDepthObjDeBr t
        calcBVOThreshold p = if propDeBrBoundVarInside p boundVarIdx then
                                  boundDepthPropDeBr p
                             else boundvarOffsetThreshold

propDeBrSub :: Int -> Int -> PropDeBr -> ObjDeBr -> PropDeBr
propDeBrSub boundVarIdx boundvarOffsetThreshold prop t = case prop of
    Neg p -> Neg (propDeBrSub boundVarIdx boundvarOffsetThreshold p t)
    (:&&:) p1 p2 ->  (:&&:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t) 
    (:||:) p1 p2 ->  (:||:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t) 
    (:->:) p1 p2 ->  (:->:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t)
    (:<->:) p1 p2 ->  (:<->:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t)
    (:==:) o1 o2 -> (:==:) (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)   
    (:<-:) o1 o2 -> (:<-:) (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)  
    Forall p -> Forall (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)
    Exists p -> Exists (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)
    (:>=:) o1 o2 -> (:>=:) (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)
  where
          calcBVOThreshold p = if propDeBrBoundVarInside p boundVarIdx then
                                      boundDepthPropDeBr p
                               else boundvarOffsetThreshold 


objDeBrApplyUG :: ObjDeBr -> Int -> Int -> ObjDeBr
objDeBrApplyUG obj freevarIdx boundvarIdx =
    case obj of
        Integ num -> Integ num
        Constant name -> Constant name
        Hilbert p1 -> Hilbert (propDeBrApplyUG p1 freevarIdx boundvarIdx)
        Bound idx -> Bound idx
        Free idx -> if idx == freevarIdx then
                               Bound boundvarIdx
                           else
                               Free idx 



propDeBrApplyUG :: PropDeBr -> Int -> Int -> PropDeBr
propDeBrApplyUG prop freevarIdx boundvarIdx =
    case prop of
        Neg p -> Neg (propDeBrApplyUG p freevarIdx boundvarIdx)
        (:&&:) p1 p2 -> (:&&:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx) 
        (:||:) p1 p2 -> (:||:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (:->:) p1 p2 -> (:->:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (:<->:) p1 p2 -> (:<->:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (:==:) o1 o2 -> (:==:) (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        (:<-:) o1 o2 -> (:<-:) (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        Forall p -> Forall (propDeBrApplyUG p freevarIdx boundvarIdx)
        Exists p -> Exists (propDeBrApplyUG p freevarIdx boundvarIdx)
        (:>=:) o1 o2 -> (:>=:) (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)




assignNullIndices :: Ord s => [s] -> Map s [Int]
assignNullIndices = Prelude.foldr f mempty
     where f el = Data.Map.insert el []


createInitialState :: (Ord o, Ord s) => [s] -> [o] -> PrfStdState s o ()
createInitialState sents consts = PrfStdState (assignNullIndices sents) 
                           (fmap (\x -> ((),x)) (assignNullIndices consts)) 0




createInitialContext :: PrfStdContext ()
createInitialContext = PrfStdContext [] [] [] 



instance PredLogicSent PropDeBr ObjDeBr () LambdaDeBr where
    parseExists :: PropDeBr -> Maybe LambdaDeBr
    parseExists prop =
      case prop of
          Exists p -> Just $ Lambda p
          _ -> Nothing
    parseForall :: PropDeBr -> Maybe LambdaDeBr
    parseForall prop =
        case prop of
           Forall p -> Just $ Lambda p
           _ -> Nothing

    createLambda :: PropDeBr -> () -> Int -> LambdaDeBr
    createLambda prop () idx = Lambda (propDeBrApplyUG prop idx (boundDepthPropDeBr prop))

    lType2Func :: LambdaDeBr -> (ObjDeBr -> PropDeBr)
    lType2Func (Lambda p) = propDeBrSub (boundVarIdx p) (calcBVOThreshold p) p
           where boundVarIdx = boundDepthPropDeBr
                 calcBVOThreshold p = if propDeBrBoundVarInside p (boundVarIdx p) then
                                      boundDepthPropDeBr p
                                  else 
                                      boundDepthPropDeBr p + 1 
    lType2Forall :: LambdaDeBr -> PropDeBr
    lType2Forall (Lambda p)= Forall p

    lType2Exists :: LambdaDeBr -> PropDeBr
    lType2Exists (Lambda p)= Forall p

    lTypeTType :: LambdaDeBr -> ()
    lTypeTType l = ()
        



type PropErrDeBr = PropLogError PropDeBr DeBrSe Text ObjDeBr
type PropRuleDeBr = PropLogR () PropDeBr DeBrSe Text

type PredErrDeBr = PredProofError PropDeBr DeBrSe Text ObjDeBr () LambdaDeBr
type PredRuleDeBr = PredLogR PropDeBr DeBrSe Text ObjDeBr () LambdaDeBr


type PrfStdStepPredDeBr = PrfStdStep PropDeBr Text ()

subscriptCharTable :: [Text]
subscriptCharTable = ["₀","₁","₂","₃","₄","₅","₆","₇","₈","₉"]

showIndexAsSubscript :: Int -> Text
showIndexAsSubscript n =  Data.Text.concat (Prelude.map f (show n))
      where
          f char = subscriptCharTable!!read [char]




showPropDeBrStep :: [Bool] -> [Int] ->Int -> Bool -> Bool -> PrfStdStepPredDeBr -> Text
showPropDeBrStep contextFrames index lineNum notFromMonad isLastLine step =
        Data.Text.concat (Prelude.map mapBool contextFrames)
          <> showIndex index 
          <> (if (not . Prelude.null) index then "." else "")
          <> (pack . show) lineNum
          <> ": "
          <> showStepInfo
      where
        mapBool frameBool =  if frameBool
                                then
                                    "┃"
                                else
                                    "│"
        showIndices idxs = if Prelude.null idxs then "" else "[" 
                            <> Data.Text.concat (intersperse "," (Prelude.map showIndexDepend idxs))
                            <> "]"
        showIndexDepend i = if Prelude.null i then "?" else showIndex i 
        showIndex i = Data.Text.concat (intersperse "." (Prelude.map (pack . show) i))
        showStepInfo = 
          case step of
             PrfStdStepStep prop justification depends -> 
                  (pack . show) prop
                <> "    "
                <> justification
                <> showIndices depends
                <> qed
             PrfStdStepLemma prop mayWhereProven ->
                   (pack . show) prop
                <> "    LEMMA"
                <> maybe "" (("[⬅ " <>) . (<> "]"). showIndexDepend) mayWhereProven
                <> qed
             PrfStdStepConst constName _ mayWhereDefined ->
                   "Const "
                <> (pack .show) constName
                <> "    CONSTDEF"
                <> maybe "" (("[⬅ " <>) . (<> "]"). showIndexDepend) mayWhereDefined
             PrfStdTheorem prop steps ->
                   (pack . show) prop
                <> "    THEOREM"
                <> qed
                <> showSubproofF steps True
             PrfStdPrfBySubproof prop subproofName steps ->
                   (pack . show) prop
                <> "    "
                <> subproofName
                <> qed
                <> showSubproofF steps False
             PrfStdTheoremM prop  ->
                   (pack . show) prop
                <> "    PRF_BY_THEOREM_M"
                <> qed
             PrfStdStepFreevar index _ ->
                   "FreeVar 𝑣"
                <> showIndexAsSubscript index
                <> "    VARDEF"        
             where
                showSubproofF steps isTheorem = 
                    if notFromMonad then
                          "\n"
                       <> showPropDeBrSteps (contextFrames <> [isTheorem]) newIndex 0 notFromMonad steps
--                       <> " ◻"
                       <> "\n"
                       <> Data.Text.concat (Prelude.map mapBool contextFrames) 
                               <> cornerFrame
                      else ""
                     where
                        newIndex = if isTheorem then [] else index <> [lineNum]
                        cornerFrame = if isTheorem then
                                 "┗"
                              else
                                  "└"
                qed = if notFromMonad && isLastLine then " ◻" else ""


instance StdPrfPrintMonadFrame IO where
    printStartFrame :: [Bool] -> IO ()
    printStartFrame contextFrames = do
        unless (Prelude.null contextFrames) ( do
            let mapBool frameBool = 
                                   if frameBool
                                   then
                                      "┃"
                                   else
                                      "│"
            let contextFramesPre = Prelude.take (length contextFrames - 1) contextFrames
            let cornerBool =  last contextFrames
            let cornerFrame = if cornerBool then
                                 "┏"
                              else
                                  "┌"
            let frames = Data.Text.concat (Prelude.map mapBool contextFramesPre) <> cornerFrame 
            (putStrLn . unpack) frames
            )




instance StdPrfPrintMonadFrame (Either SomeException) where
    printStartFrame :: [Bool] -> Either SomeException ()
    printStartFrame _ = return ()

instance StdPrfPrintMonad PropDeBr Text () IO where
  printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep PropDeBr Text ()] -> IO ()
  printSteps contextFrames idx stepStart steps = do
    let outputTxt = showPropDeBrSteps contextFrames idx stepStart False steps
    (putStrLn . unpack) outputTxt

  printMReturn :: [Bool] -> PropDeBr -> [Int] -> IO ()
  printMReturn contextFrames s index = do
    let showIndex i = Data.Text.concat (intersperse "." (Prelude.map (pack . show) i))
    let mapBool frameBool =  if frameBool
                                then
                                    "┃"
                                else
                                    "│"
    let frames = Data.Text.concat (Prelude.map mapBool contextFrames)
    let outputTxt = frames <> "MReturn: " <> (pack . show) s <> " [" <> showIndex index <> "]"
    (putStrLn . unpack) outputTxt
    return ()

instance StdPrfPrintMonad PropDeBr Text () (Either SomeException) where
  printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep PropDeBr Text ()] -> Either SomeException ()
  printSteps _ _ _ _ = return ()
  printMReturn :: [Bool] -> PropDeBr -> [Int] -> Either SomeException ()
  printMReturn _ _ _ = return ()


showPropDeBrSteps :: [Bool] -> [Int] -> Int -> Bool -> [PrfStdStepPredDeBr] -> Text
showPropDeBrSteps contextFrames index stepStart notFromMonad steps = fst foldResult
    where 
        foldResult = Prelude.foldl f ("", stepStart) steps
           where
             f (accumText,stepNum) step = (accumText 
                                             <> showPropDeBrStep contextFrames index stepNum notFromMonad isLastLine step <> eol,
                                           stepNum + 1)
                  where 
                    isLastLine = stepNum == stepStart + length steps - 1
                    eol = if isLastLine then "" else "\n"



showPropDeBrStepsBase :: [PrfStdStepPredDeBr] -> Text
showPropDeBrStepsBase = showPropDeBrSteps [] [] 0 True






instance Semigroup (PrfStdState PropDeBr Text ()) where
    (<>) :: PrfStdState PropDeBr Text () -> PrfStdState PropDeBr Text () -> PrfStdState PropDeBr Text ()
    (<>) (PrfStdState provenSentsA constsA stepCountA) (PrfStdState provenSentsB constsB stepCountB)
           = PrfStdState (provenSentsA <> provenSentsB) (constsA <> constsB) (stepCountA + stepCountB)

instance Monoid (PrfStdState PropDeBr Text ()) where
  mempty :: PrfStdState PropDeBr Text ()
  mempty = PrfStdState mempty mempty 0

testTheoremMSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => TheoremSchemaMT () PredErrDeBr [PredRuleDeBr] PropDeBr Text m ()
testTheoremMSchema = TheoremSchemaMT [z1,z2] theoremProg [("N",())]
  where
    z1 = Forall (Bound 0  :<-: (Constant . pack) "N" :&&: Bound 0 :>=: Integ 10 :->: Bound 0 :>=: Integ 0)
    z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
    z3 = (Integ 0 :>=: Integ 0) :||: ((Integ 0 :>=: Integ 0) :||: (Integ 0 :>=: Integ 0))
    z4 = ((Integ 0 :>=: Integ 0) :||: (Integ 0 :>=: Integ 0)) :||: (Integ 0 :>=: Integ 21)
    z5 = (Integ 0 :>=: Integ 0) :->: ((Integ 0 :>=: Integ 0) :->: (Integ 0 :>=: Integ 88))


main :: IO ()
main = do
    let y0 =  (Integ 0 :==: Integ 0) :->: (Integ 99 :==: Integ 99)
    let y1 = Integ 0 :==: Integ 0
    let y2= (Integ 99 :==: Integ 99) :->: (Integ 1001 :==: Integ 1001)
    let x0 = Exists (Forall ((Integ 0 :==: Free 102) 
              :&&: (Bound 0 :<-: Bound 1)) :&&: (Bound 1 :<-: Bound 1))
    let x1 = Forall (Forall (Forall ((Bound 3 :==: Bound 2) :&&: Forall (Bound 0 :==: Bound 1))))
    (print . show) (checkSanity [(),()] x0 mempty)
    (print . show) x1
    let f = parseForall x1
    case f of
        Just l -> do
            let term1 = Hilbert (Integ 0 :<-: Integ 0)
            let fNew = lType2Func l term1
            (print.show) fNew
        Nothing -> print "parse failed!"
       --let z = applyUG xn () 102
--    -- (print . show) z
    let proof = [
                  MP y0
                , MP y2
                , PLProofByAsm $ ProofByAsmSchema y1 [MP $ y1 .->. (Integ 99 :==: Integ 99)] (Integ 99 :==: Integ 99)
                ] 



    let zb = runProof createInitialContext proof (createInitialState [y0,y1,y2] []) 
    either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb
    print "OI leave me alone"
    let z1 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10)) :->: (Bound 0 :>=: Integ 0))
    let z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
    let generalizable = Lambda (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10)) :->: (Bound 0 :==: Integ 0))
    let asm = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
    let mid = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 0)
    let proof2 = [
                    PredProofByUG (ProofByUGSchema generalizable
                                     [
                                        PredProofByAsm (ProofByAsmSchema asm [
                                             PredProofUI (Free 0) z1,
                                             predProofMP $ asm .->. (Free 0 :>=: Integ 0),
                                             predProofSimpL $ (:&&:) (Free 0  :<-: (Constant . pack) "N") (Free 0 :>=: Integ 10),
                                             predProofAdj (Free 0  :<-: (Constant . pack) "N") (Free 0 :>=: Integ 0),
                                             PredProofUI (Free 0) z2,
                                             predProofMP $ mid .->. (Free 0 :==: Integ 0)
                                        ]  (Free 0 :==: Integ 0))
                                     ]
                                  )
                 ]

    let proof3 = [
                    PredProofByUG (ProofByUGSchema generalizable
                                     [
                                        PredProofByAsm (ProofByAsmSchema asm [
                                             PredProofUI (Free 0) z1,
                                              
                                             predProofMP $ asm .->. (Free 0 :>=: Integ 0)
                                      
                                        ]  z1)
                                     ]
                                  )
                 ]
    let zb2 = runProof createInitialContext proof2 (createInitialState [z1,z2] ["N"])

    

    let zb3 = runProof createInitialContext [PredProofUI (Free 0) z1] (createInitialState [z1,z2] ["N"])
    either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd)  zb2
    either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb3
    (a,b,c,d) <- runProofGeneratorT testprog createInitialContext (createInitialState [z1,z2] ["N"])
    print "hi wattup"
    (putStrLn . unpack . showPropDeBrStepsBase) d
    print "YOYOYOYOYOYOYOYOYOYO"
    (a,b,c,d,e) <- checkTheoremMConsistency testTheoremMSchema
    print "yo"
    (putStrLn . unpack . showPropDeBrStepsBase) d
    return ()


testprog::ProofGenTStd () PredErrDeBr [PredRuleDeBr] PropDeBr Text IO ()
testprog = do
      let z1 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10))  :->: (Bound 0 :>=: Integ 0))
      let z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
      let generalizable = ((Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)) :->: (Free 0 :==: Integ 0)
      let asm = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
      let asm2 = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
      let mid = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 0)
      fux<- runProofByUGM () (\schm -> [PredProofByUG schm]) do
          runProofByAsmM (\schm -> [PredProofByAsm schm]) asm2 do
              (s1,_) <- predProofUIM (Free 0) z1
              (s2,_) <- predProofMPM s1
              (lift . print) "Coment1"
              (lift . print . show) s1

              (natAsm,_) <- predProofSimpLM asm
              (lift . print) "COmment 2"
              (s3,_) <- predProofAdjM natAsm s2
              (s4,_) <-predProofUIM (Free 0) z2
              (s5,_) <- predProofMPM s4
              runTheoremM (\schm -> [PredProofTheorem schm]) testTheoremMSchema
              return (s5,())
     
      runTheoremM (\schm -> [PredProofTheorem schm]) testTheoremMSchema
 
      return ()

theoremProg::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => ProofGenTStd () PredErrDeBr [PredRuleDeBr] PropDeBr Text m (PropDeBr,())
theoremProg = do
    let z1 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10))  :->: (Bound 0 :>=: Integ 0))
    let z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
    let generalizable = ((Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)) :->: (Free 0 :==: Integ 0)
    let asm = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
    let asm2 = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
    let mid = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 0)
    runProofByUGM () (\schm -> [PredProofByUG schm]) do
          runProofByAsmM (\schm -> [PredProofByAsm schm]) asm2 do
              (s1,_) <- predProofUIM (Free 0) z1
              (s2,_) <- predProofMPM s1
              --(lift . print) "Coment1"
              --(lift . print . show) s1

              (natAsm,_) <- predProofSimpLM asm
              --(lift . print) "COmment 2"
              (s3,_) <- predProofAdjM natAsm s2
              (s4,line_idx) <-predProofUIM (Free 0) z2
              -- (lift . print . show) line_idx
              (s5,_) <- predProofMPM s4
              (s6,_) <- predProofSimpLM asm
              return (s5,())
