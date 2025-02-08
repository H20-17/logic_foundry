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




module Main where



import Data.Monoid
import Data.Functor.Identity ( Identity(runIdentity) )
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.RWS
import Text.XHtml (vspace, name, abbr, p, table, rules)
import Data.Set (Set)
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


default(Text)


class ErrorEmbed e1 e2 where
     errEmbed:: e1-> e2



class Monoid s => Proof e r s c stpT | r -> s, r->e, r->c, r -> stpT  where
      runProof :: c -> r -> s -> Either e (s , stpT)



data ProofGeneratorT stpT eL c r s m x where
  ProofGenInternalT  :: {runProofGenTInternal :: RWST c r s m x}
                   -> ProofGeneratorT stpT eL c r s m x


runProofGeneratorT ::  (Monad m, MonadThrow m, Proof eL r s c stpT) => ProofGeneratorT stpT eL c r s m x -> c -> s -> m (x,s, r)
runProofGeneratorT ps = runRWST (runProofGenTInternal ps)



type ProofGenerator stpT eL c r s x = ProofGeneratorT stpT eL c r s (Either SomeException) x


runProofGenerator :: (Proof eL r s c stpT) => ProofGenerator stpT eL c r s x -> c -> s-> Either SomeException (x, s, r)
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
            catch (runProofGeneratorT z c s) (\err -> runProofGeneratorT (errhandler err) c s))




instance (Monad m, Monoid r, Monad (ProofGeneratorT stpT eL c r s m)) => MonadReader c (ProofGeneratorT stpT eL c r s m) where
   ask ::  ProofGeneratorT stpT eL c r s m c
   ask = ProofGenInternalT  ask
   local :: (c->c) -> ProofGeneratorT stpT eL c r s m a -> ProofGeneratorT stpT eL c r s m a
   local f (ProofGenInternalT  g) = ProofGenInternalT  $ local f g

data MonadifyProofException eL where
  MonadifyProofException :: eL -> MonadifyProofException eL
  deriving (Typeable, Show)


instance (Show eL,Typeable eL) => Exception (MonadifyProofException eL)
monadifyProof :: (Monoid r, Proof eL r s c stpT, Monad m,  MonadThrow m, 
                 Show eL, Typeable eL) => r -> ProofGeneratorT stpT eL c r s m s
monadifyProof p = ProofGenInternalT  $ do
                        c <- ask
                        u <- get
                        let proofResult = runProof c p u
                        resultSet <- either (lift . throwM . MonadifyProofException) (return . fst) proofResult
                        put (u <> resultSet)
                        tell p
                        return resultSet


modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c stpT, 
             Proof eL2 r2 s c stpT,  MonadThrow m, Typeable eL2, Show eL2)
             =>  (r1 -> r2) -> ProofGeneratorT stpT eL1 c r1 s m a
                       -> ProofGeneratorT stpT eL2 c r2 s m a
modifyPS g m1 = do
    c <- ask
    ps <- getProofState
    (datum,_,rules) <- lift $ runProofGeneratorT m1 c ps
    monadifyProof $ g rules
    return datum





---------------------- END KERNEL --------------------------------------------------------------

-------------- SUBPROOFABLE-----------------------------------------------------------------------



data PrfStdContext tType where
    PrfStdContext :: {
        freeVarTypeStack :: [tType],
        stepIdxPrefix :: [Int],
        contextDepth :: Int 
    } -> PrfStdContext tType
    deriving Show

data PrfStdState s o tType where
   PrfStdState :: {
      provenSents :: Map s [Int],
      consts :: Map o (tType, [Int]),
      stepCount :: Int 
   } -> PrfStdState s o tType
   deriving Show



type ProofGenTStd tType eL r s o m x 
               = ProofGeneratorT [PrfStdStep s o tType] eL (PrfStdContext tType) r (PrfStdState s o tType) m x




type ProofStd s eL r o tType = Proof eL r (PrfStdState s o tType) (PrfStdContext tType) [PrfStdStep s o tType]

data PrfStdStep s o tType where
    PrfStdStepStep :: s -> Text -> [[Int]] -> PrfStdStep s o tType
    PrfStdStepLemma :: s -> Maybe [Int] -> PrfStdStep s o tType
    PrfStdStepConst :: o -> tType -> Maybe [Int] -> PrfStdStep s o tType
    PrfStdTheorem :: s -> [PrfStdStep s o tType] -> PrfStdStep s o tType
    PrfStdPrfByUG :: s -> [PrfStdStep s o tType] -> PrfStdStep s o tType
    PrfStdPrfByAsm ::  s -> [PrfStdStep s o tType] -> PrfStdStep s o tType
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




data TestSubproofErr senttype sanityerrtype logicerrtype where
   TestSubproofErrResultNotSane :: senttype -> sanityerrtype -> TestSubproofErr senttype sanityerrtype logicerrtype
   TestSubproofErrorSubproofFailedOnErr :: logicerrtype
                                    -> TestSubproofErr senttype sanityerrtype logicerrtype
   TestSubproofErrorResultNotProved :: senttype -> TestSubproofErr senttype sanityerrtype logicerrtype
   deriving(Show)


testSubproof :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s    )
                       => PrfStdContext tType -> PrfStdState s o tType -> s -> r1 
                             -> Either (TestSubproofErr s sE eL1) [PrfStdStep s o tType]
testSubproof context state consequent subproof =
      --either return (const Nothing) eitherResult
      do
             let frVarTypeStack = freeVarTypeStack context
             let constdict = fmap fst (consts state)
             let sc = checkSanity frVarTypeStack consequent constdict
             maybe (return ()) (throwError . TestSubproofErrResultNotSane consequent) sc
             (newState,steps) <- left TestSubproofErrorSubproofFailedOnErr (runProof context subproof state)
             let alreadyProven = (keysSet  . provenSents) state
             let newlyProven = (keysSet . provenSents) newState
             unless (consequent `Set.member` (newlyProven `Set.union` alreadyProven))
                                 (throwError $ TestSubproofErrorResultNotProved consequent)
             return steps


data TheoremSchema s r o tType where
   TheoremSchema :: {
                       constDict :: Map o tType,
                       lemmas :: Set s,
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
   deriving(Show)


assignSequentialSet :: Ord s => Int -> Set s -> (Int, Map s [Int])
assignSequentialSet base = Set.foldr (\el (i, m) -> (i + 1, Data.Map.insert el [i] m)) (base, mempty)

assignSequentialMap :: Ord o => Int -> Map o tType -> (Int,Map o (tType,[Int]))
assignSequentialMap base = Data.Map.foldrWithKey f (base,mempty)
   where 
      f k v (count,m) = (count+1, Data.Map.insert k (v,[count]) m)

checkTheorem :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType -> Maybe (PrfStdState s o tType,PrfStdContext tType)
                                       -> Either (ChkTheoremError s sE eL1 o tType) [PrfStdStep s o tType]
checkTheorem (TheoremSchema constdict lemmas subproof theorem) mayPrStateCxt =
  do
       maybe (return ()) throwError (maybe g1 g2 mayPrStateCxt)
       preSubproof <- left ChkTheoremErrSubproofErr (testSubproof newContext newState theorem subproof)
       return $ conststeps <> lemmasteps <> preSubproof
      where
         conststeps = Data.Map.foldrWithKey h1 [] constdict
         lemmasteps = Set.foldr h2 [] lemmas
         h1 const constType accumList = accumList <> [PrfStdStepConst const constType (q mayPrStateCxt)]
            where
                 q Nothing = Nothing
                 q (Just (state,_)) = fmap snd (Data.Map.lookup const (consts state)) 
         h2 lemma accumList = accumList <> [PrfStdStepLemma lemma (q mayPrStateCxt)]
            where
                 q Nothing = Nothing
                 q (Just (state,_)) = Data.Map.lookup lemma (provenSents state) 



         newContext = PrfStdContext [] [] (maybe 0  ((+1) . contextDepth . snd) mayPrStateCxt)
         newState = PrfStdState newProven newConsts newStepCountB
              where 
                 (newStepCountA, newConsts) = assignSequentialMap 0 constdict
                 (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
         g2 (PrfStdState alreadyProven alreadyDefinedConsts stepCount, 
                 PrfStdContext freeVarTypeStack stepIdfPrefix contextDepth) 
               = fmap constDictErr (constDictTest (fmap fst alreadyDefinedConsts) constdict)
                                               <|> Prelude.foldr f1 Nothing lemmas
           where
             constDictErr (k,Nothing) = ChkTheoremErrConstNotDefd k
             constDictErr (k, Just (a,b)) = ChkTheoremErrConstTypeConflict k a b
             f1 a = maybe (maybeLemmaMissing <|> maybeLemmaInsane) Just 
               where
                  maybeLemmaMissing = if not (a `Set.member` Data.Map.keysSet alreadyProven)
                                          then (Just . ChkTheoremErrLemmaNotEstablished) a else Nothing
                  maybeLemmaInsane = fmap (ChkTheoremErrLemmaSanity a) (checkSanity mempty a constdict)
         g1  = Prelude.foldr f1 Nothing lemmas
           where
             f1 a = maybe maybeLemmaInsane Just 
               where
                  maybeLemmaInsane = fmap (ChkTheoremErrLemmaSanity a) (checkSanity mempty a constdict)
                     


establishTheorem :: (ProofStd s eL1 r1 o tType, PropLogicSent s tType, TypedSent o tType sE s    )
                            => TheoremSchema s r1 o tType -> PrfStdState s o tType -> PrfStdContext tType
                                       -> Either (ChkTheoremError s sE eL1 o tType) (PrfStdStep s o tType)
establishTheorem schema state context = do
    steps <- checkTheorem schema (Just (state,context))
    let tm = theorem schema
    return (PrfStdTheorem tm steps)




data TheoremSchemaMT tType eL r s o m x where
   TheoremSchemaMT :: {
                       lemmasM :: Set s,
                       proofM :: ProofGenTStd tType eL r s o m (s,x),
                       constDictM :: Map o tType
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


   deriving(Show)


instance (
              Show sE, Typeable sE, 
              Show s, Typeable s,
              Show o, Typeable o,
              Show tType, Typeable tType)
           => Exception (BigException s sE o tType)


checkTheoremM :: (Show s, Typeable s, Monoid r1, ProofStd s eL1 r1 o tType, Monad m, MonadThrow m,
                      PropLogicSent s tType, TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType,
                      Show eL1, Typeable eL1,
                      Typeable o, Show o )
                 =>   Set s -> ProofGenTStd tType eL1 r1 s o m (s, x) -> Map o tType -> 
                      Maybe (PrfStdState s o tType,PrfStdContext tType)
                              -> m (s, r1, x)
checkTheoremM lemmas prog constdict mayPrStateCxt =  do
    maybe (maybe (return ()) throwM g1) (maybe (return ()) throwM . g2) mayPrStateCxt
    let (newStepCountA, newConsts) = assignSequentialMap 0 constdict
    let (newStepCountB, newProven) = assignSequentialSet newStepCountA lemmas
    let newContext = PrfStdContext [] [] (maybe 0  ((+1) . contextDepth . snd) mayPrStateCxt)
    let newState = PrfStdState newProven newConsts newStepCountB
    (extra,tm,proof) <- runSubproofM newState newContext prog
    return (tm,proof,extra)
        where 
            g2 (PrfStdState alreadyProven alreadyDefinedConsts stepCount, PrfStdContext freeVarTypeStack stepIdfPrefix contextDepth) 
                 = fmap constDictErr (constDictTest (fmap fst alreadyDefinedConsts) constdict)
                                               <|> Prelude.foldr f1 Nothing lemmas
             where
                constDictErr (k,Nothing) = BigExceptConstNotDefd k
                constDictErr (k, Just (a,b)) = BigExceptConstTypeConflict k a b
                f1 a = maybe (maybeLemmaInsane <|> maybeLemmaMissing) Just 
                  where
                     maybeLemmaMissing = if not (a `Set.member` Data.Map.keysSet alreadyProven)
                                          then (Just . BigExceptLemmaNotEstablished) a else Nothing
                     maybeLemmaInsane = fmap (BigExceptLemmaSanityErr a) (checkSanity mempty a constdict)
            g1 = Prelude.foldr f1 Nothing lemmas
              where
                 f1 a = maybe maybeLemmaInsane Just 
                   where
                      maybeLemmaInsane = fmap (BigExceptLemmaSanityErr a) (checkSanity mempty a constdict)
  




data EstTmMError s o tType where
    EstTmMErrMExcept :: SomeException -> EstTmMError s o tType
    deriving (Show)
   




establishTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType ,
                     PropLogicSent s tType,
                     Show s, Typeable s, Ord o, TypedSent o tType sE s, Show sE, Typeable sE, Typeable tType, Show tType, Typeable o,
                     Show o, Show eL1, Typeable eL1)
                            => PrfStdState s o tType -> PrfStdContext tType -> 
                                  TheoremSchemaM tType eL1 r1 s o -> Either (EstTmMError s o tType) (s, PrfStdStep s o tType)
establishTheoremM state context ((TheoremSchemaMT lemmas proofprog constdict):: TheoremSchemaM tType eL1 r1 s o) = 
    do
        (tm, prf, ()) <-  left EstTmMErrMExcept $ checkTheoremM lemmas proofprog constdict (Just (state,context))
        return (tm, PrfStdTheoremM tm)



data ExpTmMError where
    ExpTmMErrMExcept :: SomeException -> ExpTmMError
    deriving (Show)


expandTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType ,
                     PropLogicSent s tType, Show s, Typeable s, TypedSent o tType sE s, Show sE, Typeable sE,
                     Show eL1, Typeable eL1,
                     Typeable tType, Show tType, Typeable o, Show o)
                            => TheoremSchemaM tType eL1 r1 s o -> Either ExpTmMError (TheoremSchema s r1 o tType)
expandTheoremM ((TheoremSchemaMT lemmas proofprog constdict):: TheoremSchemaM tType eL1 r1 s o) =
      do
          (tm,r1,()) <- left ExpTmMErrMExcept (checkTheoremM lemmas proofprog constdict Nothing)
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
         let newSents = Data.Map.insert assumption (newStepIdxPrefix ++ [0]) alreadyProven
         let newContextDepth = contextDepth context + 1
         let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextDepth
         let newState = PrfStdState newSents (consts state) 1
         let eitherTestResult = testSubproof newContext newState consequent subproof
         testResult <- either (throwError . ProofByAsmErrSubproofFailedOnErr) return eitherTestResult
         let implication = assumption .->. consequent
         let finalSteps = [PrfStdStepStep assumption "ASM" []] <> testResult
         return (implication, PrfStdPrfByAsm implication finalSteps)


data ProofByUGSchema lType r where
   ProofByUGSchema :: {
                       ugPrfLambda :: lType,
                       ugPrfProof :: r
                    } -> ProofByUGSchema lType r
    deriving (Show)


class (PropLogicSent s tType) => PredLogicSent s t tType lType | lType -> s, lType->tType, lType->t, s->t, s-> lType where
    -- o is the type of constants
    parseExists :: s -> Maybe lType
    -- create generalization from sentence and varstack
    parseForall :: s -> Maybe lType
    -- create generalization from sentence and varstack
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
         let newContextDepth = contextDepth context + 1
         let newContext = PrfStdContext newVarstack newStepIdxPrefix newContextDepth
         let newState = PrfStdState (provenSents state) (consts state) 1
         let newFreeTerm = free2Term $ length varstack
         let generalizable = lType2Func lambda newFreeTerm 
         let eitherTestResult = testSubproof newContext newState generalizable subproof
         testResult <- either (throwError . ProofByUGErrSubproofFailedOnErr) return eitherTestResult
         let generalized = lType2Forall lambda
         let finalSteps = [PrfStdStepFreevar (length varstack) (lTypeTType lambda)] <> testResult
         return  (generalized, PrfStdPrfByUG generalized finalSteps)







runSubproofM :: ( Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                        PropLogicSent s tType, Show eL1, Typeable eL1, Show s, Typeable s,
                        MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE)
                 =>   PrfStdState s o tType -> PrfStdContext tType
                          -> ProofGenTStd tType eL1 r1 s o m (s, x) ->
                          m (x,s,r1)
runSubproofM state context prog =  do
          ((prfResult,extraData),newState,r) <- runProofGeneratorT prog context state
          let constdict = fmap fst (consts state)
          let sc = checkSanity (freeVarTypeStack context) prfResult constdict
          maybe (return ()) (throwM . BigExceptResultSanity prfResult) sc
          let nowProven = (keysSet . provenSents) newState
          unless (prfResult `Set.member` nowProven)
                             ((throwM . BigExceptResNotProven) prfResult)
          return (extraData, prfResult, r)



runTheoremM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                      PropLogicSent s tType, MonadThrow m, Show tType, Typeable tType,
                      Show o, Typeable o, Show s, Typeable s,
                      Show eL1, Typeable eL1, Ord o, TypedSent o tType sE s, Show sE, Typeable sE)
                 =>   (TheoremSchema s r1 o tType -> r1) -> Set s -> ProofGenTStd tType eL1 r1 s o m (s, x) -> Map o tType ->
                               ProofGenTStd tType eL1 r1 s o m (s, x)
runTheoremM f lemmas prog constDict =  do
        state <- getProofState
        context <- ask
        (tm, proof, extra) <- lift $ checkTheoremM lemmas prog constDict (Just (state,context))
        monadifyProof (f $ TheoremSchema constDict lemmas proof tm)
        return (tm, extra)


runProofByAsmM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PropLogicSent s tType, MonadThrow m,
                       Show s, Typeable s,
                       Show eL1, Typeable eL1, TypedSent o tType sE s, Show sE, Typeable sE)
                 =>   (ProofByAsmSchema s r1 -> r1) -> s -> ProofGenTStd tType eL1 r1 s o m (s, x)
                            -> ProofGenTStd tType eL1 r1 s o m (s, x)
runProofByAsmM f asm prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let constdict = fmap fst (consts state)
        let sc = checkSanity frVarTypeStack asm constdict
        maybe (return ()) (throwM . BigExceptAsmSanity asm) sc
        let alreadyProven = provenSents state
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newSents = Data.Map.insert asm (newStepIdxPrefix ++ [0]) alreadyProven
        let newContextDepth = contextDepth context + 1
        let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextDepth
        let newState = PrfStdState newSents (consts state) 1
        (extraData,consequent,subproof) <- lift $ runSubproofM newState newContext prog
        (monadifyProof . f) (ProofByAsmSchema asm subproof consequent)
        return (asm .->. consequent,extraData)



runProofByUGM :: (Monoid r1, ProofStd s eL1 r1 o tType, Monad m,
                       PredLogicSent s t tType lType, Show eL1, Typeable eL1,
                    Show s, Typeable s,
                       MonadThrow m, TypedSent o tType sE s, Show sE, Typeable sE)
                 =>  tType -> (ProofByUGSchema lType r1 -> r1) -> ProofGenTStd tType eL1 r1 s o m (s, x)
                            -> ProofGenTStd tType eL1 r1 s o m (s, x)
runProofByUGM tt f prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let newFrVarTypStack = tt : frVarTypeStack
        let newContextDepth = contextDepth context + 1
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newContext = PrfStdContext newFrVarTypStack newStepIdxPrefix newContextDepth
        let newState = PrfStdState (provenSents state) (consts state) 0
        (extraData,generalizable,subproof) <- lift $ runSubproofM newState newContext prog
        let lambda = createLambda generalizable tt (Prelude.length frVarTypeStack)
        (monadifyProof . f) (ProofByUGSchema lambda subproof)
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
    deriving(Show)



pLrunProof :: (ProofStd s (PropLogError s sE o tType) [PropLogR tType s sE o] o tType,
               PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
               Show o, Typeable o, Typeable tType, Show tType) =>
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





instance (PropLogicSent s tType, Show sE, Typeable sE, Show s, Typeable s, Ord o, TypedSent o tType sE s,
          Typeable o, Show o, Typeable tType, Show tType, Monoid (PrfStdState s o tType))
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
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType)
       => r -> ProofGenTStd tType eL r s o m (s,[Int])
standardRuleM rule = do
     state <- monadifyProof rule
     (return . head . assocs . provenSents) state

mpM :: (Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType))
          => s -> ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m (s,[Int])
mpM impl = standardRuleM [MP impl]
      

plSimpLM :: (Monad m, Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType)) =>
            s -> ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m (s,[Int])
plSimpLM aAndB = standardRuleM [PLSimpL aAndB]


plAdjM :: (Monad m, Monad m, PropLogicSent s tType, Ord o, Show sE, Typeable sE, Show s, Typeable s,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType)   )
         => s -> s-> ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m (s,[Int])
plAdjM a b = standardRuleM [PLAdj a b]


predProofUIM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType), Typeable lType,
                Show lType     )
                   => t -> s -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofUIM term sent = standardRuleM [PredProofUI term sent]




predProofEIM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType)
                   => s -> o -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofEIM sent const = standardRuleM [PredProofEI sent const]


predProofPropM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType)
                    => ProofGenTStd tType (PropLogError s sE o tType) [PropLogR tType s sE o] s o m x ->
                     ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m x
predProofPropM = modifyPS (fmap PredProofProp)         

predProofMPM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType)
                   => s -> ProofGenTStd tType  (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofMPM = predProofPropM . mpM

predProofSimpLM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType)
                   => s -> ProofGenTStd tType (PredProofError s sE o t tType lType) [PredLogR s sE o t tType lType] s o m (s,[Int])
predProofSimpLM = predProofPropM . plSimpLM

predProofAdjM :: (Monad m, PredLogicSent s t tType lType, TypeableTerm t o tType sE, Show s,
                Typeable s, Show sE, Typeable sE, MonadThrow m, Show o, Typeable o, Show t, Typeable t,
                Show tType, Typeable tType, TypedSent o tType sE s, Monoid (PrfStdState s o tType),
                Typeable lType, Show lType )
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
               Typeable lType, Show lType) =>
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
             Monoid (PrfStdState s o tType), Show t, Typeable t, Typeable lType, Show lType) 
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


propNeedsBrackets :: PropDeBr -> Bool
propNeedsBrackets p = case p of
    Neg q -> False
    (:&&:) a b -> True 
    (:||:) a b -> True
    (:->:)  a b -> True
    (:<->:) a b -> True
    (:==:) a b -> True
    (:<-:) a b -> True
    Forall a -> False
    Exists a -> False
    (:>=:) a b -> True


maybeWrapProp :: PropDeBr -> [Char]
maybeWrapProp p = if propNeedsBrackets p then
                          "(" <> show p <> ")"
                       else
                           show p


unaryOpPropShow :: Text -> PropDeBr -> [Char]
unaryOpPropShow opSymb a =
    unpack opSymb <> " " <> maybeWrapProp a



binaryOpPropShow :: Text -> PropDeBr -> PropDeBr -> [Char]
binaryOpPropShow opSymb a b =
    maybeWrapProp a <> " " <> unpack opSymb <> " " <> maybeWrapProp b

                          

binaryOpObjShow :: Text -> ObjDeBr -> ObjDeBr -> [Char]
binaryOpObjShow opSymb a b =
    show a <> " " <> unpack opSymb <> " " <> show b


instance Show PropDeBr where
    show :: PropDeBr -> String
    show prop = case prop of
        Neg a -> unaryOpPropShow "¬" a
        (:&&:) a b -> binaryOpPropShow "∧" a b
        (:||:) a b -> binaryOpPropShow "∨" a b
        (:->:) a b -> binaryOpPropShow "→" a b
        (:<->:) a b -> binaryOpPropShow "↔" a b
        (:==:) a b -> binaryOpObjShow "=" a b
        (:<-:) a b -> binaryOpObjShow "∈" a b
        Forall a ->  "∀𝑥" <> (unpack . showIndexAsSubscript . boundDepthPropDeBr) a <> "(" <> show a <> ")"
        Exists a ->  "∃𝑥" <> (unpack . showIndexAsSubscript . boundDepthPropDeBr) a <> "(" <> show a <> ")"
        (:>=:) a b -> binaryOpObjShow "≥" a b


infixl 9 :&&:
infixl 9 :||:
infixl 9 :->:
infixl 9 :<->:
infixl 9 :==:
infixl 9 :<-:
infixl 9 :>=:




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
    

instance Show ObjDeBr where
    show :: ObjDeBr -> String
    show obj = case obj of
        Integ i -> show i
        Constant c -> unpack c
        Hilbert p -> "ε𝑥" <> (unpack . showIndexAsSubscript . boundDepthPropDeBr) p <> "(" <> show p <> ")"
        Bound i -> "𝑥" <> (unpack . showIndexAsSubscript) i
        Free i -> "𝑣" <> (unpack . showIndexAsSubscript) i        



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
createInitialContext = PrfStdContext [] [] 0 



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




showPredDeBrStep :: Int -> [Int] ->Int  -> PrfStdStepPredDeBr -> Text
showPredDeBrStep contextDepth index lineNum step =
    Data.Text.concat (replicate contextDepth "│")
          <> showIndex index 
          <> (if (not . Prelude.null) index then "." else "")
          <> (pack . show) lineNum
          <> ": "
          <> showStepInfo
      where
        showIndexDepend i = if Prelude.null i then "?" else showIndex i 
        showIndex i = Data.Text.concat (intersperse "." (Prelude.map (pack . show) i))
        showStepInfo = 
          case step of
             PrfStdStepStep prop justification depends -> 
                  (pack . show) prop
                <> " "
                <> justification
                <> "["
                <> Data.Text.concat (intersperse "," (Prelude.map showIndexDepend depends))
                <> "]"
             PrfStdStepLemma prop mayWhereProven ->
                   (pack . show) prop
                <> " LEMMA"
                <> maybe "" (("[^" <>) . (<> "]"). showIndexDepend) mayWhereProven
             PrfStdStepConst constName _ mayWhereDefined ->
                   "Const "
                <> constName
                <> maybe "" (("[^" <>) . (<> "]"). showIndexDepend) mayWhereDefined
             PrfStdTheorem prop steps ->
                   (pack . show) prop
                <> " THEOREM\n"
                <> showPredDeBrSteps (contextDepth + 1) ([]) steps
                <> "\n"
                <> Data.Text.concat (replicate contextDepth "│")
                <> "└"   -- will be unicode corner when I get to it
             PrfStdPrfByUG prop steps ->
                   (pack . show) prop
                <> " PRF_BY_UG\n"
                <> showPredDeBrSteps (contextDepth + 1) (index <> [lineNum]) steps
                <> "\n"
                <> Data.Text.concat (replicate contextDepth "│")
                <> "└"   -- will be unicode corner when I get to it
             PrfStdPrfByAsm prop steps ->
                   (pack . show) prop
                <> " PRF_BY_ASM\n"
                <> showPredDeBrSteps (contextDepth + 1) (index <> [lineNum]) steps
                <> "\n"
                <> Data.Text.concat (replicate contextDepth "│")
                <> "└"   -- will be unicode corner when I get to it
             PrfStdTheoremM prop  ->
                   (pack . show) prop
                <> " PRF_BY_THEOREM_M"
             PrfStdStepFreevar index _ ->
                   "FreeVar 𝑣"
                <> showIndexAsSubscript index

             

showPredDeBrSteps :: Int -> [Int] ->  [PrfStdStepPredDeBr] -> Text
showPredDeBrSteps contextDepth index steps = fst foldResult
    where 
        foldResult = Prelude.foldl f ("", 0) steps
           where
             f (accumText,stepNum) step = (accumText <> showPredDeBrStep contextDepth index stepNum step <> eol,
                                           stepNum + 1)
                  where eol = if stepNum == length steps - 1 then "" else "\n"


showPredDeBrStepsBase :: [PrfStdStepPredDeBr] -> Text
showPredDeBrStepsBase = showPredDeBrSteps 0 []






instance Semigroup (PrfStdState PropDeBr Text ()) where
    (<>) :: PrfStdState PropDeBr Text () -> PrfStdState PropDeBr Text () -> PrfStdState PropDeBr Text ()
    (<>) (PrfStdState provenSentsA constsA stepCountA) (PrfStdState provenSentsB constsB stepCountB)
           = PrfStdState (provenSentsA <> provenSentsB) (constsA <> constsB) (stepCountA + stepCountB)

instance Monoid (PrfStdState PropDeBr Text ()) where
  mempty :: PrfStdState PropDeBr Text ()
  mempty = PrfStdState mempty mempty 0


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
    either (putStrLn . show) (putStrLn . unpack . showPredDeBrStepsBase . snd) zb

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
    let t="shit"
    print "fuck"
    either (putStrLn . show) (putStrLn . unpack . showPredDeBrStepsBase . snd)  zb2
    either (putStrLn . show) (putStrLn . unpack . showPredDeBrStepsBase . snd) zb3
    x <- runProofGeneratorT testprog createInitialContext (createInitialState [z1,z2] ["N"])
    let y = show x
    print "hi wattup"
    --(putStrLn . show) x
    (putStrLn . show) x


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
              return (s5,())
     
      (lift . print . pack . show) fux
      return ()


