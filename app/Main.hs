
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
module Main where

import Data.Monoid
import Data.Functor.Identity ( Identity(runIdentity) )
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.RWS
import Text.XHtml (vspace, name, abbr, p, table)
import Data.Set (Set)
import Data.List (mapAccumL)
import qualified Data.Set as Set
import Data.Text
import Data.Map
import Distribution.Simple (ProfDetailLevel(ProfDetailExportedFunctions))
import Data.Text.Internal.Encoding.Utf8 (ord2)
import Data.Maybe
import GHC.RTS.Flags (MiscFlags(linkerMemBase))
import Control.Applicative
import Control.Monad.Reader
import Control.Arrow
import Control.Monad.Except

import Control.Monad.Error.Class
import Foreign.C (eEXIST, throwErrnoIfMinus1Retry_)
--import Control.Exception
import Control.Monad.Catch
    ( SomeException, MonadCatch(..), MonadThrow(..), Exception )
import qualified GHC.Stack.Types
import Data.Data (Typeable)
import Distribution.PackageDescription (TestType)




class ErrorEmbed e1 e2 where
     errEmbed:: e1-> e2






class Monoid s => Proof e r s c | r -> s, r->e, r->c  where
      runProof :: c -> r -> s -> Either e s



runProofE :: (Proof e1 r s c) => c -> r ->s -> (e1 -> e2) -> Either e2 s
runProofE c r s f = left f (runProof c r s)





data ProofStateT eM eL c r s m x where
  ProofStateTInternal :: {runProofStateTTop :: RWST c r s (ExceptT eM m) x}
                   -> ProofStateT eM eL c r s m x


runProofStateT ::  (Monad m, ErrorEmbed eL eM, Proof eL r s c) => ProofStateT eM eL c r s m x -> c -> s -> m (Either eM (x,s, r))
runProofStateT ps c s = runExceptT $ runRWST (runProofStateTTop ps) c s








type ProofState eM eL c r s x = ProofStateT eM eL c r s (Either SomeException) x


runProofState :: (ErrorEmbed eL eM, Proof eL r s c) => ProofState eM eL c r s x -> c -> s-> Either SomeException (Either eM (x, s, r))
runProofState = runProofStateT





instance (Monad m) => Functor (ProofStateT eM eL c r s m) where
     fmap :: Monad m =>
              (a -> b) -> ProofStateT eM eL c r s m a -> ProofStateT eM eL c r s m b
     fmap f (ProofStateTInternal g) = ProofStateTInternal $ fmap f g







instance (Monoid r, Monad m, Proof eL r s c, ErrorEmbed eL eM) => Applicative (ProofStateT eM eL c r s m) where
   pure :: (Monad m, Proof eL r s c) => a -> ProofStateT eM eL c r s m a
   (<*>) :: (Monad m, Proof eL r s c, ErrorEmbed eL eM) => ProofStateT eM eL c r s m (a -> b)
                                        -> ProofStateT eM eL c r s m a -> ProofStateT eM eL c r s m b
   ProofStateTInternal a <*> ProofStateTInternal b = ProofStateTInternal $ a <*> b
   pure x = ProofStateTInternal $ pure x





instance (Monoid r,Proof eL r s c, Monad m, ErrorEmbed eL eM) => Monad (ProofStateT eM eL c r s m) where
   (>>=) :: (Proof eL r s c, Monad m, ErrorEmbed eL eM) => ProofStateT eM eL c r s m a
                                         -> (a -> ProofStateT eM eL c r s m b)
                                     -> ProofStateT eM eL c r s m b
   ProofStateTInternal y >>= g = ProofStateTInternal (y >>= runProofStateTTop . g)




instance (Monoid r, Proof eL r s c, ErrorEmbed eL eM) =>  MonadTrans (ProofStateT eM eL c r s) where
      lift :: (Monoid r, Monad m) => m a -> ProofStateT eM eL c r s m a
      lift = ProofStateTInternal . lift . lift





getProofState :: (Monoid r, Proof eL r s c, Monad m) => ProofStateT eM eL c r s m s
getProofState = ProofStateTInternal get



instance (Monoid r,Proof eL r s c, Monad m, ErrorEmbed eL eM) => MonadError eM  (ProofStateT eM eL c r s m) where
      throwError :: (Proof eL r s c, Monad m, ErrorEmbed eL eM) => eM -> ProofStateT eM eL c r s m a
      throwError = ProofStateTInternal . lift . throwError

      catchError :: (Proof eL r s c, Monad m, ErrorEmbed eL eM) =>
                     ProofStateT eM eL c r s m a -> (eM -> ProofStateT eM eL c r s m a) -> ProofStateT eM eL c r s m a
      catchError z errHandler = ProofStateTInternal  (RWST \ c s -> ExceptT $ do
                   st <- runProofStateT z c s
                   either (\e -> runProofStateT (errHandler e) c s) (return . Right) st
           )


instance (Monoid r,Proof eL r s c, Monad m, MonadThrow m, ErrorEmbed eL eM) => MonadThrow (ProofStateT eM eL c r s m) where
  throwM :: (Monoid r, Proof eL r s c, Monad m, MonadThrow m, GHC.Stack.Types.HasCallStack, Exception e) =>
                 e -> ProofStateT eM eL c r s m a
  throwM = ProofStateTInternal . lift . throwM


instance (Proof eL r s c, Monoid r, MonadThrow m, MonadCatch m, ErrorEmbed eL eM)  
               => MonadCatch (ProofStateT eM eL c r s m) where
       catch :: (Proof eL r s c, GHC.Stack.Types.HasCallStack, MonadThrow m, MonadCatch m,Exception e) =>
            ProofStateT eM eL c r s m a -> (e -> ProofStateT eM eL c r s m a) -> ProofStateT eM eL c r s m a
       catch z errhandler = ProofStateTInternal (RWST \c s -> ExceptT $ do
            catch (runProofStateT z c s) (\err -> runProofStateT (errhandler err) c s))


instance (Monoid c,Monad m, Monoid r, Monad (ProofStateT eM eL c r s m)) => MonadReader c (ProofStateT eM eL c r s m) where
   ask ::  ProofStateT eM eL c r s m c
   ask = ProofStateTInternal ask
   local :: (c->c) -> ProofStateT eM eL c r s m a -> ProofStateT eM eL c r s m a
   local f (ProofStateTInternal g) = ProofStateTInternal $ local f g




monadifyProof :: (Monoid r, Proof eL r s c, Monad m, ErrorEmbed eL eM) => r -> ProofStateT eM eL c r s m s
monadifyProof p = ProofStateTInternal $ do
                        c <- ask
                        u <- get
                        let proofResult = runProofE c p u errEmbed
                        resultSet <- either (lift . throwError) return proofResult
                        put (u <> resultSet)
                        tell p
                        return resultSet







modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c, Proof eL2 r2 s c,ErrorEmbed eL2 eM2, Monoid c, ErrorEmbed eL1 eM1)
             => (eM1 -> eM2) -> (r1 -> r2) -> ProofStateT eM1 eL1 c r1 s m a
                       -> ProofStateT eM2 eL2 c r2 s m a
modifyPS f g m1 = do
    c <- ask
    ps <- getProofState
    monadResult <- lift $ runProofStateT m1 c ps
    (datum,_,rules) <- either (throwError . f) return monadResult
    monadifyProof $ g rules
    return datum





------------------ END KERNEL --------------------------------------------------------------

---------- SUBPROOFABLE-----------------------------------------------------------------------



data BigException  eL where
    BErrSubproof :: BigException eL -> BigException eL
    BEPrfErr :: eL -> BigException eL
    deriving (Typeable,Show)

instance ErrorEmbed eL (BigException eL) where
     errEmbed::eL -> BigException  eL
     errEmbed = BEPrfErr


type ProofStateGenT tType sE eL r s o m x = ProofStateT (BigException eL) eL [tType] r (Set s,Map o tType) m x

runProofStateGenT ::  (Monad m, Proof eL r (Set s, Map o tType) [tType]) 
                            => ProofStateGenT tType sE eL r s o m x -> [tType] -> Set s -> Map o tType -> m (Either (BigException eL) (x,(Set s,Map o tType), r))
runProofStateGenT p varstack proven constDict = runProofStateT p varstack (proven,constDict)


type ProofStateGen tType sE eL r s o x = ProofState (BigException eL) eL [tType] r (Set s, Map o tType) x
runProofStateGen :: (Proof eL r (Set s, Map o tType) [tType]) =>
                      ProofStateGen tType sE eL r s o x -> [tType] -> Set s -> Map o tType -> Either SomeException (Either (BigException eL) (x,(Set s,Map o tType), r))
runProofStateGen p varstack proven constDict = runProofState p varstack (proven,constDict)


class (Eq tType, Ord o) => TypeableTerm t o tType sE | t -> o, t->tType, t -> sE where
    getTypeTerm :: t -> [tType] -> Map o tType -> Either sE tType
    const2Term :: o -> t
        -- get term type using a varstack and a const dictionary


class (Ord s,TypeableTerm t o tType sE) 
              => PropLogicSent s sE t o tType | s -> sE, s->t where
     checkSanity :: [tType] -> s -> Map o tType -> Maybe sE
     buildAdj :: s -> s -> s
     parseAdj :: s -> Maybe(s,s)
     build_implication:: s->s->s
     parse_implication:: s -> Maybe (s,s)
     buildNot :: s -> s
     parseNot :: s -> Maybe s
     buildDis :: s -> s -> s
     parseDis :: s -> Maybe (s,s)



data TestSubproofErr senttype sanityerrtype logicerrtype where
   TestSubproofErrResultNotSane :: senttype -> sanityerrtype -> TestSubproofErr senttype sanityerrtype logicerrtype
   TestSubproofErrorSubproofFailedOnErr :: logicerrtype
                                    -> TestSubproofErr senttype sanityerrtype logicerrtype
   TestSubproofErrorResultNotProved :: TestSubproofErr senttype sanityerrtype logicerrtype
   deriving(Show)


testSubproof :: (Proof eL1 r1 (Set s, Map o tType) [tType], PropLogicSent s sE t o tType) => [tType] -> Map o tType ->
                                         Set s -> s -> r1 -> Maybe (TestSubproofErr s sE eL1)
testSubproof varstack constdict already_proven consequent subproof =
      either return (const Nothing) eitherResult
      where eitherResult = do
             let sc = checkSanity varstack consequent constdict
             maybe (return ()) (throwError . TestSubproofErrResultNotSane consequent) sc
             (proven,_) <- left TestSubproofErrorSubproofFailedOnErr (runProof varstack subproof (already_proven,constdict))
             unless (consequent `Set.member` (proven `Set.union` already_proven))
                                 (throwError TestSubproofErrorResultNotProved)


data TheoremSchema s r o tType where
   TheoremSchema :: {
                       constDict :: Map o tType,
                       lemmas :: Set s,
                       theoremProof :: r,
                       theorem :: s
                    } -> TheoremSchema s r o tType



data TheoremError senttype sanityerrtype logcicerrtype o tType where
   TheoremErrLemmaSanityErr :: senttype -> sanityerrtype -> TheoremError senttype sanityerrtype logcicerrtype o tType
   TheoremErrorLemmaNotEstablished :: senttype -> TheoremError senttype sanityerrtype logcicerrtype o tType
   TheoremErrConstDictNotDefd :: o -> TheoremError senttype sanityerrtype logcicerrtype o tType
   TheoremErrConstTypeConflict :: o -> tType -> tType -> TheoremError senttype sanityerrtype logcicerrtype o tType
   TheoremErrSubproofErr :: TestSubproofErr senttype sanityerrtype logcicerrtype -> TheoremError senttype sanityerrtype logcicerrtype o tType
   deriving(Show)

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

establishTheorem :: (Proof eL1 r1 (Set s, Map o tType) [tType], PropLogicSent s sE t o tType)
                            => Map o tType -> Set s -> TheoremSchema s r1 o tType -> Maybe (TheoremError s sE eL1 o tType)
establishTheorem existingConsts already_proven (TheoremSchema constdict lemmas subproof theorem) =
        fmap constDictErr (constDictTest existingConsts constdict)
    <|> Prelude.foldr f1 Nothing lemmas
    <|> fmap TheoremErrSubproofErr (testSubproof mempty constdict lemmas theorem subproof)
      where 
            f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where
                   maybeLemmaNotSane = fmap (TheoremErrLemmaSanityErr a) (checkSanity mempty a constdict)
                   maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . TheoremErrorLemmaNotEstablished) a else Nothing
            constDictErr (k,Nothing) = TheoremErrConstDictNotDefd k
            constDictErr (k, Just (a,b)) = TheoremErrConstTypeConflict k a b
                           






data TheoremSchemaMT tType sE eL r s o m x where
   TheoremSchemaMT :: {
                       lemmasM :: Set s,
                       proofM :: ProofStateGenT tType sE eL r s o m (x,s),
                       constDictM :: Map o tType
                     } -> TheoremSchemaMT tType sE eL r s o m x

type TheoremSchemaM tType sE eL r s o = TheoremSchemaMT tType sE eL r s o (Either SomeException) ()



data EstTmMError s sE o tType eL where
    EstTmMErrMError :: BigException eL -> EstTmMError s sE o tType eL
    EstTmMErrMExcept :: SomeException -> EstTmMError s sE o tType eL
    -- EstTmMErrBasic :: TmErr s sE o tType -> EstTmMError s sE o tType eL
    EstTmMResultNotProved :: s ->  EstTmMError s sE o tType eL
    EstTmMErrResultSanity :: s -> sE -> EstTmMError s sE o tType eL
    EstTmMErrLemmaSanity :: s -> sE -> EstTmMError s sE o tType eL
    EstTmMErrLemmaNotEstablished :: s -> EstTmMError s sE o tType eL
    EstTmMErrConstDictNotDefd :: o -> EstTmMError s sE o tType eL
    EstTmMErrConstTypeConflict :: o -> tType -> tType ->  EstTmMError s sE o tType eL
    deriving (Show)
   


establishTheoremM :: (Monoid r1,  Proof eL1 r1 (Set s, Map o tType) [tType], 
                     PropLogicSent s sE t o tType)
                            => Map o tType -> Set s -> TheoremSchemaM tType sE eL1 r1 s o -> Either (EstTmMError s sE o tType eL1) s
establishTheoremM existingConsts already_proven ((TheoremSchemaMT lemmas proofprog constdict):: TheoremSchemaM tType sE eL1 r1 s o) = 
    do
        maybe (return ()) (throwError . constDictErr) (constDictTest existingConsts constdict)
        maybe (return ()) throwError (Prelude.foldr f1 Nothing lemmas)
        prfResult <- left EstTmMErrMExcept (runProofStateGen proofprog mempty lemmas constdict)
        (((),tm), (proven, newconsts), r1) <- left EstTmMErrMError prfResult
        let sc = checkSanity mempty tm constdict
        maybe (return ()) (throwError . EstTmMErrResultSanity tm) sc
        unless (tm `Set.member` (proven `Set.union` already_proven))
                            ((throwError . EstTmMResultNotProved) tm)
        return tm
   where
     constDictErr (k,Nothing) = EstTmMErrConstDictNotDefd k
     constDictErr (k, Just (a,b)) = EstTmMErrConstTypeConflict k a b
     f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
                   where
                     maybeLemmaNotSane = fmap (EstTmMErrLemmaSanity a) (checkSanity mempty a constdict)
                     maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . EstTmMErrLemmaNotEstablished) a else Nothing


data ProofByAsmSchema s r where
   ProofByAsmSchema :: {
                       asmPrfAsm :: s,
                       asmPrfProof :: r,
                       asmPrfConsequent :: s
                    } -> ProofByAsmSchema s r



data ProofByAsmError senttype sanityerrtype logcicerrtype where
   ProofByAsmErrAsmNotSane :: senttype -> sanityerrtype -> ProofByAsmError senttype sanityerrtype logcicerrtype
   ProofByAsmErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> ProofByAsmError senttype sanityerrtype logcicerrtype
    deriving(Show)


proofByAsm :: ( Proof eL1 r1 (Set s, Map o tType) [tType], PropLogicSent s sE t o tType) => [tType] -> Map o tType ->
                                         Set s -> ProofByAsmSchema s r1 -> Either (ProofByAsmError s sE eL1) s
proofByAsm varstack constdict already_proven (ProofByAsmSchema assumption subproof consequent) =
      do

         let sc = checkSanity varstack assumption constdict
         maybe (return ()) (throwError .  ProofByAsmErrAsmNotSane assumption) sc
         let contextSents = Set.insert assumption already_proven
         let mayTestResult = testSubproof varstack constdict contextSents consequent subproof
         maybe (return ()) (throwError . ProofByAsmErrSubproofFailedOnErr) mayTestResult
         return $ build_implication assumption consequent


data ProofByUGSchema s r tType where
   ProofByUGSchema :: {
                       ugPrfGeneralizable :: s,
                       ugPrfProof :: r,
                       ugTType :: tType
                    } -> ProofByUGSchema s r tType


class (PropLogicSent s sE t o tType) => PredLogicSent s t o tType sE | s->o, s->tType, s->t  where
    -- o is the type of constants
    parseExists :: s -> Maybe (t->s,tType)
    -- create generalization from sentence and varstack
    parseForall :: s -> Maybe (t->s,tType)
    -- create generalization from sentence and varstack
    applyUG ::s -> tType -> Int -> s
    -- constToTerm :: o -> t



data ProofByUGError senttype sanityerrtype logicerrtype where
   ProofByUGErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logicerrtype 
                                    -> ProofByUGError senttype sanityerrtype logicerrtype
 
     deriving(Show)

proofByUG :: ( Proof eL1 r1 (Set s, Map o tType) [tType], PredLogicSent s t o tType sE) 
                        => [tType] -> Map o tType ->
                                         Set s -> ProofByUGSchema s r1 tType -> Either (ProofByUGError s sE eL1) s
proofByUG varstack constdict already_proven (ProofByUGSchema generalizable subproof ttype) =
      do
         let newVarstack = ttype : varstack
         let mayTestResult = testSubproof newVarstack constdict already_proven generalizable subproof
         maybe (return ()) (throwError . ProofByUGErrSubproofFailedOnErr) mayTestResult
         return $ applyUG generalizable ttype (Prelude.length varstack)




runSubproofM :: ( Monoid r1, Proof eL1 r1 (Set s,Map o tType) [tType], Monad m,
                        PropLogicSent s sE t o tType)
                 =>   (s-> r1 -> r1) -> Set s -> Map o tType -> [tType] -> ProofStateGenT tType sE eL1 r1 s o m (s, x) ->
                           ProofStateGenT tType sE eL1 r1 s o m (s, x)
runSubproofM f sentences constDict varstack prog =  do
        monadResult <- lift $ runProofStateGenT prog varstack sentences constDict
        ((theorem,extraData),(newlyProven,_),r) <- either (throwError . BErrSubproof) return monadResult
        monadifyProof $ f theorem r
        return (theorem,extraData)




runTheoremM :: (Monoid r1, Proof eL1 r1 (Set s,Map o tType) [tType], Monad m,  
                      PropLogicSent s sE t o tType)
                 =>   (TheoremSchema s r1 o tType -> r1) -> Set s -> ProofStateGenT tType sE eL1 r1 s o m (s, x) -> Map o tType ->
                               ProofStateGenT tType sE eL1 r1 s o m (s, x)
runTheoremM f lemmas prog constDict =  do   
        runSubproofM (\ s p -> f (TheoremSchema constDict lemmas p s)) lemmas constDict mempty prog
 

runProofByAsmM :: (Monoid r1, Proof eL1 r1 (Set s,Map o tType) [tType], Monad m,
                       PropLogicSent s sE t o tType)
                 =>   (ProofByAsmSchema s r1 -> r1) -> s -> ProofStateGenT tType sE eL1 r1 s o m (s, x)
                            -> ProofStateGenT tType sE eL1 r1 s o m (s, x)
runProofByAsmM f asm prog =  do
        (proven,constDict) <- getProofState
        varstack <- ask
        (consequent, extraData) <-
                  runSubproofM (\ s p -> f (ProofByAsmSchema asm p s)) (Set.singleton asm <> proven) constDict varstack prog
        return (build_implication asm consequent,extraData)



runProofByUGM :: (Monoid r1, Proof eL1 r1 (Set s,Map o tType) [tType], Monad m,
                       PredLogicSent s t o tType sE)
                 =>  tType -> (ProofByUGSchema s r1 tType -> r1) -> ProofStateGenT tType sE eL1 r1 s o m (s, x)
                            -> ProofStateGenT tType sE eL1 r1 s o m (s, x)
runProofByUGM tt f prog =  do
        (proven,constDict) <- getProofState
        varstack <- ask
        let newVarstack = tt : varstack
        (generalizable, extraData) <-
                  runSubproofM (\ s p -> f (ProofByUGSchema s p tt)) proven constDict newVarstack prog
        return (applyUG generalizable tt (Prelude.length varstack),extraData)


data PropLogError s sE o tType where
    PLErrMPImplNotProven :: s-> PropLogError s sE o tType
    PLErrMPAnteNotProven :: s-> PropLogError s sE o tType
    PLErrSentenceNotImp :: s -> PropLogError s sE o tType
    PLErrPrfByAsmErr :: ProofByAsmError s sE (PropLogError s sE o tType) -> PropLogError s sE o tType
    PLErrTheorem :: TheoremError s sE (PropLogError s sE o tType) o tType -> PropLogError s sE o tType
    PLErrTheoremM :: EstTmMError s sE o tType (PropLogError s sE o tType) -> PropLogError s sE o tType
    PLExclMidSanityErr :: s -> sE -> PropLogError s sE o tType
    deriving(Show)


data PropLogR tType s sE o where
    MP :: s -> s -> PropLogR tType s sE o
    PLProofByAsm :: ProofByAsmSchema s [PropLogR tType s sE o]-> PropLogR tType s sE o
    PLTheorem :: TheoremSchema s [PropLogR tType s sE o] o tType -> PropLogR tType s sE o
    PLTheoremM :: TheoremSchemaM tType sE (PropLogError s sE o tType ) [PropLogR tType s sE o] s o -> PropLogR tType s sE o
    PLExclMid :: s -> PropLogR tType s sE o
    



pLrunProof :: (Proof (PropLogError s sE o tType) [PropLogR tType s sE o] (Set s, Map o tType) [tType],
               PropLogicSent s sE t o tType) =>
                            [tType] -> PropLogR tType s sE o -> (Set s, Map o tType) -> Either (PropLogError s sE o tType) s
pLrunProof varStack rule (proven,constDict) = 
      case rule of
        MP antecedant conseq -> do
             let implication = build_implication antecedant conseq
             unless (build_implication antecedant conseq  `Set.member` proven) ((throwError . PLErrMPImplNotProven) implication)
             unless (antecedant `Set.member` proven) ((throwError . PLErrMPAnteNotProven) antecedant)
             return conseq
        PLProofByAsm schema ->
             left PLErrPrfByAsmErr (proofByAsm varStack constDict proven schema)
        PLTheorem schema -> do
              maybe (return ()) (throwError . PLErrTheorem) (establishTheorem constDict proven schema)
              (return . theorem) schema
        PLTheoremM schema ->
            left PLErrTheoremM (establishTheoremM constDict proven schema)
        PLExclMid s -> do
             maybe (return ())   (throwError . PLExclMidSanityErr s) (checkSanity varStack s constDict)
             return $ buildDis s (buildNot s)





instance (PropLogicSent s sE t o tType) 
          => Proof (PropLogError s sE o tType) [PropLogR tType s sE o] (Set s, Map o tType) [tType] where
  runProof :: [tType] -> [PropLogR tType s sE o] -> (Set s, Map o tType) -> Either (PropLogError s sE o tType) (Set s, Map o tType)
  runProof varStack rs (proven, constDict) = foldM f (mempty,mempty) rs
      where
          f :: (Set s, Map o tType) -> PropLogR tType s sE o  -> Either (PropLogError s sE o tType) (Set s, Map o tType)
          f (pr, _) r =  fmap g (pLrunProof varStack r (pr<>proven,constDict))
            where
                g s = (pr <> Set.singleton s,mempty )




data PredProofError s sE o t tType where
    PredProofPrfByAsmErr :: ProofByAsmError s sE (PredProofError s sE o t tType) -> PredProofError s sE o t tType
    PredProofErrTheorem :: TheoremError s sE (PredProofError s sE o t tType) o tType -> PredProofError s sE o t tType
    PredProofErrTheoremM :: EstTmMError s sE o tType (PredProofError s sE o t tType) -> PredProofError s sE o t tType
    PredProofErrPL ::  PropLogError s sE o tType -> PredProofError s sE o t tType
    PredProofErrUG :: ProofByUGError s sE  (PredProofError s sE o t tType) -> PredProofError s sE o t tType
    PredProofErrEINotProven :: s -> PredProofError s sE o t tType
    PredProofErrUINotProven :: s -> PredProofError s sE o t tType
    PredProofErrEINotExists :: s -> PredProofError s sE o t tType
    PredProofErrAddConstErr :: o -> PredProofError s sE o t tType
    PredProofErrEIConstDefined :: o -> PredProofError s sE o t tType
    PredProofErrEGNotExists :: s -> PredProofError s sE o t tType
    PredProofErrUINotForall :: s -> PredProofError s sE o t tType
    PredProofErrEGNotGeneralization :: t -> s -> PredProofError s sE o t tType
    PredProofErrEGTermTypeMismatch :: t -> tType -> s -> tType -> PredProofError s sE o t tType
    PredProofErrUITermTypeMismatch :: t -> tType -> s -> tType -> PredProofError s sE o t tType
    PredProofTermSanity :: sE ->  PredProofError s sE o t tType
  deriving (Show)

data PredLogR s sE o t tType where
   -- t is a term
    PredProofProp :: PropLogR tType s sE o -> PredLogR s sE o t tType
    PredProofByAsm :: ProofByAsmSchema s [PredLogR s sE o t tType] -> PredLogR s sE o t tType
    PredProofByUG :: ProofByUGSchema s [PredLogR s sE o t tType] tType -> PredLogR s sE o t tType
    PredProofEI :: s -> o -> PredLogR s sE o t tType
       -- sentence of form E x . P, and a constant
    PredProofEG :: t -> s -> PredLogR s sE o t tType
        -- a free term,
        -- a sentence of the form E x . P
        -- Instantiate s using term t,
        -- If the resulting sentence is already proven, then the generalization is OK, and that is sentence s.BErrAsmSanity
    PredProofUI :: t -> s -> PredLogR s sE o t tType

    PredProofTheorem :: TheoremSchema s [PredLogR s sE o t tType] o tType -> PredLogR s sE o t tType
    PredProofTheoremM :: TheoremSchemaM tType sE (PredProofError s sE o t tType) [PredLogR s sE o t tType] s o -> 
                             PredLogR s sE o t tType








predPrfRunProof :: (PredLogicSent s t o tType sE,
               Proof (PredProofError s sE o t tType) [PredLogR s sE o t tType] (Set s, Map o tType) [tType]  ) =>
                            [tType] -> PredLogR s sE o t tType -> (Set s, Map o tType) -> Either (PredProofError s sE o t tType) (s,Maybe (o,tType))
predPrfRunProof varStack rule (proven,constDict) = 
      case rule of
          PredProofProp propR -> do
               sent <- left  PredProofErrPL (pLrunProof varStack propR (proven,constDict))
               return (sent, Nothing)
          PredProofByAsm schema -> do
               implication <- left PredProofPrfByAsmErr (proofByAsm varStack constDict proven schema)
               return (implication, Nothing)
          PredProofTheorem schema -> do
               maybe (return ()) (throwError . PredProofErrTheorem) (establishTheorem constDict proven schema)
               return (theorem schema, Nothing)
          PredProofTheoremM schema -> do
               theorem <- left PredProofErrTheoremM (establishTheoremM constDict proven schema)
               return (theorem,Nothing)
          PredProofByUG schema -> do
               generalized <- left PredProofErrUG (proofByUG varStack constDict proven schema)
               return (generalized,Nothing)
          PredProofEI existsSent const -> do 
               let existsParse = parseExists existsSent
               (f,tType) <- maybe ((throwError . PredProofErrEINotExists) existsSent) return existsParse
               let existsSentProven = existsSent `Set.member` proven
               unless existsSentProven ((throwError . PredProofErrEINotProven) existsSent)
               let constNotDefined = isNothing $ Data.Map.lookup const constDict
               unless constNotDefined ((throwError . PredProofErrEIConstDefined) const)
               return ((f . const2Term) const,Just (const,tType))
          PredProofEG term existsSent -> do
               let existsParse = parseExists existsSent
               (f,tType) <- maybe ((throwError . PredProofErrEINotExists) existsSent) return existsParse
               let eitherTermType = getTypeTerm term varStack constDict
               termType <- left PredProofTermSanity eitherTermType
               unless (tType == termType) ((throwError .  PredProofErrEGTermTypeMismatch term termType existsSent) tType)
               let sourceSent = f term
               unless (sourceSent `Set.member` proven) ((throwError . PredProofErrEGNotGeneralization term) existsSent)
               return (existsSent,Nothing)
          PredProofUI term forallSent -> do
               unless (forallSent `Set.member` proven)  ((throwError . PredProofErrUINotProven) forallSent)
               let forallParse = parseForall forallSent
               (f,tType) <- maybe ((throwError . PredProofErrUINotForall) forallSent) return forallParse
               let eitherTermType = getTypeTerm term varStack constDict
               termType <- left PredProofTermSanity eitherTermType
               unless (tType == termType) ((throwError .  PredProofErrUITermTypeMismatch term termType forallSent) tType)
               return (f term,Nothing)





instance (PredLogicSent s t o tType sE) 
          => Proof (PredProofError s sE o t tType) [PredLogR s sE o t tType] (Set s, Map o tType) [tType] where
  runProof :: [tType] -> [PredLogR s sE o t tType] -> (Set s, Map o tType) -> Either (PredProofError s sE o t tType) (Set s, Map o tType)
  runProof varStack rs (proven, constDict) = foldM f (mempty,mempty) rs
      where
          f (pr, dict) r =  fmap g (predPrfRunProof varStack r (pr<>proven,constDict<>dict))
            where
                g (s, Nothing) = (pr <> Set.singleton s,dict) 
                g (s,Just (newConst,tType)) = (pr <> Set.singleton s,insert newConst tType dict)





 
data PropDeBr where
      NotDeBr :: PropDeBr -> PropDeBr
      AndDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      OrDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      ImplDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      EquivDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      EqualsDeBr :: ObjDeBr -> ObjDeBr -> PropDeBr
      MemberDeBr :: ObjDeBr -> ObjDeBr -> PropDeBr
      ForAllDeBr :: PropDeBr -> PropDeBr
      ExistsDeBr :: PropDeBr -> PropDeBr
    deriving (Eq, Ord, Show)
  
  
data ObjDeBr where
      NumDeBr :: Int -> ObjDeBr
      ConstDeBr :: Text -> ObjDeBr
      HilbertDeBr :: PropDeBr -> ObjDeBr
      BoundVarDeBr :: Int -> ObjDeBr
      FreeVarDeBr :: Int ->ObjDeBr
   deriving (Eq, Ord, Show)


data DeBrSe where
    ObjDeBrSeConstNotDefd :: Text -> DeBrSe
    ObjDeBrBoundVarIdx :: Int -> DeBrSe
    ObjDeBrFreeVarIdx :: Int -> DeBrSe
   deriving Show


boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     NumDeBr num -> 0
     ConstDeBr name -> 0
     HilbertDeBr prop -> boundDepthPropDeBr prop + 1
     BoundVarDeBr idx -> 0
     FreeVarDeBr idx -> 0


checkSanityObjDeBr :: ObjDeBr -> Int -> Set Text -> Set Int -> Maybe DeBrSe

checkSanityObjDeBr obj varStackHeight constSet boundSet = case obj of
     NumDeBr num -> Nothing
     ConstDeBr name -> if name `Set.member` constSet then
                           Nothing
                       else
                           (return . ObjDeBrSeConstNotDefd) name
     HilbertDeBr prop -> checkSanityPropDeBr prop varStackHeight constSet 
                            (Set.insert (boundDepthPropDeBr prop) boundSet )
     BoundVarDeBr idx -> 
        if idx `Set.member` boundSet then
            Nothing
        else
            (return . ObjDeBrBoundVarIdx) idx
     FreeVarDeBr idx ->
        if idx >= 0 && idx < varStackHeight then
            Nothing
        else
            (return . ObjDeBrFreeVarIdx) idx



boundDepthPropDeBr :: PropDeBr -> Int
boundDepthPropDeBr p = case p of
    NotDeBr p -> boundDepthPropDeBr p
    AndDeBr p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    OrDeBr p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    ImplDeBr p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    EquivDeBr p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    MemberDeBr o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    EqualsDeBr o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    ForAllDeBr p -> boundDepthPropDeBr p + 1
    ExistsDeBr p -> boundDepthPropDeBr p + 1

checkSanityPropDeBr :: PropDeBr -> Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityPropDeBr prop freevarStackHeight consts boundVars = 
      case prop of
        NotDeBr p -> checkSanityPropDeBr p freevarStackHeight consts boundVars
        AndDeBr p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        OrDeBr p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        ImplDeBr p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        EquivDeBr p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        MemberDeBr o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars
        EqualsDeBr o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars
        ForAllDeBr prop -> checkSanityPropDeBr prop freevarStackHeight consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        ExistsDeBr prop -> checkSanityPropDeBr prop freevarStackHeight consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )



instance TypeableTerm ObjDeBr Text () DeBrSe where
 
     getTypeTerm :: ObjDeBr -> [()] -> Map Text () -> Either DeBrSe ()
     getTypeTerm term vs constDict = 
         maybe (return ()) throwError (checkSanityObjDeBr term (Prelude.length vs) (keysSet constDict) mempty)
     const2Term :: Text -> ObjDeBr
     const2Term = ConstDeBr

instance PropLogicSent PropDeBr DeBrSe ObjDeBr Text () where
  checkSanity :: [()] -> PropDeBr -> Map Text () -> Maybe DeBrSe
  checkSanity freeVarStack prop constDict = checkSanityPropDeBr
        prop (Prelude.length freeVarStack) (keysSet constDict) mempty
  buildAdj :: PropDeBr -> PropDeBr -> PropDeBr
  buildAdj = AndDeBr
  parseAdj :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseAdj p = case p of
                 AndDeBr p1 p2 -> Just (p1,p2) 
                 _ -> Nothing
  build_implication :: PropDeBr -> PropDeBr -> PropDeBr
  build_implication = ImplDeBr
  parse_implication :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parse_implication p = case p of
                 ImplDeBr p1 p2 -> Just (p1,p2) 
                 _ -> Nothing
  buildNot :: PropDeBr -> PropDeBr
  buildNot = NotDeBr
  parseNot :: PropDeBr -> Maybe PropDeBr
  parseNot p = case p of
    NotDeBr p1 -> Just p1
    _ -> Nothing
  buildDis :: PropDeBr -> PropDeBr -> PropDeBr
  buildDis = OrDeBr
  parseDis :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseDis p = case p of
                 OrDeBr p1 p2 -> Just(p1,p2)
                 _ -> Nothing

objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx =
    case obj of
        NumDeBr num -> False
        ConstDeBr const -> False
        HilbertDeBr p -> propDeBrBoundVarInside p idx
        BoundVarDeBr i -> idx == i
        FreeVarDeBr i -> False



propDeBrBoundVarInside :: PropDeBr -> Int -> Bool
propDeBrBoundVarInside prop idx = case prop of
    NotDeBr p -> propDeBrBoundVarInside p idx
    AndDeBr p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    OrDeBr p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    ImplDeBr p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    EquivDeBr p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    EqualsDeBr o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    MemberDeBr o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    ForAllDeBr p -> propDeBrBoundVarInside p idx
    ExistsDeBr p -> propDeBrBoundVarInside p idx


objDeBrSub :: Int -> Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSub boundVarIdx boundvarOffsetThreshold obj t = case obj of
    NumDeBr num -> NumDeBr num
    ConstDeBr const -> ConstDeBr const
    HilbertDeBr p -> HilbertDeBr (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)                            
    BoundVarDeBr idx 
                 | idx==boundVarIdx -> t
                 | idx >= boundvarOffsetThreshold -> BoundVarDeBr (idx + termDepth)
                 | idx < boundVarIdx -> BoundVarDeBr idx

    FreeVarDeBr idx -> FreeVarDeBr idx
  where
        termDepth = boundDepthObjDeBr t
        calcBVOThreshold p = if propDeBrBoundVarInside p boundVarIdx then
                                  boundDepthPropDeBr p
                             else boundvarOffsetThreshold

propDeBrSub :: Int -> Int -> PropDeBr -> ObjDeBr -> PropDeBr
propDeBrSub boundVarIdx boundvarOffsetThreshold prop t = case prop of
    NotDeBr p -> NotDeBr (propDeBrSub boundVarIdx boundvarOffsetThreshold p t)
    AndDeBr p1 p2 ->  AndDeBr (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t) 
    OrDeBr p1 p2 ->  OrDeBr (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t) 
    ImplDeBr p1 p2 ->  ImplDeBr (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t)
    EquivDeBr p1 p2 ->  EquivDeBr (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t)
    EqualsDeBr o1 o2 -> EqualsDeBr (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)   
    MemberDeBr o1 o2 -> MemberDeBr (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)  
    ForAllDeBr p -> ForAllDeBr (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)
    ExistsDeBr p -> ExistsDeBr (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)
  where
          calcBVOThreshold p = if propDeBrBoundVarInside p boundVarIdx then
                                      boundDepthPropDeBr p
                               else boundvarOffsetThreshold 


objDeBrApplyUG :: ObjDeBr -> Int -> Int -> ObjDeBr
objDeBrApplyUG obj freevarIdx boundvarIdx =
    case obj of
        NumDeBr num -> NumDeBr num
        ConstDeBr name -> ConstDeBr name
        HilbertDeBr p1 -> HilbertDeBr (propDeBrApplyUG p1 freevarIdx boundvarIdx)
        BoundVarDeBr idx -> BoundVarDeBr idx
        FreeVarDeBr idx -> if idx == freevarIdx then
                               BoundVarDeBr boundvarIdx
                           else
                               FreeVarDeBr idx 



propDeBrApplyUG :: PropDeBr -> Int -> Int -> PropDeBr
propDeBrApplyUG prop freevarIdx boundvarIdx =
    case prop of
        NotDeBr p -> NotDeBr (propDeBrApplyUG p freevarIdx boundvarIdx)
        AndDeBr p1 p2 -> AndDeBr (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx) 
        OrDeBr p1 p2 -> OrDeBr (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        ImplDeBr p1 p2 -> OrDeBr (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        EquivDeBr p1 p2 -> EquivDeBr (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        EqualsDeBr o1 o2 -> EqualsDeBr (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        MemberDeBr o1 o2 -> MemberDeBr (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        ForAllDeBr p -> ForAllDeBr (propDeBrApplyUG p freevarIdx boundvarIdx)
        ExistsDeBr p -> ExistsDeBr (propDeBrApplyUG p freevarIdx boundvarIdx)




instance PredLogicSent PropDeBr ObjDeBr Text () DeBrSe where
    parseExists :: PropDeBr -> Maybe (ObjDeBr -> PropDeBr,())
    parseExists prop = do
        case prop of
            ExistsDeBr p -> Just (propDeBrSub (boundVarIdx p) (calcBVOThreshold p) p,())
            _ -> Nothing
       where boundVarIdx = boundDepthPropDeBr
             calcBVOThreshold p = if propDeBrBoundVarInside p (boundVarIdx p) then
                                      boundDepthPropDeBr p
                                  else 
                                      boundDepthPropDeBr p + 1 
    parseForall :: PropDeBr -> Maybe (ObjDeBr -> PropDeBr, ())
    parseForall prop = do
        case prop of
            ForAllDeBr p -> Just (propDeBrSub (boundVarIdx p) (calcBVOThreshold p) p,())
            _ -> Nothing
      where boundVarIdx = boundDepthPropDeBr
            calcBVOThreshold p = if propDeBrBoundVarInside p (boundVarIdx p) then
                                      boundDepthPropDeBr p
                                  else 
                                      boundDepthPropDeBr p + 1             
    applyUG :: PropDeBr -> () -> Int -> PropDeBr
    applyUG prop () idx = ForAllDeBr (propDeBrApplyUG prop idx (boundDepthPropDeBr prop))
      

type PropErrDeBr = PropLogError PropDeBr DeBrSe Text ObjDeBr
type PropRuleDeBr = PropLogR () PropDeBr DeBrSe Text

type PredErrDeBr = PredProofError PropDeBr DeBrSe Text ObjDeBr () 
type PredRuleDeBr = PredLogR PropDeBr DeBrSe Text ObjDeBr ()


main :: IO ()
main = do
    let y0 =  (NumDeBr 0 `EqualsDeBr` NumDeBr 0) `ImplDeBr` (NumDeBr 99 `EqualsDeBr` NumDeBr 99)
    let y1 = NumDeBr 0 `EqualsDeBr` NumDeBr 0
    let y2= (NumDeBr 99 `EqualsDeBr` NumDeBr 99) `ImplDeBr` (NumDeBr 1001 `EqualsDeBr` NumDeBr 1001)
    let x0 = ExistsDeBr (ForAllDeBr ((NumDeBr 0 `EqualsDeBr` FreeVarDeBr 102) 
              `AndDeBr` (BoundVarDeBr 0 `MemberDeBr` BoundVarDeBr 1)) `AndDeBr` (BoundVarDeBr 1 `MemberDeBr` BoundVarDeBr 1))
    let x1 = ForAllDeBr (ForAllDeBr (ForAllDeBr ((BoundVarDeBr 3 `EqualsDeBr` BoundVarDeBr 2) `AndDeBr` ForAllDeBr (BoundVarDeBr 0 `EqualsDeBr` BoundVarDeBr 1))))
    (print . show) (checkSanity [(),()] x0 mempty)
    (print . show) x1
    let f = parseForall x1
    case f of
        Just (f,()) -> do
            let term1 = HilbertDeBr (NumDeBr 0 `MemberDeBr` NumDeBr 0)
            let fNew = f term1
            (print.show) fNew
        Nothing -> print "parse failed!"
    --let z = applyUG xn () 102
    -- (print . show) z
    let proof = [MP y1 (NumDeBr 99 `EqualsDeBr` NumDeBr 99),MP (NumDeBr 99 `EqualsDeBr` NumDeBr 99) (NumDeBr 1001 `EqualsDeBr` NumDeBr 1001)] 
    let zb = runProof [] proof (Set.fromList [y0,y1,y2], mempty) -- :: Either ErrDeBr (Set PropDeBr, Map Text ())
    (print . show) zb
--yrdy

