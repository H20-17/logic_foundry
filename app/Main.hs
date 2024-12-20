
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
import qualified GHC.Stack.Types
import Data.Data (Typeable)




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
                   case st of
                       Left e -> runProofStateT (errHandler e) c s
                       Right nonError -> (return . Right) nonError
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
                        case proofResult of
                            Right resultSet -> do
                                 put (u <> resultSet)
                                 tell p
                                 return resultSet
                            Left e -> (lift . throwError) e







modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c, Proof eL2 r2 s c,ErrorEmbed eL2 eM2, Monoid c, ErrorEmbed eL1 eM1)
             => (eM1 -> eM2) -> (r1 -> r2) -> ProofStateT eM1 eL1 c r1 s m a
                       -> ProofStateT eM2 eL2 c r2 s m a
modifyPS f g m1 = do
    c <- ask
    ps <- getProofState
    monadResult <- lift $ runProofStateT m1 c ps
    case monadResult of
        Left err -> throwError $ f err
        Right (datum,_,rules) -> do
            monadifyProof $ g rules
            return datum




---------------- END KERNEL --------------------------------------------------------------

-------- SUBPROOFABLE-----------------------------------------------------------------------








data BigException s sE o where
    BErrResultNotSane :: s -> sE -> BigException s sE o
    BErrResultNotProved :: s ->  BigException s sE o
    BErrLemmaSanity :: s -> sE -> BigException s sE o
    BErrLemmaNotEstablished :: s -> BigException s sE o
    BErrAsmSanity :: s -> sE -> BigException s sE o
    BErrConstDict :: o -> BigException s sE o
    BErrSubproof :: BigException s sE o -> BigException s sE o
    -- BErrSubproofFail ::
    deriving (Typeable,Show)


type ProofStateGenT sE eL c r s d o m x = ProofStateT (BigException s sE o) eL c r (Set s,d) m x

runProofStateGenT ::  (Monad m, ErrorEmbed eL (BigException s sE o), Proof eL r (Set s, d) c) 
                            => ProofStateGenT sE eL c r s d o m x -> c -> Set s -> d -> m (Either (BigException s sE o) (x,(Set s,d), r))
runProofStateGenT p varstack proven constDict = runProofStateT p varstack (proven,constDict)


type ProofStateGen sE eL c r s d o x = ProofState (BigException s sE o) eL c r (Set s, d) x
runProofStateGen :: (ErrorEmbed eL (BigException s sE o), Proof eL r (Set s, d) c) =>
                      ProofStateGen sE eL c r s d o x -> c -> Set s -> d -> Either SomeException (Either (BigException s sE o) (x,(Set s,d), r))
runProofStateGen p varstack proven constDict = runProofState p varstack (proven,constDict)


class (Eq tType) => TypeableTerm c t d o tType sE | t -> o, t->c, t->d, t->tType, t -> sE where
    getTypeTerm :: t -> c -> d -> Either sE tType
    const2Term :: o -> t
    -- get term type using a varstack and a const dictionary

class Monoid d => ConstDict d o tType | d->tType, d->o where
    constDictTest :: d -> d -> Maybe o
    constDictAddConst :: d -> o -> tType -> d
    constDictGetConst :: d -> o -> Maybe tType

class Monoid c => VarStack c tType  where
    varStackPush :: c ->tType -> c


class (TypeableTerm c t d o tType sE, ConstDict d o tType, VarStack c tType) 
              => PropLogicSent s c d sE t o tType | s -> sE , s -> c, s->t where
   checkSanity :: c -> s -> d -> Maybe sE
   buildAdj :: s -> s -> s
   parseAdj :: s -> Maybe(s,s)
   build_implication:: s->s->s
   parse_implication:: s -> Maybe (s,s)
   build_not :: s -> s
   buildDis :: s -> s -> s





data TestSubproofErr senttype sanityerrtype logcicerrtype where
   TestSubproofErrResultNotSane :: senttype -> sanityerrtype -> TestSubproofErr senttype sanityerrtype logcicerrtype
   TestSubproofErrorSubproofFailedOnErr :: logicerrtype
                                    -> TestSubproofErr senttype sanityerrtype logcicerrtype
   TestSubproofErrorResultNotProved :: TestSubproofErr senttype sanityerrtype logcicerrtype



testSubproof :: ( Ord s, Proof eL1 r1 (Set s, d) c, PropLogicSent s c d sE t o tType) => c -> d ->
                                         Set s -> s -> r1 -> Maybe (TestSubproofErr s sE eL1)
testSubproof varstack constdict already_proven consequent subproof =
    case eitherResult of
        Left err -> return err
        Right _ -> Nothing
      where eitherResult = do
             let sc = checkSanity varstack consequent constdict
             maybe (return ()) (throwError . TestSubproofErrResultNotSane consequent) sc
             let proofResult = runProof  varstack subproof (already_proven,constdict)
             case proofResult of
                Left e -> (throwError . TestSubproofErrorSubproofFailedOnErr) e
                Right (proven,_) -> unless (consequent `Set.member` (proven `Set.union` already_proven))
                                 (throwError TestSubproofErrorResultNotProved)
             return ()




data TheoremSchema s r d where
   TheoremSchema :: {
                       constDict :: d,
                       lemmas :: Set s,
                       theoremProof :: r,
                       theorem :: s
                    } -> TheoremSchema s r d





data TheoremError senttype sanityerrtype logcicerrtype o where
   TheoremErrLemmaSanityErr :: senttype -> sanityerrtype -> TheoremError senttype sanityerrtype logcicerrtype o
   TheoremErrorLemmaNotEstablished :: senttype -> TheoremError senttype sanityerrtype logcicerrtype o
   TheoremErrorConstDict :: o -> TheoremError senttype sanityerrtype logcicerrtype o
   TheoremErrSubproofErr :: TestSubproofErr senttype sanityerrtype logcicerrtype -> TheoremError senttype sanityerrtype logcicerrtype o



establishTheorem :: (Monoid c, Ord s, Proof eL1 r1 (Set s, d) c, PropLogicSent s c d sE t o tType)
                            => d -> Set s -> TheoremSchema s r1 d -> Maybe (TheoremError s sE eL1 o)
establishTheorem existingConsts already_proven (TheoremSchema constdict lemmas subproof theorem) =
     case eitherResult of
        Left err -> return err
        Right _ -> Nothing
      where eitherResult =  do
               let mayConst = constDictTest existingConsts constdict
               maybe (return ()) (throwError . TheoremErrorConstDict) mayConst
               let sc2 = Prelude.foldr f1 Nothing lemmas
               maybe (return ()) throwError  sc2
               let mayTestResult = testSubproof mempty constdict lemmas theorem subproof
               maybe (return ()) (throwError . TheoremErrSubproofErr) mayTestResult
               return theorem
            f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where
                   maybeLemmaNotSane = fmap (TheoremErrLemmaSanityErr a) (checkSanity mempty a constdict)
                   maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . TheoremErrorLemmaNotEstablished) a else Nothing


data TheoremSchemaMT sE eL c r s d o m x where
   TheoremSchemaMT :: {
                       lemmasM :: Set s,
                       proofM :: ProofStateGenT sE eL c r s d o m (x,s),
                       constDictM :: d
                     } -> TheoremSchemaMT sE eL c r s d o m x

type TheoremSchemaM sE eL c r s d o = TheoremSchemaMT sE eL c r s d o (Either SomeException) ()


data TheoremMError s sE o where
    TheoremMErrBErr :: BigException s sE o-> TheoremMError s sE o
    TheoremMErrExcept :: SomeException -> TheoremMError s sE o
    
   


establishTheoremM :: (Monoid r1, Monoid c,ConstDict d o tType, Ord s, Proof eL1 r1 (Set s, d) c, ErrorEmbed eL1 (BigException s sE o), 
                     PropLogicSent s c d sE t o tType)
                            => d -> Set s -> TheoremSchemaM sE eL1 c r1 s d o -> Either (TheoremMError s sE o) s
establishTheoremM existingConsts already_proven ((TheoremSchemaMT lemmas proofprog constdict):: TheoremSchemaM sE eL1 c r1 s d o)= 
    case runProofStateGen mainprog mempty already_proven existingConsts of
        Left excep -> (Left . TheoremMErrExcept) excep
        Right (Left err) -> (Left . TheoremMErrBErr) err
        Right (Right (theorem,_,_)) -> Right theorem

    where 
        mainprog :: ProofStateGen sE eL1 c r1 s d o s 
        mainprog = do
            let mayConstDictErr = constDictTest existingConsts constdict
            maybe (return ()) (throwError . BErrConstDict) mayConstDictErr
            let sc2 = Prelude.foldr f1 Nothing lemmas
            maybe (return ()) throwError  sc2

            prfResult <- lift $ runProofStateGen proofprog mempty lemmas constdict
            case prfResult of 
               Left e -> (throwError . BErrSubproof) e
               Right (((),tm), (proven, newconsts), r1) -> do
                     let sc = checkSanity mempty tm constdict
                     maybe (return ()) (throwError . BErrResultNotSane tm) sc
                     unless (tm `Set.member` (proven `Set.union` already_proven))
                        (throwError $ BErrResultNotProved tm)
                     return tm
           
          
               where
                f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
                   where
                     maybeLemmaNotSane = fmap (BErrLemmaSanity a) (checkSanity mempty a constdict)
                     maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . BErrLemmaNotEstablished) a else Nothing



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



proofByAsm :: ( Ord s, Proof eL1 r1 (Set s, d) c, ConstDict d o tType, PropLogicSent s c d sE t o tType) => c -> d ->
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






data ProofByUGError senttype sanityerrtype logcicerrtype where
   ProofByUGErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype 
                                    -> ProofByUGError senttype sanityerrtype logcicerrtype

proofByUG :: ( Ord s, Proof eL1 r1 (Set s, d) c, PredLogicSent s c t o tType d sE, ConstDict d o tType) 
                        => c -> d ->
                                         Set s -> ProofByUGSchema s r1 tType -> Either (ProofByUGError s sE eL1) s
proofByUG varstack constdict already_proven (ProofByUGSchema generalizable subproof ttype) =
      do
         let newVarstack = varStackPush varstack ttype
         let mayTestResult = testSubproof newVarstack constdict already_proven generalizable subproof
         maybe (return ()) (throwError . ProofByUGErrSubproofFailedOnErr) mayTestResult
         return $ applyUG generalizable newVarstack




runSubproofM :: (Ord s, Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c, Monad m, ErrorEmbed eL1 (BigException s sE o), 
                        PropLogicSent s c d sE t o tType)
                 =>   (s-> r1 -> r1) -> Set s -> d -> c-> ProofStateGenT sE eL1 c r1 s d o m (s, x) ->
                           ProofStateGenT sE eL1 c r1 s d o m (s, x)
runSubproofM f sentences constDict varstack prog =  do
        monadResult <- lift $ runProofStateGenT prog varstack sentences constDict

        case monadResult of
           Left e -> (throwError . BErrSubproof) e
           Right ((theorem,extraData),(newlyProven,_),r) -> do
               let sc = checkSanity varstack theorem constDict
               maybe (return ()) (throwError . BErrResultNotSane theorem) sc
               unless (theorem `Set.member` newlyProven)
                                 ((throwError . BErrResultNotProved) theorem)
               monadifyProof $ f theorem r
               return (theorem,extraData)




runTheoremM :: (Ord s,Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c, Monad m, ErrorEmbed eL1 (BigException s sE o), 
                      PropLogicSent s c d sE t o tType)
                 =>   (TheoremSchema s r1 d -> r1) -> Set s -> ProofStateGenT sE eL1 c r1 s d o m (s, x) -> d ->
                               ProofStateGenT sE eL1 c r1 s d o m (s, x)
runTheoremM f lemmas prog constDict =  do
        (proven,existingConsts) <- getProofState
        let mayConstDictErr = constDictTest existingConsts constDict
        maybe (return ()) (throwError . BErrConstDict) mayConstDictErr

        let sc2 = Prelude.foldr (f1 proven) Nothing lemmas
        maybe (return ()) throwError  sc2
        modifyPS BErrSubproof id $ runSubproofM (\ s p -> f (TheoremSchema constDict lemmas p s)) lemmas constDict mempty prog
    where
        f1 pr a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing 
                   Just x -> Just x
              where

                   maybeLemmaNotSane = fmap (BErrLemmaSanity a) (checkSanity mempty a constDict)
                   maybeLemmaMissing = if not (a `Set.member` pr)
                                            then (Just . BErrLemmaNotEstablished) a else Nothing



runProofByAsmM :: (Ord s,Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c, Monad m,
                       ErrorEmbed eL1 (BigException s sE o), PropLogicSent s c d sE t o tType)
                 =>   (ProofByAsmSchema s r1 -> r1) -> s -> ProofStateGenT sE eL1 c r1 s d o m (s, x)
                            -> ProofStateGenT sE eL1 c r1 s d o m (s, x)
runProofByAsmM f asm prog =  do
        (proven,constDict) <- getProofState
        varstack <- ask
        let sc = checkSanity varstack asm constDict
        maybe (return ()) (throwError .  BErrResultNotSane asm) sc
        (consequent, extraData) <- modifyPS BErrSubproof id $ 
                  runSubproofM (\ s p -> f (ProofByAsmSchema asm p s)) (Set.singleton asm <> proven) constDict varstack prog
        return (build_implication asm consequent,extraData)



runProofByUGM :: (Ord s,Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c, Monad m,
                      ErrorEmbed eL1 (BigException s sE o), PredLogicSent s c t o tType d sE)
                 =>  tType -> (ProofByUGSchema s r1 tType -> r1) -> ProofStateGenT sE eL1 c r1 s d o m (s, x)
                            -> ProofStateGenT sE eL1 c r1 s d o m (s, x)
runProofByUGM tt f prog =  do
        (proven,constDict) <- getProofState
        varstack <- ask
        let newVarstack = varStackPush varstack tt
        (generalizable, extraData) <- modifyPS BErrSubproof id $ 
                  runSubproofM (\ s p -> f (ProofByUGSchema s p tt)) proven constDict newVarstack prog
        return (applyUG generalizable newVarstack,extraData)






data PropLogR s d c sE o where
    MP :: s -> s -> PropLogR s d c sE o
    PLProofByAsm :: ProofByAsmSchema s [PropLogR s d c sE o]-> PropLogR s d c sE o
    PLTheorem :: TheoremSchema s [PropLogR s d c sE o] d -> PropLogR s d c sE o
    PLTheoremM :: TheoremSchemaM sE (PropLogError s sE o) c [PropLogR s d c sE o] s d o -> PropLogR s d c sE o
    PLExclMid :: s -> PropLogR s d c sE o
    

data PropLogError s sE o where
    PLErrMPImpNotProven :: s-> PropLogError s sE o
    PLErrMPanteNotProven :: s-> PropLogError s sE o
    PLErrSentenceNotImp :: s -> PropLogError s sE o
    PLErrPrfByAsmErr :: ProofByAsmError s sE (PropLogError s sE o) -> PropLogError s sE o
    PLErrTheorem :: TheoremError s sE (PropLogError s sE o) o -> PropLogError s sE o
    PLErrTheoremM :: TheoremMError s sE o -> PropLogError s sE o
    PLExclMidSanityErr :: s -> sE -> PropLogError s sE o

pLrunProof :: (Monoid c, Ord s,
               Proof (PropLogError s sE o) [PropLogR s d c sE o] (Set s, d) c,
               ErrorEmbed (PropLogError s sE o) (BigException s sE o), PropLogicSent s c d sE t o tType) =>
                            c -> PropLogR s d c sE o -> (Set s, d) -> Either (PropLogError s sE o) s
pLrunProof varStack rule (proven,constDict) = 
      case rule of
        MP implication antecedent -> do
             unless (implication `Set.member` proven) ((throwError . PLErrMPImpNotProven) implication)
             unless (antecedent `Set.member` proven) ((throwError . PLErrMPanteNotProven) antecedent)
             case parse_implication implication of
                Nothing -> throwError (PLErrSentenceNotImp implication)
                Just (a,b) -> return b
        PLProofByAsm schema -> do
             case proofByAsm varStack constDict proven schema of
                Left err -> (throwError . PLErrPrfByAsmErr) err
                Right implication -> return implication
        PLTheorem schema -> do
             case establishTheorem constDict proven schema of
                Just err -> (throwError . PLErrTheorem) err
                Nothing -> (return . theorem) schema
        PLTheoremM schema -> do
             case establishTheoremM constDict proven schema of
                Left err -> (throwError . PLErrTheoremM) err
                Right theorem -> return theorem
        PLExclMid s -> do
             case checkSanity varStack s constDict of
                Just err -> throwError $ PLExclMidSanityErr s err
                Nothing -> return $ buildDis s (build_not s)




-- instance (Monoid c, Monoid s, Ord s, Monoid d, PropLogicSent s c d sE t o tType,
--        ErrorEmbed (PropLogError s sE o) (BigException s sE o)) 
--          => Proof (PropLogError s sE o) [PropLogR s d c sE o] (Set s, d) c where
--  runProof :: c -> [PropLogR s d c sE o] -> (Set s, d) -> Either (PropLogError s sE o) (Set s, d)
--  runProof varStack rs (proven, constDict) = foldM f (proven,constDict) rs
--      where
--          f :: (Set s, d) -> PropLogR s d c sE o -> Either (PropLogError s sE o) (Set s, d)
--          f (pr, c) r =  fmap g (pLrunProof varStack r (pr,c))
--            where
--                g s = (pr <> Set.singleton s,c )



instance (Monoid c, Monoid s, Ord s, Monoid d, PropLogicSent s c d sE t o tType,
        ErrorEmbed (PropLogError s sE o) (BigException s sE o)) 
          => Proof (PropLogError s sE o) [PropLogR s d c sE o] (Set s, d) c where
  runProof :: c -> [PropLogR s d c sE o] -> (Set s, d) -> Either (PropLogError s sE o) (Set s, d)
  runProof varStack rs (proven, constDict) = foldM f (mempty,mempty) rs
      where
          f :: (Set s, d) -> PropLogR s d c sE o -> Either (PropLogError s sE o) (Set s, d)
          f (pr, _) r =  fmap g (pLrunProof varStack r (pr<>proven,constDict))
            where
                g s = (pr <> Set.singleton s,mempty )




class (PropLogicSent s c d sE t o tType) => PredLogicSent s c t o tType d sE | s->o, s-> c, s->tType, s->t  where
    -- o is the type of constants
    parseExists :: s -> Maybe (t->s,tType)
    -- create generalization from sentence and varstack
    parseForall :: s -> Maybe (t->s,tType)
    -- create generalization from sentence and varstack
    applyUG ::s -> c -> s
    -- constToTerm :: o -> t


data PredLogR s d c sE o t tType where
    -- o is a constant (a type of term)
    -- t is a term
    PredProofProp :: PropLogR s d c sE o -> PredLogR s d c sE o t tType
    PredProofByAsm :: ProofByAsmSchema s [PredLogR s d c sE o t tType] -> PredLogR s d c sE o t tType
    PredProofByUG :: ProofByUGSchema s [PredLogR s d c sE o t tType] tType -> PredLogR s d c sE o t tType
    PredProofEI :: s -> o -> PredLogR s d c sE o t tType
       -- sentence of form E x . P, and a constant
    PredProofEG :: t -> s -> PredLogR s d c sE o t tType
        -- a free term,
        -- a sentence of the form E x . P
        -- Instantiate s using term t,
        -- If the resulting sentence is already proven, then the generalization is OK, and that is sentence s.BErrAsmSanity
    PredProofUI :: t -> s -> PredLogR s d c sE o t tType

    PredProofTheorem :: TheoremSchema s [PredLogR s d c sE o t tType] d -> PredLogR s d c sE o t tType
    PredProofTheoremM :: TheoremSchemaM sE (PredProofError s sE o t tType) c [PredLogR s d c sE o t tType] s d o -> 
                             PredLogR s d c sE o t tType



data PredProofError s sE o t tType where
    PredProofPrfByAsmErr :: ProofByAsmError s sE (PredProofError s sE o t tType) -> PredProofError s sE o t tType
    PredProofErrTheorem :: TheoremError s sE (PredProofError s sE o t tType) o -> PredProofError s sE o t tType
    PredProofErrTheoremM :: TheoremMError s sE o -> PredProofError s sE o t tType
    PredProofErrPL ::  PropLogError s sE o -> PredProofError s sE o t tType
    PredProofErrUG :: ProofByUGError s sE  (PredProofError s sE eD t tType) -> PredProofError s sE o t tType
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




predPrfRunProof :: (Monoid c, Ord s, PredLogicSent s c t o tType d sE,
               Proof (PredProofError s sE o t tType) [PredLogR s d c sE o t tType] (Set s, d) c,
               ErrorEmbed (PredProofError s sE o t tType) (BigException s sE o),
               Monoid s,
               ErrorEmbed (PropLogError s sE o) (BigException s sE o)) =>
                            c -> PredLogR s d c sE o t tType -> (Set s, d) -> Either (PredProofError s sE o t tType) (s,Maybe (o,tType))
predPrfRunProof varStack rule (proven,constDict) = 
      case rule of
          PredProofProp propR -> do
               case pLrunProof varStack propR (proven,constDict) of
                  Left err -> (throwError .  PredProofErrPL) err
                  Right sent -> Right (sent,Nothing)
          PredProofByAsm schema -> do
               case proofByAsm varStack constDict proven schema of
                  Left err -> (throwError . PredProofPrfByAsmErr) err
                  Right implication -> return (implication,Nothing)
          PredProofTheorem schema -> do
               case establishTheorem constDict proven schema of
                  Just err -> (throwError . PredProofErrTheorem) err
                  Nothing -> return (theorem schema, Nothing)
          PredProofTheoremM schema -> do
               case establishTheoremM constDict proven schema of
                  Left err -> (throwError . PredProofErrTheoremM) err
                  Right theorem -> return (theorem,Nothing)
          PredProofByUG schema -> do
               case proofByUG varStack constDict proven schema of
                  Left err -> (throwError . PredProofErrUG) err
                  Right generalized -> return (generalized,Nothing)
          PredProofEI existsSent const -> do 
               let existsParse = parseExists existsSent
               (f,tType) <- maybe ((throwError . PredProofErrEINotExists) existsSent) return existsParse
               let existsSentProven = existsSent `Set.member` proven
               unless existsSentProven ((throwError . PredProofErrEINotProven) existsSent)
               let constNotDefined = isNothing $ constDictGetConst constDict const
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

-- instance (Monoid c, Monoid s, Ord s, Monoid d, PredLogicSent s c t o tType d sE,
--        ErrorEmbed (PredProofError s sE o t tType) (BigException s sE o),
--        ErrorEmbed (PropLogError s sE o) (BigException s sE o)) 
--          => Proof (PredProofError s sE o t tType) [PredLogR s d c sE o t tType] (Set s, d) c where
--  runProof :: c -> [PredLogR s d c sE o t tType] -> (Set s, d) -> Either (PredProofError s sE o t tType) (Set s, d)
--  runProof varStack rs (proven, constDict) = foldM f (proven,constDict) rs
--      where
--          f (pr, dict) r =  fmap g (predPrfRunProof varStack r (pr,dict))
--            where
--                g (s, Nothing) = (pr <> Set.singleton s,dict) 
--                g (s,Just (newConst,tType)) = (pr <> Set.singleton s,constDictAddConst dict newConst tType)



instance (Monoid c, Monoid s, Ord s, Monoid d, PredLogicSent s c t o tType d sE,
        ErrorEmbed (PredProofError s sE o t tType) (BigException s sE o),
        ErrorEmbed (PropLogError s sE o) (BigException s sE o)) 
          => Proof (PredProofError s sE o t tType) [PredLogR s d c sE o t tType] (Set s, d) c where
  runProof :: c -> [PredLogR s d c sE o t tType] -> (Set s, d) -> Either (PredProofError s sE o t tType) (Set s, d)
  runProof varStack rs (proven, constDict) = foldM f (mempty,mempty) rs
      where
          f (pr, dict) r =  fmap g (predPrfRunProof varStack r (pr<>proven,constDict<>dict))
            where
                g (s, Nothing) = (pr <> Set.singleton s,dict) 
                g (s,Just (newConst,tType)) = (pr <> Set.singleton s,constDictAddConst dict newConst tType)




-- ∀F∃A∀Y∀x[(x∈Y∧Y∈F)⇒x∈A]




-- instance (VarStack c, Ord s, Proof eL r (Set s, d) c sE, PredLogicSent s c d sE o, ConstDict d eD,
--          ErrorEmbed eL eM) =>
--          Proof (PredSPError s sE eL eD) (PredSubProof s r d sE eL c eM) (Set s,d) c sE where
--    runProof ::  c -> PredSubProof s r d sE eL c eM -> (Set s, d) -> Either (PredSPError s sE eL eD) (Set s, d)
--    runProof c (PredSPUG p generalizable) (proven, consts) = fmap g (proofByUG c consts proven (ProofByUGSchema generalizable p))
--          where g s = (Set.singleton s,mempty)
--    runProof c (PredSPPLSubProof p) state = do
--          let mayResult = runProof c p state
--          case mayResult of
--             Left e -> (throwError . PredSPErrPLSubProofErr) e
--             Right result -> return result




--data PLSchemaErr s sE eD where
--    PLSchemaImpNotProven :: s -> PLSchemaErr s sE eD
--    PLSSchemaNotImp :: s -> PLSchemaErr s sE eD
--    PLSSchemaSubproofErr :: SubproofError s sE (PLSchemaErr s sE eD) eD -> PLSchemaErr s sE eD


-- data PLSchema s eD sE c d eM where
--   PLSchemaMP :: s -> s -> PLSchema s eD sE c d eM
--   PLSchemaSubproof :: PLSubProof s [PLSchema s eD sE c d eM] d sE (PLSchemaErr s sE eD) c eM -> PLSchema s eD sE c d eM



-- instance (Monoid c,Ord s, Monoid d, StandardState (Set s, d) c sE, PropLogicSent s c d sE,
--         ConstDict d eD, Proof (PLSchemaErr s sE eD)  [PLSchema s eD sE c d eProgM] (Set s, d) c sE,
--         ErrorEmbed (PLSchemaErr s sE eD) eProgM)
--          => Proof (PLSchemaErr s sE eD) (PLSchema s eD sE c d eProgM) (Set s,d) c sE where
--    runProof :: (Monoid c, Ord s, Monoid d, StandardState (Set s, d) c sE,
--                 PropLogicSent s c d sE,
--                 ConstDict d eD) =>
--        c -> PLSchema s eD sE c d eProgM -> (Set s, d) -> Either (PLSchemaErr s sE eD) (Set s, d)
--    runProof vardict (PLSchemaMP imp ante) (proven,constdict) = do
--         case parse_implication imp of
--            Just (ante,cons) -> do
--                 unless (imp `Set.member` proven) $ throwError (PLSchemaImpNotProven imp)
--                 return (Set.singleton cons,mempty)
--            Nothing -> throwError $ PLSSchemaNotImp imp
--    runProof vardict (PLSchemaSubproof subproof) (proven,constdict) =
--         case runProof vardict subproof (proven,constdict) of
--            Left e -> throwError $ PLSSchemaSubproofErr e
--            Right result -> return result


-- instance (Monoid c,Ord s, Monoid d, StandardState (Set s, d) c sE,
--          PropLogicSent s c d sE,ConstDict d eD) 
--          => Proof (PLSchemaErr s sE eD) [PLSchema s eD sE c d eM] (Set s, d) c sE where
--
--    runProof :: (Monoid c, Ord s, Monoid d, StandardState (Set s, d) c sE,
--                 PropLogicSent s c d sE, ConstDict d eD) =>
--            c
--              -> [PLSchema s eD sE c d]
--              -> (Set s, d)
--            -> Either (PLSchemaErr s sE eD) (Set s, d)
--    runProof vardict pls (proven, constdict) = 
--        Prelude.foldl 





-- 
-- 
-- 
-- data RPL p where
    -- PLMp :: p -> RPL p
    -- PLAdj :: p -> RPL p
    -- RPLSubproof :: [BLRule p [RPL p]] -> RPL p
--  
-- data PLErr p v where
    -- PLErrSentNotImp :: PLErr p v
    -- PLErrSentNotAdj :: PLErr p v
    -- PLErrMPImpNotProven:: PLErr p v
    -- PLErrAdjNotProven:: PLErr p v
    -- PLErrMPAntecedantNotProven :: PLErr p v
    -- PLErrBL :: BLError p v (PLErr p v) -> PLErr p v
--     
-- 
-- instance BLErrEmbeddable p v (PLErr p v) where
    -- embedBLError :: BLError p v (PLErr p v) -> PLErr p v
    -- embedBLError = PLErrBL
-- 
-- 
-- 
-- instance (Ord p, BasicLang p v,BLErrEmbeddable p v (PLErr p v) , PropLogic p) => Proof (PLErr p v) [RPL p] (Set p) (Set v) where
    -- runProof :: Set v -> [RPL p] -> Set p -> Either (PLErr p v) (Set p)
    -- runProof _ blrs ss = foldM blRunProofBasic' ss blrs
        -- where blRunProofBasic' ss' blr = fmap specialOp (blRunProofBasic ss' blr)
                 -- where specialOp s = s `Set.union` ss'
                       -- blRunProofBasic :: Set p -> RPL p -> Either (PLErr p v) (Set p)
                       -- blRunProofBasic ss (PLMp prop) = do
                          -- case parse_implication prop of
                            -- Just (a,b) -> do
                              -- unless (prop `Set.member` ss') $ throwError PLErrMPImpNotProven
                              -- unless (a `Set.member` ss') $ throwError PLErrMPAntecedantNotProven
                              -- (return . Set.singleton) b
                            -- _ -> throwError PLErrSentNotImp
                       -- blRunProofBasic ss (PLMp prop) = do
                          -- case parseAdj prop of
                              -- Just (a,b) -> do
                                 -- unless (prop `Set.member` ss') $ throwError PLErrAdjNotProven
                                 -- (return . Set.fromList) [a,b]
                              -- _ -> throwError PLErrSentNotAdj    
                       -- blRunProofBasic ss (RPLSubproof blrs) =
                            -- runProof (mempty::Set v)  blrs ss
-- 
--  
--  
-- 
-- 
-- data PropDeBr where
      -- NotDeBr :: PropDeBr -> PropDeBr
      -- AndDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      -- OrDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      -- ImplDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      -- EquivDeBr :: PropDeBr -> PropDeBr -> PropDeBr
      -- EqualsDeBr :: ObjDeBr -> ObjDeBr -> PropDeBr
      -- ForAllDeBr :: PropDeBr -> PropDeBr
      -- ExistsDeBr :: PropDeBr -> PropDeBr
    -- deriving (Eq, Ord, Show)
--  
--  
-- data ObjDeBr where
      -- NumDeBr :: Integer -> ObjDeBr
      -- AddDeBr :: ObjDeBr -> ObjDeBr -> ObjDeBr
      -- MulDeBr :: ObjDeBr -> ObjDeBr -> ObjDeBr
      -- VarDeBr :: Text -> ObjDeBr
      -- HilbertDeBr :: PropDeBr -> ObjDeBr
      -- IndexDeBr :: Int -> ObjDeBr
    -- deriving (Eq, Ord, Show)
-- 
--  
-- data PropF where
      -- NotF :: PropF -> PropF
      -- AndF :: PropF -> PropF -> PropF
      -- OrF :: PropF -> PropF -> PropF
      -- ImplF :: PropF -> PropF -> PropF
      -- EquivF :: PropF -> PropF -> PropF
      -- EqualsF :: ObjF -> ObjF -> PropF
      -- ForAllF :: (ObjF -> PropF) -> PropF
      -- ExistsF :: (ObjF -> PropF) -> PropF
-- 
-- 
-- 
-- data ObjF where
      -- NumF :: Integer -> ObjF
      -- AddF :: ObjF -> ObjF -> ObjF
      -- MulF :: ObjF -> ObjF -> ObjF
      -- VarF :: Text -> ObjF
      -- HilbertF :: (ObjF -> PropF) -> ObjF
      -- IndexF :: Int -> ObjF
--  
--  
-- propDeBr2F':: [ObjF] -> PropDeBr -> PropF
-- propDeBr2F' xs (NotDeBr p) = NotF (propDeBr2F' xs p)
-- propDeBr2F' xs (p1 `AndDeBr` p2) = propDeBr2F' xs p1 `AndF` propDeBr2F' xs p2
-- propDeBr2F' xs (p1 `OrDeBr` p2) = propDeBr2F' xs p1 `OrF` propDeBr2F' xs p2
-- propDeBr2F' xs (p1 `ImplDeBr` p2) = propDeBr2F' xs p1 `ImplF` propDeBr2F' xs p2
-- propDeBr2F' xs (p1 `EquivDeBr` p2) = propDeBr2F' xs p1 `EquivF` propDeBr2F' xs p2
-- propDeBr2F' xs (o1 `EqualsDeBr` o2) = objDeBr2F' xs o1 `EqualsF` objDeBr2F' xs o2
-- propDeBr2F' xs (ForAllDeBr p) = ForAllF (\x -> propDeBr2F' (x:xs) p)
-- propDeBr2F' xs (ExistsDeBr p) = ExistsF (\x -> propDeBr2F' (x:xs) p)
-- 
-- 
-- 
-- 
-- objDeBr2F' :: [ObjF] -> ObjDeBr -> ObjF
-- objDeBr2F' xs (NumDeBr n) = NumF n
-- objDeBr2F' xs (o1 `AddDeBr` o2) = objDeBr2F' xs o1 `AddF` objDeBr2F' xs o2
-- objDeBr2F' xs (o1 `MulDeBr` o2) = objDeBr2F' xs o1 `MulF` objDeBr2F' xs o2
-- objDeBr2F' xs (VarDeBr t) = VarF t
-- objDeBr2F' xs (HilbertDeBr p) = HilbertF (\x -> propDeBr2F' (x:xs) p)
-- objDeBr2F' xs (IndexDeBr i) = xs !! i
-- 
-- 
-- objDeBr2F :: ObjDeBr -> ObjF
-- objDeBr2F = objDeBr2F' []
--  
-- propDeBr2F:: PropDeBr -> PropF
-- propDeBr2F = propDeBr2F' []
-- 
-- 
-- 
-- 
-- propF2DeBr':: Int -> PropF -> PropDeBr
-- propF2DeBr' i (NotF p) = NotDeBr (propF2DeBr' i p)
-- propF2DeBr' i (p1 `AndF` p2) = propF2DeBr' i p1 `AndDeBr` propF2DeBr' i p2
-- propF2DeBr' i (p1 `OrF` p2) = propF2DeBr' i p1 `OrDeBr` propF2DeBr' i p2
-- propF2DeBr' i (p1 `ImplF` p2) = propF2DeBr' i p1 `ImplDeBr` propF2DeBr' i p2
-- propF2DeBr' i (p1 `EquivF` p2) = propF2DeBr' i p1 `EquivDeBr` propF2DeBr' i p2
-- propF2DeBr' i (o1 `EqualsF` o2) = objF2DeBr' i o1 `EqualsDeBr` objF2DeBr' i o2
-- propF2DeBr' i (ForAllF f) = ForAllDeBr (propF2DeBr' (i+1) (f (IndexF i)))
-- propF2DeBr' i (ExistsF f) = ExistsDeBr (propF2DeBr' (i+1) (f (IndexF i)))
-- 
-- 
-- 
-- objF2DeBr' :: Int -> ObjF -> ObjDeBr
-- objF2DeBr' i (NumF n) = NumDeBr n
-- objF2DeBr' i (o1 `AddF` o2) = objF2DeBr' i o1 `AddDeBr` objF2DeBr' i o2
-- objF2DeBr' i (o1 `MulF` o2) = objF2DeBr' i o1 `MulDeBr` objF2DeBr' i o2
-- objF2DeBr' i (VarF t) = VarDeBr t
-- objF2DeBr' i (HilbertF f) = HilbertDeBr (propF2DeBr' (i+1) (f (IndexF i)))
-- objF2DeBr' i (IndexF ind) = IndexDeBr (i - ind -1)
-- 
-- 
-- objF2DeBr :: ObjF -> ObjDeBr
-- objF2DeBr = objF2DeBr' 0
-- 
-- 
-- propF2DeBr :: PropF -> PropDeBr
-- propF2DeBr = propF2DeBr' 0
-- 
-- 
-- propFFreeVars:: PropF -> Set Text
-- propFFreeVars (NotF p) = propFFreeVars p
-- propFFreeVars (p1 `AndF` p2) = propFFreeVars p1 `Set.union` propFFreeVars p2
-- propFFreeVars (p1 `OrF` p2) = propFFreeVars p1 `Set.union` propFFreeVars p2
-- propFFreeVars (p1 `OrF` p2) = propFFreeVars p1 `Set.union` propFFreeVars p2
-- propFFreeVars (p1 `EquivF` p2) = propFFreeVars p1 `Set.union` propFFreeVars p2
-- propFFreeVars (o1 `EqualsF` o2) = objFFreeVars o1 `Set.union` objFFreeVars o2
-- propFFreeVars (ForAllF f) = propFFreeVars (f (IndexF 0))
-- propFFreeVars (ExistsF f) = propFFreeVars (f (IndexF 0))
-- 
-- 
-- 
-- objFFreeVars :: ObjF -> Set Text
-- objFFreeVars (NumF n) = mempty
-- objFFreeVars (o1 `AddF` o2) = objFFreeVars o1 `Set.union` objFFreeVars o2
-- objFFreeVars (o1 `MulF` o2) = objFFreeVars o1 `Set.union` objFFreeVars o2
-- objFFreeVars (VarF t) = Set.singleton t
-- objFFreeVars (HilbertF f) = propFFreeVars (f (IndexF 0))
-- objFFreeVars (IndexF ind) = mempty
-- 
-- 
-- propFBindVar :: PropF -> Text -> (ObjF -> PropF)
-- propFBindVar p v = \x ->  propDeBr2F' [x] (propFVarDeBr' p v 0)
    -- where propFVarDeBr'::PropF -> Text -> Int -> PropDeBr
          -- propFVarDeBr' (NotF p) v i = NotDeBr (propFVarDeBr' p v i)
          -- propFVarDeBr' (p1 `AndF` p2) v i = propFVarDeBr' p1 v i `AndDeBr` propFVarDeBr' p2 v i
          -- propFVarDeBr' (p1 `OrF` p2) v i = propFVarDeBr' p1 v i `OrDeBr` propFVarDeBr' p2 v i
          -- propFVarDeBr' (p1 `ImplF` p2) v i = propFVarDeBr' p1 v i `ImplDeBr` propFVarDeBr' p2 v i
          -- propFVarDeBr' (p1 `EquivF` p2) v i = propFVarDeBr' p1 v i `EquivDeBr` propFVarDeBr' p2 v i
          -- propFVarDeBr' (o1 `EqualsF` o2) v i = objFVarDeBr' o1 v i `EqualsDeBr` objFVarDeBr' o2 v i
          -- propFVarDeBr' (ForAllF f) v i = ForAllDeBr (propFVarDeBr' (f (IndexF i)) v (i+1))
          -- propFVarDeBr' (ExistsF f) v i = ExistsDeBr (propFVarDeBr' (f (IndexF i)) v (i+1))
          -- objFVarDeBr' :: ObjF -> Text -> Int -> ObjDeBr
          -- objFVarDeBr' (NumF n) v i = NumDeBr n
          -- objFVarDeBr' (o1 `AddF` o2) v i = objFVarDeBr' o1 v i `AddDeBr` objFVarDeBr' o2 v i
          -- objFVarDeBr' (o1 `MulF` o2) v i = objFVarDeBr' o1 v i `MulDeBr` objFVarDeBr' o2 v i
          -- objFVarDeBr' (VarF t) v i = if v==t
                                        -- then
                                          -- IndexDeBr i
                                            -- else
                                              -- VarDeBr t
          -- objFVarDeBr' (HilbertF f) v i = HilbertDeBr (propFVarDeBr' (f (IndexF i)) v (i+1))
          -- objFVarDeBr' (IndexF ind) v i = IndexDeBr (i - ind -1)
-- 
-- 
-- propFBindForAll :: PropF -> Text -> PropF
-- propFBindForAll p v = ForAllF (propFBindVar p v) 
-- 
-- propFBindExists :: PropF -> Text -> PropF
-- propFBindExists p v = ExistsF (propFBindVar p v) 
-- 
-- 
-- instance Eq PropF where
     -- (==) :: PropF -> PropF -> Bool
     -- a == b = propF2DeBr a == propF2DeBr a
-- 
-- 
-- instance Ord PropF where
    -- (<=) :: PropF -> PropF -> Bool
    -- a <= b =  propF2DeBr a <= propF2DeBr a
-- 
-- 
-- useQuantifier :: PropF -> ObjF -> PropF
-- useQuantifier (ExistsF f) o = f o
-- useQuantifier (ForAllF f) o = f o
-- useQuantifier _ _ = error "help"
-- 
-- instance BasicLang PropF Text where
    -- extractContext :: Set PropF -> Set Text
    -- extractContext = Set.foldr f mempty
       -- where
          -- f prop accumSet = accumSet `Set.union` propFFreeVars prop
    -- build_implication :: PropF -> PropF -> PropF
    -- build_implication = ImplF
    -- parse_implication :: PropF -> Maybe (PropF, PropF)
    -- parse_implication s = case s of 
                             -- a `ImplF` b -> Just (a,b)
                             -- _ -> Nothing
-- 
-- 
-- 
-- main :: IO ()
-- main = do
    -- let testSent = ExistsDeBr (ForAllDeBr (VarDeBr "x" `EqualsDeBr` IndexDeBr 1) `OrDeBr` (IndexDeBr 0 `EqualsDeBr` VarDeBr "x") ) `OrDeBr` (VarDeBr "x" `EqualsDeBr` VarDeBr "x")
    -- let testSentF =  propDeBr2F testSent
--  
    -- -- let testSentnew = (propF2DeBr . propDeBr2F) testSent
--     
    -- -- let testObj = HilbertDeBr (ForAllDeBr (IndexDeBr 0 `EqualsDeBr` IndexDeBr 1) `OrDeBr` (IndexDeBr 0 `EqualsDeBr` IndexDeBr 0))
    -- -- let testObjF = objDeBr2F testObj
--  
    -- (print . show) testSent
    -- let fardF= propFBindForAll testSentF "x"
    -- let fard = propF2DeBr fardF
    -- (print . show) fard
-- -- 
-- -- 
-- -- 
-- -- 
-- -- 
-- -- 

-- runProofStateTChecked:: (Monad m, ErrorEmbed eL eM, Proof eL r s c sE) => ProofStateT eM eL c r s m x -> c -> s -> m (Either sE (Either eM (x,s, r)))
-- runProofStateTChecked ps c s = do
--        case checkSanity c s  of
--            Just err -> return  $ throwError err
--            Nothing -> do
--                 mayResult <- runProofStateT ps c s
--                 case mayResult of
--                    Left e -> return $ Right (Left e)
--                    Right (x,s,r) -> return $ Right $ Right (x,s,r)



-- runProofChecked :: (Proof eL r s c sE) => c -> r -> s -> Either sE (Either eL s)
-- runProofChecked vardict prf state = do
--         case checkSanity vardict state  of
--            Just err -> throwError err
--            Nothing -> return $ runProof vardict prf state



-- runProofStateChecked :: (ErrorEmbed eL eM, Proof eL r s c sE)
--       => ProofState eM eL c r s x -> c -> s-> Either SomeException (Either sE (Either eM (x,s, r)))
-- runProofStateChecked = runProofStateTChecked










main :: IO ()
main = do
    print "HI BITCH"
    print "WFT??"
    print "FUCK"


