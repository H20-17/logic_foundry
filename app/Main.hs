
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
import Foreign.C (eEXIST)


class ErrorEmbed e1 e2  where
     errEmbed:: e1-> e2



class StandardState s c sE  | s -> sE , s -> c where
   checkSanity :: c -> s -> Maybe sE


class (Monoid s, StandardState s c sE) => Proof e r s c sE |  r->e  where
      runProof :: c -> r -> s -> Either e s



runProofE :: (Proof e1 r s c sE) => c -> r ->s -> (e1 -> e2) -> Either e2 s
runProofE c r s f = left f (runProof c r s)





runProofChecked :: (Proof eL r s c sE) => c -> r -> s -> Either sE (Either eL s)
runProofChecked vardict prf state = do
         case checkSanity vardict state  of
            Just err -> throwError err
            Nothing -> return $ runProof vardict prf state







data ProofStateT eM eL c r s m x where
  ProofStateTInternal :: {runProofStateTTop :: RWST c r s (ExceptT eM m) x}
                   -> ProofStateT eM eL c r s m x


runProofStateT ::  (Monad m, ErrorEmbed eL eM, Proof eL r s c sE) => ProofStateT eM eL c r s m x -> c -> s -> m (Either eM (x,s, r))
runProofStateT ps c s = runExceptT $ runRWST (runProofStateTTop ps) c s





runProofStateTChecked:: (Monad m, ErrorEmbed eL eM, Proof eL r s c sE) => ProofStateT eM eL c r s m x -> c -> s -> m (Either sE (Either eM (x,s, r)))
runProofStateTChecked ps c s = do
        case checkSanity c s  of
            Just err -> return  $ throwError err
            Nothing -> do
                 mayResult <- runProofStateT ps c s
                 case mayResult of
                    Left e -> return $ Right (Left e)
                    Right (x,s,r) -> return $ Right $ Right (x,s,r)


type ProofState eM eL c r s x = ProofStateT eM eL c r s Identity x


runProofState :: (ErrorEmbed eL eM, Proof eL r s c sE) => ProofState eM eL c r s x -> c -> s-> Either eM (x, s, r)
runProofState ps c s = runIdentity (runProofStateT ps c s)




runProofStateChecked :: (ErrorEmbed eL eM, Proof eL r s c sE)
       => ProofState eM eL c r s x -> c -> s-> Either sE (Either eM (x,s, r))
runProofStateChecked ps c s = runIdentity (runProofStateTChecked ps c s)




instance (Monad m) => Functor (ProofStateT eM eL c r s m) where
     fmap :: Monad m =>
              (a -> b) -> ProofStateT eM eL c r s m a -> ProofStateT eM eL c r s m b
     fmap f (ProofStateTInternal g) = ProofStateTInternal $ fmap f g







instance (Monoid r, Monad m, Proof eL r s c sE, ErrorEmbed eL eM) => Applicative (ProofStateT eM eL c r s m) where
   pure :: (Monad m, Proof eL r s c sE) => a -> ProofStateT eM eL c r s m a
   (<*>) :: (Monad m, Proof eL r s c sE, ErrorEmbed eL eM) => ProofStateT eM eL c r s m (a -> b)
                                        -> ProofStateT eM eL c r s m a -> ProofStateT eM eL c r s m b
   ProofStateTInternal a <*> ProofStateTInternal b = ProofStateTInternal $ a <*> b
   pure x = ProofStateTInternal $ pure x





instance (Monoid r,Proof eL r s c sE, Monad m, ErrorEmbed eL eM) => Monad (ProofStateT eM eL c r s m) where
   (>>=) :: (Proof eL r s c sE, Monad m, ErrorEmbed eL eM) => ProofStateT eM eL c r s m a
                                         -> (a -> ProofStateT eM eL c r s m b)
                                     -> ProofStateT eM eL c r s m b
   ProofStateTInternal y >>= g = ProofStateTInternal (y >>= runProofStateTTop . g)




instance (Monoid r) =>  MonadTrans (ProofStateT eM eL c r s) where
      lift :: (Monoid r, Monad m) => m a -> ProofStateT eM eL c r s m a
      lift = ProofStateTInternal . lift . lift





getProofState :: (Monoid r, Proof eL r s c sE, Monad m) => ProofStateT eM eL c r s m s
getProofState = ProofStateTInternal get



instance (Monoid r,Proof eL r s c sE, Monad m, ErrorEmbed eL eM) => MonadError eM  (ProofStateT eM eL c r s m) where
      throwError :: (Proof eL r s c sE, Monad m, ErrorEmbed eL eM) => eM -> ProofStateT eM eL c r s m a
      throwError = ProofStateTInternal . lift . throwError

      catchError :: (Proof eL r s c sE, Monad m, ErrorEmbed eL eM) =>
                     ProofStateT eM eL c r s m a -> (eM -> ProofStateT eM eL c r s m a) -> ProofStateT eM eL c r s m a
      catchError z errHandler = ProofStateTInternal  (RWST \ c s -> ExceptT $ do
                   st <- runProofStateT z c s
                   case st of
                       Left e -> runProofStateT (errHandler e) c s
                       Right nonError -> (return . Right) nonError
           )





instance (Monoid c,Monad m, Monoid r, Monad (ProofStateT eM eL c r s m)) => MonadReader c (ProofStateT eM eL c r s m) where
   ask ::  ProofStateT eM eL c r s m c
   ask = ProofStateTInternal ask
   local :: (c->c) -> ProofStateT eM eL c r s m a -> ProofStateT eM eL c r s m a
   local f (ProofStateTInternal g) = ProofStateTInternal $ local f g




monadifyProof :: (Monoid r, Proof eL r s c sE, Monad m, ErrorEmbed eL eM) => r -> ProofStateT eM eL c r s m s
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
    






modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c sE, Proof eL2 r2 s c sE,ErrorEmbed eL2 eM2, Monoid c, ErrorEmbed eL1 eM1)
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

data SubproofError senttype sanityerrtype logcicerrtype constdicterrtype where
   SubproofErrLemmaSanityErr :: senttype -> sanityerrtype -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrAsmNotSane :: senttype -> sanityerrtype -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrConsNotSane :: senttype -> sanityerrtype -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrTheoremNotSane :: senttype -> sanityerrtype -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrorSubproofFailedOnErr :: logicerrtype
                                    -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrorSubproofResultConsNotProved :: SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrorLemmaNotEstablished :: senttype -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype
   SubproofErrorConstDict :: constdicterrtype -> SubproofError senttype sanityerrtype logcicerrtype consdicterrtype





testSubproof :: ( Ord s, Proof eL1 r1 (Set s, d) c sE, PropLogicSent s c d sE, ConstDict d eD) => c -> d ->
                                         Set s -> s -> r1 -> Maybe (SubproofError s sE eL1 eD)
testSubproof varstack constdict already_proven consequent subproof = 
    case eitherResult of
        Left err -> return err
        Right _ -> Nothing
      where eitherResult = do
             let sc = checkSanity varstack (Set.singleton consequent,constdict)
             maybe (return ()) (throwError . SubproofErrConsNotSane consequent) sc
             let proofResult = runProof  varstack subproof (already_proven,constdict)
             case proofResult of
                Left e -> (throwError . SubproofErrorSubproofFailedOnErr) e
                Right (proven,_) -> unless (consequent `Set.member` (proven `Set.union` already_proven))
                                 (throwError SubproofErrorSubproofResultConsNotProved)
             return ()
        

data TheoremSchema s r d where
   TheoremSchema :: {
                       constDict :: d,
                       lemmas :: Set s,
                       theoremProof :: r,
                       theorem :: s
                    } -> TheoremSchema s r d











data TheoremSchemaMtrans eM eL c s r m x d where
   TheoremSchemaMtrans :: {
                       lemmasMtrans :: Set s,
                       proofMtrans :: ProofStateT eM eL c r (Set s,d) m (s, x),
                       constDictMtrans :: d
                     } -> TheoremSchemaMtrans eM eL c s r m x d




data TheoremSchemaM eM eL c s r d where
   TheoremSchemaM :: {
                       lemmasM :: Set s,
                       proofM :: ProofState eM eL c r (Set s,d) s,
                       constDictM :: d
                     } -> TheoremSchemaM eM eL c s r d


class (StandardState s c sE) => PropLogicSent s c d sE | s->d where
    buildAdj :: s -> s -> s
    parseAdj :: s -> Maybe(s,s)
    build_implication:: s->s->s
    parse_implication:: s -> Maybe (s,s)



data PLSubProof s r d sE eL c eM where
      PLSPProofByAsm :: s -> s-> r -> PLSubProof s r d sE eL c eM
      PLSubProofTheorem :: TheoremSchema s r d -> PLSubProof s r d sE eL c eM
      PLSubProofTheoremM :: TheoremSchemaM eM eL c s r d -> PLSubProof s r d sE eL c eM



class Monoid d => ConstDict d e | d->e where
    constDictTest :: d -> d -> Maybe e







proofByAsm :: ( Ord s, Proof eL1 r1 (Set s, d) c sE, PropLogicSent s c d sE, ConstDict d eD) => c -> d ->
                                         Set s -> s -> s -> r1 -> Either (SubproofError s sE eL1 eD) s
proofByAsm varstack constdict already_proven assumption consequent subproof =
      do
         let sc = checkSanity varstack (Set.singleton assumption, constdict)
         maybe (return ()) (throwError .  SubproofErrAsmNotSane assumption) sc
         let sc = checkSanity varstack (Set.singleton consequent,constdict)
         maybe (return ()) (throwError . SubproofErrConsNotSane assumption) sc
         let contextSents = (Set.insert assumption already_proven,constdict)
         let proofResult = runProof  varstack subproof contextSents
         case proofResult of
            Left e -> (throwError .  SubproofErrorSubproofFailedOnErr) e
            Right (proven,_) -> unless (consequent `Set.member` (proven `Set.union` already_proven))
                                 (throwError SubproofErrorSubproofResultConsNotProved)
         return $ build_implication assumption consequent







establishTheorem :: (Monoid c,ConstDict d eD, Ord s,PropLogicSent s c d sE, Proof eL1 r1 (Set s, d) c sE)
                            => d -> Set s -> TheoremSchema s r1 d -> Either (SubproofError s sE eL1 eD) s
establishTheorem existingConsts already_proven (TheoremSchema constdict lemmas subproof theorem) =
     do
         let mayConstDictErr = constDictTest existingConsts constdict
         maybe (return ()) (throwError . SubproofErrorConstDict) mayConstDictErr
         let sc2 = Prelude.foldr f1 Nothing lemmas
         maybe (return ()) throwError  sc2
         let sc = checkSanity mempty (Set.singleton theorem,constdict)
         maybe (return ()) (throwError . SubproofErrTheoremNotSane theorem) sc
         let proofResult = runProof mempty subproof (lemmas,constdict)
         case proofResult of
            Left e -> (throwError . SubproofErrorSubproofFailedOnErr) e
            Right (proven,_) -> unless (theorem `Set.member` (proven `Set.union` already_proven))
                     (throwError  SubproofErrorSubproofResultConsNotProved)
         return theorem
      where
         f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where
                   maybeLemmaNotSane = fmap (SubproofErrLemmaSanityErr a) (checkSanity mempty (Set.singleton a,constdict))
                   maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . SubproofErrorLemmaNotEstablished) a else Nothing




establishTheoremM :: (Monoid c,ConstDict d eD, Ord s,PropLogicSent s c d sE, Proof eL1 r1 (Set s, d) c sE, ErrorEmbed eL1 eM)
                            => d -> Set s -> TheoremSchemaM eM eL1 c s r1 d -> Either (SubproofError s sE eL1 eD) s
establishTheoremM existingConsts already_proven (TheoremSchemaM lemmas proofprog constdict) =
     do
         let mayConstDictErr = constDictTest existingConsts constdict
         maybe (return ()) (throwError . SubproofErrorConstDict) mayConstDictErr
         let sc2 = Prelude.foldr f1 Nothing lemmas
         maybe (return ()) throwError  sc2

         let prfResult = runProofState proofprog mempty (lemmas,constdict)
         case prfResult of -- ::(Either eM (r1,(Set s,d),s)) of
            Left e -> (throwError . SubproofErrorSubproofFailedOnErr) e
            Right (tm, (proven, newconsts), r1) -> do
                     let sc = checkSanity mempty (Set.singleton tm,constdict)
                     maybe (return ()) (throwError . SubproofErrTheoremNotSane tm) sc
                     unless (tm `Set.member` (proven `Set.union` already_proven))
                        (throwError  SubproofErrorSubproofResultConsNotProved)
                     return tm
      where
         f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where
                   maybeLemmaNotSane = fmap (SubproofErrLemmaSanityErr a) (checkSanity mempty (Set.singleton a,constdict))
                   maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . SubproofErrorLemmaNotEstablished) a else Nothing



instance (Monoid c,Ord s, Proof eL r (Set s, d) c sE, PropLogicSent s c d sE, ConstDict d eD, ErrorEmbed eL eM) =>
           Proof (SubproofError s sE eL eD) (PLSubProof s r d sE eL c eM) (Set s,d) c sE where
    runProof :: (Ord s, Monoid d) => c -> PLSubProof s r d sE eL c eM -> (Set s, d) -> Either (SubproofError s sE eL eD) (Set s, d)
    runProof c (PLSPProofByAsm asm cons p) (proven, consts) = fmap g (proofByAsm c consts proven asm cons p)
         where g s = (Set.singleton s,mempty)
    runProof c (PLSubProofTheorem ts) (proven, consts) = fmap g (establishTheorem consts proven ts)
         where g s = (Set.singleton s,mempty)
    runProof c (PLSubProofTheoremM tsM) (proven,consts) = fmap g (establishTheoremM consts proven tsM)
         where g s = (Set.singleton s, mempty)



class PLSchemaLift s r d sE eL c eM | s -> sE, s->d, r->eL, s-> c, r->eM where
    plSchemaLift :: PLSubProof s r d sE eL c eM -> r


data PLSubProofErrorM eM where
     PLSPErrMProofByASM :: eM -> PLSubProofErrorM eM
     PLSPErrMTheorem :: eM -> PLSubProofErrorM eM


class PLSubProofErrMEmbed eM where
      plSubProofErrMEmbed :: PLSubProofErrorM eM -> eM



proofByAsmM :: (Monoid r, Monad m, Ord s, ErrorEmbed eL eM1, Monoid c, PLSchemaLift s r d sE eL c eProgM, Proof eL r (Set s, d) c sE,
                    PLSubProofErrMEmbed eM1)
        => s -> ProofStateT eM1 eL c r (Set s,d) m (s, x) -> ProofStateT eM1 eL c r (Set s,d) m (s,x)
proofByAsmM asm prog = do
       (ss,d) <- getProofState
       c <- ask
       let antecedents = Set.insert asm ss

       monadResult <- lift $  runProofStateT prog c (antecedents,d)
       case monadResult of
           Left e -> (throwError .  plSubProofErrMEmbed . PLSPErrMProofByASM) e
           Right ((cons,extraData),_,r) -> do
               monadifyProof $ plSchemaLift (PLSPProofByAsm asm cons r)
               return (cons,extraData)








class SchemaLift r1 r2 where
    schemaLift :: r1 -> r2





blTheoremM :: (Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c sE, Monad m,
                        PLSchemaLift s r2 d sE eL2 c eProgM, Proof eL2 r2 (Set s, d) c sE, ErrorEmbed eL2 eM2, Monoid r2, ErrorEmbed eL1 eM1,
                        PLSubProofErrMEmbed eM2, ErrorEmbed eM1 eM2, SchemaLift r1 r2)
                 =>   TheoremSchemaMtrans eM1 eL1 c s r1 m x d -> ProofStateT eM2 eL2 c r2 (Set s,d) m (s,x)
blTheoremM  (TheoremSchemaMtrans lemmas prog constDict) = do
        monadResult <- lift $ runProofStateT (modifyPS errEmbed schemaLift prog)  mempty (lemmas,constDict)
        case monadResult of
           Left e -> (throwError . plSubProofErrMEmbed . PLSPErrMTheorem) e
           Right ((theorem,extraData),_,r) -> do
               monadifyProof $ plSchemaLift (PLSubProofTheorem (TheoremSchema constDict lemmas r theorem))
               return (theorem,extraData)








class (PropLogicSent s c d sE) => PredLogicSent s c d sE o | s->o where
    parseExists :: s -> Maybe (o->s)
    applyUG ::s -> c -> s



data PredSubProof s r d sE eL c eM where
      PredSPPLSubProof :: PLSubProof s r d sE eL c eM -> PredSubProof s r d sE eL c eM
      PredSPUG :: r -> s -> PredSubProof s r d sE eL c eM



class Monoid c => VarStack c  where
    varStackPushType0 :: c -> c


data PredSPError s sE eL d where
   PredSPErrPLSubProofErr :: SubproofError s sE eL d -> PredSPError s sE eL d
   PredSPError :: PredSPError s sE eL d
   PredSPErrGenNotSane :: s -> sE -> PredSPError s sE eL d
   PredSPErrSubproofFailedOnErr :: eL -> PredSPError s sE eL d
   PredSPResultGenNotProved :: PredSPError s sE eL d

class PredSubProofErrMEmbed eM where
      predSubProofErrMEmbed :: PredSubProofErrorM eM -> eM

proofByUG :: ( Ord s, Proof eL1 r1 (Set s, d) c sE, PredLogicSent s c d sE o, ConstDict d eD, VarStack c) => c -> d ->
                                         Set s -> s -> r1 -> Either (PredSPError s sE eL1 eD) s
proofByUG varstack constdict already_proven generalizable subproof =
      do
         let newVarstack = varStackPushType0 varstack
         let sc = checkSanity newVarstack (Set.singleton generalizable,constdict)
         maybe (return ()) (throwError .  PredSPErrGenNotSane generalizable) sc

         let proofResult = runProof  newVarstack subproof (already_proven,constdict)
         case proofResult of
            Left e -> (throwError .  PredSPErrSubproofFailedOnErr) e
            Right (proven,_) -> unless (generalizable `Set.member` proven) (throwError PredSPResultGenNotProved)
         return $ applyUG generalizable newVarstack


instance (VarStack c, Ord s, Proof eL r (Set s, d) c sE, PredLogicSent s c d sE o, ConstDict d eD,
          ErrorEmbed eL eM) =>
          Proof (PredSPError s sE eL eD) (PredSubProof s r d sE eL c eM) (Set s,d) c sE where
    runProof ::  c -> PredSubProof s r d sE eL c eM -> (Set s, d) -> Either (PredSPError s sE eL eD) (Set s, d)
    runProof c (PredSPUG p generalizable) (proven, consts) = fmap g (proofByUG c consts proven generalizable p)
          where g s = (Set.singleton s,mempty)
    runProof c (PredSPPLSubProof p) state = do
          let mayResult = runProof c p state
          case mayResult of
             Left e -> (throwError . PredSPErrPLSubProofErr) e
             Right result -> return result


class PredSchemaLift s r d sE eL c eM | s -> sE, s->d, r->eL, s-> c, r->eM where
    predSchemaLift :: PredSubProof s r d sE eL c eM -> r


data PredSubProofErrorM eM where
     PredSPErrMProofByUG :: eM -> PredSubProofErrorM eM



proofByUGM :: (Monoid r, Monad m, Ord s, ErrorEmbed eL eM1, Monoid c, PredSchemaLift s r d sE eL c eProgM,
                Proof eL r (Set s, d) c sE, VarStack c,
                PredLogicSent s c d sE o, PredSubProofErrMEmbed eM1)
        => ProofStateT eM1 eL c r (Set s,d) m (s, x) -> ProofStateT eM1 eL c r (Set s,d) m (s,x)
proofByUGM prog = do
       (antecedents,d) <- getProofState
       c <- ask
       let newVarStack = varStackPushType0 c
       monadResult <- lift $  runProofStateT prog  newVarStack (antecedents,d)
       case monadResult of
           Left e -> (throwError . predSubProofErrMEmbed . PredSPErrMProofByUG) e
           Right ((generalizable,extraData),_,r) -> do
               monadifyProof $ predSchemaLift (PredSPUG r generalizable)
               return (applyUG generalizable newVarStack,extraData)




data PLSchemaErr s sE eD where
    PLSchemaImpNotProven :: s -> PLSchemaErr s sE eD
    PLSSchemaNotImp :: s -> PLSchemaErr s sE eD
    PLSSchemaSubproofErr :: SubproofError s sE (PLSchemaErr s sE eD) eD -> PLSchemaErr s sE eD


data PLSchema s eD sE c d eM where
   PLSchemaMP :: s -> s -> PLSchema s eD sE c d eM
   PLSchemaSubproof :: PLSubProof s [PLSchema s eD sE c d eM] d sE (PLSchemaErr s sE eD) c eM -> PLSchema s eD sE c d eM



instance (Monoid c,Ord s, Monoid d, StandardState (Set s, d) c sE, PropLogicSent s c d sE,
         ConstDict d eD, Proof (PLSchemaErr s sE eD)  [PLSchema s eD sE c d eProgM] (Set s, d) c sE,
         ErrorEmbed (PLSchemaErr s sE eD) eProgM)
          => Proof (PLSchemaErr s sE eD) (PLSchema s eD sE c d eProgM) (Set s,d) c sE where
    runProof :: (Monoid c, Ord s, Monoid d, StandardState (Set s, d) c sE,
                 PropLogicSent s c d sE,
                 ConstDict d eD) =>
        c -> PLSchema s eD sE c d eProgM -> (Set s, d) -> Either (PLSchemaErr s sE eD) (Set s, d)
    runProof vardict (PLSchemaMP imp ante) (proven,constdict) = do
         case parse_implication imp of
            Just (ante,cons) -> do
                 unless (imp `Set.member` proven) $ throwError (PLSchemaImpNotProven imp)
                 return (Set.singleton cons,mempty)
            Nothing -> throwError $ PLSSchemaNotImp imp
    runProof vardict (PLSchemaSubproof subproof) (proven,constdict) =
         case runProof vardict subproof (proven,constdict) of
            Left e -> throwError $ PLSSchemaSubproofErr e
            Right result -> return result


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

main :: IO ()
main = do
    print "HI BITCH"
    print "WFT??"
    print "FUCK"