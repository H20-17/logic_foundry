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
import Control.Monad.Catch
import Control.Arrow
import Data.Typeable          (TypeRep, Typeable, typeRep)
import Control.Monad.Except

import Control.Monad.Error.Class
import Foreign.C (eEXIST)
import GHC.Stack.Types (HasCallStack)



class ErrorEmbed e1 e2  where
     errEmbed:: e1-> e2



class StandardState s c sE  | s -> sE , s -> c where
   checkSanity :: c -> s -> Maybe sE


class (Monoid s, StandardState s c sE) => Proof e r s c sE |  r->e, s->sE where
      runProof :: c -> r -> s -> Either e s



runProofE :: (Proof e1 r s c sE) => c -> r ->s -> (e1 -> e2) -> Either e2 s
runProofE c r s f = left f (runProof c r s)





runProofChecked :: (Proof eL r s c sE) => c -> r -> s -> Either sE (Either eL s)
runProofChecked vardict prf state = do
         case checkSanity vardict state  of
            Just err -> throwError err
            Nothing -> return $ runProof vardict prf state







data ProofStateT eL c r s m x where
  ProofStateTInternal :: {runProofStateTTop :: RWST c r s m x}
                   -> ProofStateT eL c r s m x


runProofStateT ::  (Monad m, MonadThrow m, Proof eL r s c sE) => ProofStateT eL c r s m x -> c -> s -> m (x,s, r)
runProofStateT ps = runRWST (runProofStateTTop ps)


data SanityException sE where
  SanityException :: sE -> SanityException sE
  deriving (Typeable, Show)


instance (Show sE,Typeable sE) => Exception (SanityException sE)



runProofStateTChecked:: (Monad m, Proof eL r s c sE,MonadThrow m,Typeable sE,Show sE) => ProofStateT eL c r s m x -> c -> s -> m (x,s, r)
runProofStateTChecked ps c s = do
        case checkSanity c s  of
            Just err -> throwM $ SanityException err
            Nothing -> runProofStateT ps c s



type ProofState eL c r s x = ProofStateT eL c r s (Either SomeException) x


runProofState :: (Proof eL r s c sE) => ProofState eL c r s x -> c -> s-> Either SomeException (x, s, r)
runProofState = runProofStateT




runProofStateChecked :: (Proof eL r s c sE,Typeable sE,Show sE)
       => ProofState eL c r s x -> c -> s-> Either SomeException (x,s, r)
runProofStateChecked = runProofStateTChecked




instance (Monad m) => Functor (ProofStateT eL c r s m) where
     fmap :: Monad m =>
              (a -> b) -> ProofStateT eL c r s m a -> ProofStateT eL c r s m b
     fmap f (ProofStateTInternal g) = ProofStateTInternal $ fmap f g







instance (Monoid r, Monad m, Proof eL r s c sE) => Applicative (ProofStateT eL c r s m) where
   pure :: (Monad m, Proof eL r s c sE) => a -> ProofStateT eL c r s m a
   (<*>) :: (Monad m, Proof eL r s c sE) => ProofStateT eL c r s m (a -> b)
                                        -> ProofStateT eL c r s m a -> ProofStateT eL c r s m b
   ProofStateTInternal a <*> ProofStateTInternal b = ProofStateTInternal $ a <*> b
   pure x = ProofStateTInternal $ pure x





instance (Monoid r,Proof eL r s c sE, Monad m) => Monad (ProofStateT eL c r s m) where
   (>>=) :: (Proof eL r s c sE, Monad m) => ProofStateT eL c r s m a
                                         -> (a -> ProofStateT eL c r s m b)
                                     -> ProofStateT eL c r s m b
   ProofStateTInternal y >>= g = ProofStateTInternal (y >>= runProofStateTTop . g)




instance (Monoid r) =>  MonadTrans (ProofStateT eL c r s) where
      lift :: (Monoid r, Monad m) => m a -> ProofStateT eL c r s m a
      lift = ProofStateTInternal . lift





getProofState :: (Monoid r, Proof eL r s c sE, Monad m) => ProofStateT eL c r s m s
getProofState = ProofStateTInternal get



instance (Monoid r,Proof eL r s c sE, Monad m, MonadThrow m) => MonadThrow (ProofStateT eL c r s m) where
  throwM :: (Monoid r, Proof eL r s c sE, Monad m, MonadThrow m, GHC.Stack.Types.HasCallStack, Exception e) =>
                 e -> ProofStateT eL c r s m a
  throwM = ProofStateTInternal . lift . throwM

      --throwError :: (Proof eL r s c sE, Monad m) => eM -> ProofStateT eL c r s m a
      --throwError = ProofStateTInternal . lift . throwError

      --catchError :: (Proof eL r s c sE, Monad m) =>
      --               ProofStateT eM eL c r s m a -> (eM -> ProofStateT eL c r s m a) -> ProofStateT eL c r s m a
      --catchError z errHandler = ProofStateTInternal  (RWST \ c s -> ExceptT $ do
      --             st <- runProofStateT z c s
      --             case st of
      --                 Left e -> runProofStateT (errHandler e) c s
      --                 Right nonError -> (return . Right) nonError
      --     )


instance (Proof eL r s c sE, Monoid r, MonadThrow m, MonadCatch m)  => MonadCatch (ProofStateT eL c r s m) where
       catch :: (Proof eL r s c sE, HasCallStack, MonadThrow m, MonadCatch m,Exception e) =>
            ProofStateT eL c r s m a -> (e -> ProofStateT eL c r s m a) -> ProofStateT eL c r s m a
       catch z errhandler = ProofStateTInternal (RWST \c s -> do
            catch (runProofStateT z c s) (\err -> runProofStateT (errhandler err) c s))



instance (Monoid c,Monad m, Monoid r, Monad (ProofStateT eL c r s m)) => MonadReader c (ProofStateT eL c r s m) where
   ask ::  ProofStateT eL c r s m c
   ask = ProofStateTInternal ask
   local :: (c->c) -> ProofStateT eL c r s m a -> ProofStateT eL c r s m a
   local f (ProofStateTInternal g) = ProofStateTInternal $ local f g



data MonadifyProofException eL where
  MonadifyProofException :: eL -> MonadifyProofException eL
  deriving (Typeable, Show)


instance (Show eL,Typeable eL) => Exception (MonadifyProofException eL)





monadifyProof :: (Monoid r, Proof eL r s c sE, Monad m, Typeable eL, Show eL, MonadThrow m)
                       => r -> ProofStateT eL c r s m s
monadifyProof p = ProofStateTInternal $ do
                        c <- ask
                        u <- get
                        let proofResult = runProof c p u
                        case proofResult of
                            Right resultSet -> do
                                 put (u <> resultSet)
                                 tell p
                                 return resultSet
                            Left e -> (lift . throwM . MonadifyProofException) e







modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c sE, Proof eL2 r2 s c sE, Monoid c, MonadThrow m, Typeable eL2, Show eL2)
             =>  (r1 -> r2) -> ProofStateT eL1 c r1 s m a
                       -> ProofStateT eL2 c r2 s m a
modifyPS g m1 = do
    c <- ask
    ps <- getProofState
    (datum,_,rules) <- lift $ runProofStateT m1 c ps
    monadifyProof $ g rules
    return datum





---------------- END KERNEL --------------------------------------------------------------

-------- SUBPROOFABLE-----------------------------------------------------------------------


data TestSubproofErr senttype sanityerrtype logcicerrtype where
   TestSubproofErrResultNotSane :: senttype -> sanityerrtype -> TestSubproofErr senttype sanityerrtype logcicerrtype
   TestSubproofErrorSubproofFailedOnErr :: logicerrtype
                                    -> TestSubproofErr senttype sanityerrtype logcicerrtype
   TestSubproofErrorResultNotProved :: TestSubproofErr senttype sanityerrtype logcicerrtype



testSubproof :: ( Ord s, Proof eL1 r1 (Set s, d) c sE, ConstDict d eD) => c -> d ->
                                         Set s -> s -> r1 -> Maybe (TestSubproofErr s sE eL1)
testSubproof varstack constdict already_proven consequent subproof =
    case eitherResult of
        Left err -> return err
        Right _ -> Nothing
      where eitherResult = do
             let sc = checkSanity varstack (Set.singleton consequent,constdict)
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

class Monoid d => ConstDict d e | d->e where
    constDictTest :: d -> d -> Maybe e



data TheoremError senttype sanityerrtype logcicerrtype constdicterrtype where
   TheoremErrLemmaSanityErr :: senttype -> sanityerrtype -> TheoremError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremErrorLemmaNotEstablished :: senttype -> TheoremError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremErrorConstDict :: constdicterrtype -> TheoremError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremErrSubproofErr :: TestSubproofErr senttype sanityerrtype logcicerrtype -> TheoremError senttype sanityerrtype logcicerrtype consdicterrtype



establishTheorem :: (Monoid c,ConstDict d eD, Ord s,PropLogicSent s, Proof eL1 r1 (Set s, d) c sE)
                            => d -> Set s -> TheoremSchema s r1 d -> Maybe (TheoremError s sE eL1 eD)
establishTheorem existingConsts already_proven (TheoremSchema constdict lemmas subproof theorem) =
     case eitherResult of
        Left err -> return err
        Right _ -> Nothing
      where eitherResult =  do
               let mayConstDictErr = constDictTest existingConsts constdict
               maybe (return ()) (throwError . TheoremErrorConstDict) mayConstDictErr
               let sc2 = Prelude.foldr f1 Nothing lemmas
               maybe (return ()) throwError  sc2
               let mayTestResult = testSubproof mempty constdict lemmas theorem subproof
               maybe (return ()) (throwError . TheoremErrSubproofErr) mayTestResult
               return theorem
            f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where
                   maybeLemmaNotSane = fmap (TheoremErrLemmaSanityErr a) (checkSanity mempty (Set.singleton a,constdict))
                   maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . TheoremErrorLemmaNotEstablished) a else Nothing


data TheoremSchemaM eL c s r d where
   TheoremSchemaM :: {
                       lemmasM :: Set s,
                       proofM :: ProofState eL c r (Set s,d) s,
                       constDictM :: d
                     } -> TheoremSchemaM  eL c s r d


data TheoremMError senttype sanityerrtype logcicerrtype constdicterrtype where
   TheoremMErrLemmaSanityErr :: senttype -> sanityerrtype -> TheoremMError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremMErrResultNotSane :: senttype -> sanityerrtype -> TheoremMError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremMErrSubproofFailedOnErr :: logicerrtype
                                    -> TheoremMError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremMErrResultNotProved :: TheoremMError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremMErrLemmaNotEstablished :: senttype -> TheoremMError senttype sanityerrtype logcicerrtype consdicterrtype
   TheoremMErrConstDict :: constdicterrtype -> TheoremMError senttype sanityerrtype logcicerrtype consdicterrtype


establishTheoremM :: (Monoid c,ConstDict d eD, Ord s, Proof eL1 r1 (Set s, d) c sE)
                            => d -> Set s -> TheoremSchemaM eL1 c s r1 d -> Either (TheoremMError s sE eL1 eD) s
establishTheoremM existingConsts already_proven (TheoremSchemaM lemmas proofprog constdict) =
     do
         let mayConstDictErr = constDictTest existingConsts constdict
         maybe (return ()) (throwError . TheoremMErrConstDict) mayConstDictErr
         let sc2 = Prelude.foldr f1 Nothing lemmas
         maybe (return ()) throwError  sc2

         let prfResult = runProofState proofprog mempty (lemmas,constdict)
         case prfResult of
            Left e -> (throwError . TheoremMErrSubproofFailedOnErr) e
            Right (tm, (proven, newconsts), r1) -> do
                     let sc = checkSanity mempty (Set.singleton tm,constdict)
                     maybe (return ()) (throwError . TheoremMErrResultNotSane tm) sc
                     unless (tm `Set.member` (proven `Set.union` already_proven))
                        (throwError  TheoremMErrResultNotProved)
                     return tm
      where
         f1 a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where
                   maybeLemmaNotSane = fmap (TheoremMErrLemmaSanityErr a) (checkSanity mempty (Set.singleton a,constdict))
                   maybeLemmaMissing = if not (a `Set.member` already_proven)
                                          then (Just . TheoremMErrLemmaNotEstablished) a else Nothing



data ProofByAsmSchema s r where
   ProofByAsmSchema :: {
                       asmPrfAsm :: s,
                       asmPrfProof :: r,
                       asmPrfConsequent :: s
                    } -> ProofByAsmSchema s r


data ProofByAsmError senttype sanityerrtype logcicerrtype constdicterrtype where
   ProofByAsmErrAsmNotSane :: senttype -> sanityerrtype -> ProofByAsmError senttype sanityerrtype logcicerrtype consdicterrtype
   ProofByAsmErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype
                                    -> ProofByAsmError senttype sanityerrtype logcicerrtype consdicterrtype



proofByAsm :: ( Ord s, Proof eL1 r1 (Set s, d) c sE, PropLogicSent s, ConstDict d eD) => c -> d ->
                                         Set s -> ProofByAsmSchema s r1 -> Either (ProofByAsmError s sE eL1 eD) s
proofByAsm varstack constdict already_proven (ProofByAsmSchema assumption subproof consequent) =
      do

         let sc = checkSanity varstack (Set.singleton assumption, constdict)
         maybe (return ()) (throwError .  ProofByAsmErrAsmNotSane assumption) sc
         let contextSents = Set.insert assumption already_proven
         let mayTestResult = testSubproof varstack constdict contextSents consequent subproof
         maybe (return ()) (throwError . ProofByAsmErrSubproofFailedOnErr) mayTestResult
         return $ build_implication assumption consequent


data ProofByUGSchema s r where
   ProofByUGSchema :: {
                       ugPrfGeneralizable :: s,
                       ugPrfProof :: r
                       -- right now we are assuming that the var being generalized is type 0, but we need to allow
                       -- for any type so we will need an Int field representing the type of the new variable to be generalized
                       -- over.
                    } -> ProofByUGSchema s r


data ProofByUGError senttype sanityerrtype logcicerrtype constdicterrtype where
   ProofByUGErrSubproofFailedOnErr :: TestSubproofErr senttype sanityerrtype logcicerrtype
                                    -> ProofByUGError senttype sanityerrtype logcicerrtype consdicterrtype

proofByUG :: ( Ord s, Proof eL1 r1 (Set s, d) c sE, PredLogicSent s c o, ConstDict d eD, VarStack c) => c -> d ->
                                         Set s -> ProofByUGSchema s r1 -> Either (ProofByUGError s sE eL1 eD) s
proofByUG varstack constdict already_proven (ProofByUGSchema generalizable subproof) =
      do
         let newVarstack = varStackPushType0 varstack
         let mayTestResult = testSubproof newVarstack constdict already_proven generalizable subproof
         maybe (return ()) (throwError . ProofByUGErrSubproofFailedOnErr) mayTestResult
         return $ applyUG generalizable newVarstack







data BigException s sE where
    BErrResultNotSane :: s -> sE -> BigException s sE
    BErrResultNotProved :: s -> BigException s sE
    BErrLemmaSanity :: s -> sE -> BigException s sE
    BErrLemmaNotEstablished :: s -> BigException s sE
    deriving (Typeable,Show)



data SubproofMErr where
     SubproofMErr :: SomeException -> SubproofMErr
     deriving (Typeable,Show)



instance Exception SubproofMErr

instance (Show s, Typeable s, Show sE,Typeable sE) => Exception (BigException s sE)

class RunSubproofMErrClass s sE | s -> sE where
    bErrResultNotSane :: s -> sE -> BigException s sE
    bErrResultNotSane = BErrResultNotSane 
    bErrResultNotProved :: s -> BigException s sE
    bErrResultNotProved = BErrResultNotProved
    bErrLemmaSanity :: s -> sE -> BigException s sE
    bErrLemmaSanity = BErrLemmaSanity
    bErrLemmaNotEstablished :: s -> BigException s sE
    bErrLemmaNotEstablished = BErrLemmaNotEstablished




runSubproofM :: (Ord s, Monoid r1, Proof eL1 r1 (Set s,d) c sE, Monad m, ConstDict d eD, 
                 MonadThrow m, Show sE,Show s, Typeable s, Typeable sE, Show eL1,Typeable eL1,
                 RunSubproofMErrClass s sE,MonadCatch m)
                 =>   (s-> r1 -> r1) -> Set s -> d -> c-> ProofStateT eL1 c r1 (Set s,d) m (s, x) ->
                           ProofStateT  eL1 c r1 (Set s,d) m (s,x)
runSubproofM f sentences constDict varstack prog =  do
        ((theorem,extraData),(newlyProven,_),r) <- lift (runProofStateT prog varstack (sentences,constDict))
                     `catch` (throwM . SubproofMErr)

        let sc = checkSanity varstack (Set.singleton theorem,constDict)
        case sc of
            Just err -> throwM $ bErrResultNotSane theorem err
            Nothing -> return ()
        let err = bErrResultNotProved theorem

        unless (theorem `Set.member` newlyProven)
                                 (throwM err)
        monadifyProof $ f theorem r
        return (theorem,extraData)



data RunTheoremMExcep senttype constdicterrtype sanityerrtype where
   RunTheoremMErrLemmaSanityErr :: senttype -> sanityerrtype ->  RunTheoremMExcep senttype constdicterrtype sanityerrtype
   RunTheoremMErrLemmaNotEstablished :: senttype -> RunTheoremMExcep senttype constdicterrtype sanityerrtype
   --mRunTheoremMErrSubproof :: SubproofMError senttype sanityerrtype -> RunTheoremMError senttype constdicterrtype sanityerrtype

data ErrConstDict eD where
    ErrConstDict :: eD -> ErrConstDict eD
    deriving (Typeable,Show)

instance (Show eD, Typeable eD) => Exception (ErrConstDict eD)


data ErrLemmaSanityErr s sE where
    ErrLemmaSanityErr :: s-> sE -> ErrLemmaSanityErr s sE
    deriving (Typeable,Show)

instance (Show s, Typeable s, Show sE, Typeable sE) => Exception (ErrLemmaSanityErr s sE)






data ErrLemmaNotEstablished s where
    ErrLemmaNotEstablished :: s->ErrLemmaNotEstablished s
    deriving (Typeable,Show)

instance (Show s, Typeable s) => Exception (ErrLemmaNotEstablished s)


runTheoremM :: (MonadThrow m, Ord s,Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c sE, Monad m, ConstDict d eD,
                       Typeable eD, Show eD,Show s,Typeable s,Typeable sE,Show sE, Show eL1,Typeable eL1, RunSubproofMErrClass s sE,
                       MonadCatch m)
                 =>   (TheoremSchema s r1 d -> r1) -> Set s -> ProofStateT eL1 c r1 (Set s,d) m (s, x) -> d ->
                               ProofStateT eL1 c r1 (Set s,d) m (s,x)
runTheoremM f lemmas prog constDict =  do
        (proven,existingConsts) <- getProofState
        let mayConstDictErr = constDictTest existingConsts constDict
        maybe (return ()) (throwM . ErrConstDict) mayConstDictErr
        let sc2 = Prelude.foldr (f1 proven) Nothing lemmas
        case sc2 of
            Just (RunTheoremMErrLemmaSanityErr s sE) -> throwM $ bErrLemmaSanity s sE
            Just (RunTheoremMErrLemmaNotEstablished s) -> throwM $ bErrLemmaNotEstablished s
            Nothing -> return ()
        runSubproofM (\ s p -> f (TheoremSchema constDict lemmas p s)) lemmas constDict mempty prog
    where
        f1 pr a b = case b of
                   Nothing ->  maybeLemmaNotSane <|> maybeLemmaMissing
                   Just x -> Just x
              where

                   maybeLemmaNotSane = fmap (RunTheoremMErrLemmaSanityErr a) (checkSanity mempty (Set.singleton a,constDict))
                   maybeLemmaMissing = if not (a `Set.member` pr)
                                            then (Just . RunTheoremMErrLemmaNotEstablished) a else Nothing



data ErrAsmSanityErr s sE where
    ErrAsmSanityErr :: s-> sE -> ErrAsmSanityErr s sE
    deriving (Typeable,Show)

instance (Show s, Typeable s, Show sE, Typeable sE) => Exception (ErrAsmSanityErr s sE)





data RunProofByAsmMError senttype sanityerrtype monaderrtype where
   RunProofByAsmMResultNotSane:: senttype -> sanityerrtype -> RunProofByAsmMError senttype sanityerrtype monaderrtype
   -- RunProofByAsmMErrSubproof :: SubproofMError senttype sanityerrtype -> RunProofByAsmMError senttype sanityerrtype monaderrtype


runProofByAsmM :: (Ord s,Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c sE, Monad m,
                      PropLogicSent s,
                      ConstDict d eD,MonadThrow m, Show s, Show sE, Typeable s, Typeable sE, Show eL1, Typeable eL1,
                      RunSubproofMErrClass s sE, MonadCatch m)
                 =>   (ProofByAsmSchema s r1 -> r1) -> s -> ProofStateT eL1 c r1 (Set s,d) m (s, x)
                            -> ProofStateT eL1 c r1 (Set s,d) m (s,x)
runProofByAsmM f asm prog =  do
        (proven,constDict) <- getProofState
        varstack <- ask
        let sc = checkSanity varstack (Set.singleton asm, constDict)
        maybe (return ()) (throwM .  ErrAsmSanityErr asm) sc
        (consequent, extraData) <-
                  runSubproofM (\ s p -> f (ProofByAsmSchema asm p s)) (Set.singleton asm <> proven) constDict varstack prog
        return (build_implication asm consequent,extraData)


-- data RunProofByUGMErr senttype sanityerrtype monaderrtype where
--   RunProofByUGMErrSubproof :: SubproofMError senttype sanityerrtype ->  RunProofByUGMErr senttype sanityerrtype monaderrtype

runProofByUGM :: (Ord s,Monoid c, Monoid r1, Proof eL1 r1 (Set s,d) c sE, Monad m,VarStack c,
                      ConstDict d eD,
                    PredLogicSent s c o,Typeable eL1, Show eL1,Typeable sE, Show sE, Typeable s, Show s, MonadThrow m, MonadCatch m, 
                    RunSubproofMErrClass s sE)
                 =>   (ProofByUGSchema s r1 -> r1) -> ProofStateT eL1 c r1 (Set s,d) m (s, x)
                            -> ProofStateT eL1 c r1 (Set s,d) m (s,x)
runProofByUGM f prog =  do
        (proven,constDict) <- getProofState
        varstack <- ask
        let newVarstack = varStackPushType0 varstack
        (generalizable, extraData) <-
                  runSubproofM (\ s p -> f (ProofByUGSchema s p)) proven constDict newVarstack prog
        return (applyUG generalizable newVarstack,extraData)


class PropLogicSent s  where
    buildAdj :: s -> s -> s
    parseAdj :: s -> Maybe(s,s)
    build_implication:: s->s->s
    parse_implication:: s -> Maybe (s,s)
    build_not :: s -> s
    buildDis :: s -> s -> s


class (PropLogicSent s ) => PredLogicSent s c o | s->o, s-> c where
    parseExists :: s -> Maybe (o->s)
    applyUG ::s -> c -> s




data PropLogR s d c sE eD where
    MP :: s -> s -> PropLogR s d c sE eD
    PLProofByAsm :: ProofByAsmSchema s [PropLogR s d c sE eD]-> PropLogR s d c sE eD
    PLTheorem :: TheoremSchema s [PropLogR s d c sE eD ] d -> PropLogR s d c sE eD
    PLTheoremM :: TheoremSchemaM (PropLogError s sE eD) c s [PropLogR s d c sE eD ] d -> PropLogR s d c sE eD
    PLExclMid :: s -> PropLogR s d c sE eD


data PropLogError s sE eD where
    PLErrMPImpNotProven :: s-> PropLogError s sE eD
    PLErrMPanteNotProven :: s-> PropLogError s sE eD
    PLErrSentenceNotImp :: s -> PropLogError s sE eD
    PLErrPrfByAsmErr :: ProofByAsmError s sE (PropLogError s sE eD) eD -> PropLogError s sE eD
    PLErrTheorem :: TheoremError s sE (PropLogError s sE eD) eD -> PropLogError s sE eD
    PLErrTheoremM :: TheoremMError s sE (PropLogError s sE eD) eD -> PropLogError s sE eD
    PLExclMidSanityErr :: s -> sE -> PropLogError s sE eD

pLrunProof :: (Monoid c,Monoid s, StandardState (Set s, d) c sE, Ord s, PropLogicSent s, ConstDict d eD,
               Proof (PropLogError s sE eD) [PropLogR s d c sE eD] (Set s, d) c sE) =>
                            c -> PropLogR s d c sE eD -> (Set s, d) -> Either (PropLogError s sE eD) s
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
             case checkSanity varStack (Set.singleton s,constDict) of
                Just err -> throwError $ PLExclMidSanityErr s err
                Nothing -> return $ buildDis s (build_not s)




instance (Monoid c, Monoid s, Ord s, Monoid d, StandardState (Set s, d) c sE,
          PropLogicSent s, ConstDict d eD)
          => Proof (PropLogError s sE eD) [PropLogR s d c sE eD] (Set s, d) c sE where
  runProof :: c -> [PropLogR s d c sE eD] -> (Set s, d) -> Either (PropLogError s sE eD) (Set s, d)
  runProof varStack rs (proven, constDict) = foldM f (proven,constDict) rs
      where
          f (pr, c) r =  fmap g (pLrunProof varStack r (pr,c))
            where
                g s = (pr <> Set.singleton s,c )




data RPL p where
    PLMp :: p -> RPL p
    PLAdj :: p -> RPL p
    -- RPLSubproof :: [BLRule p [RPL p]] -> RPL p





class Monoid c => VarStack c  where
    varStackPushType0 :: c -> c




class SchemaLift r1 r2 where
    schemaLift :: r1 -> r2















-- data PredSPError s sE eL d where
--   PredSPErrPLSubProofErr :: SubproofError s sE eL d -> PredSPError s sE eL d
--   PredSPError :: PredSPError s sE eL d
--   PredSPErrGenNotSane :: s -> sE -> PredSPError s sE eL d
--   PredSPErrSubproofFailedOnErr :: eL -> PredSPError s sE eL d
--   PredSPResultGenNotProved :: PredSPError s sE eL d




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

main :: IO ()
main = do
    print "HI BITCH"
    print "WFT??"
    print "FUCK"