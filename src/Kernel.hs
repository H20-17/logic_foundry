{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UndecidableInstances #-}

module Kernel (
  Proof(..),
  runProof,
  ProofGeneratorT,
  runProofGeneratorTOpen,
  runProofGeneratorT,
  getProofState,
  monadifyProof,
  modifyPS,
  Commentable(..),
  writeComment
) where
import Data.Text (Text)
import Control.Monad.RWS
    ( MonadTrans(..),
      MonadReader(ask, local),
      MonadState(put, get),
      MonadWriter(tell),
      RWST(..) )
import Control.Monad (Monad((>>=)))
import Control.Monad.Catch (MonadThrow(throwM), MonadCatch(catch), Exception)
import Data.Monoid (Monoid,mempty, (<>),Last(..))
import Data.Typeable (Typeable)
import GHC.Stack.Types (HasCallStack)

default(Text)


class (Monoid s, Monoid stpT, Monoid c) => Proof e r s c stpT resultT | r -> s, r->e, r->c, r -> stpT, r->resultT  where
      runProofOpen :: r -> c -> s -> Either e (s , stpT, Last resultT)


runProof :: Proof e r s c stpT resultT => r -> Either e (stpT, s)
runProof r = do
                (state, steps, lastRes) <- runProofOpen r mempty mempty
                return (steps, state)


data ProofGeneratorT resultT stpT c r s m x where
  ProofGenInternalT  :: {runProofGenTInternal :: RWST c (r,stpT, Last resultT) s m x}
                   -> ProofGeneratorT resultT stpT c r s m x


runProofGeneratorTOpen ::  (Monad m, MonadThrow m, Proof eL r s c stpT resultT) => ProofGeneratorT resultT stpT c r s m x -> c -> s -> m (x,s, r,stpT, Last resultT)
runProofGeneratorTOpen ps context state = do
           (x, s, (r,stpT, resultT)) <- runRWST (runProofGenTInternal ps) context state
           return (x,s,r,stpT, resultT)

runProofGeneratorT :: (MonadThrow m, Proof eL r s c stpT resultT) => ProofGeneratorT resultT stpT c r s m x -> m (x, r, stpT, s)
runProofGeneratorT ps = do
                      (extra, state, proof, steps, prfResult) <- runProofGeneratorTOpen ps mempty mempty
                      return (extra, proof, steps, state)

instance (Monad m) => Functor (ProofGeneratorT resultT stpT c r s m) where
     fmap :: Monad m =>
              (a -> b) -> ProofGeneratorT resultT stpT c r s m a -> ProofGeneratorT resultT stpT c r s m b
     fmap f (ProofGenInternalT  g) = ProofGenInternalT  $ fmap f g





instance (Monoid r, Monad m, Proof eL r s c stpT resultT) => Applicative (ProofGeneratorT resultT stpT c r s m) where
   pure :: (Monad m, Proof eL r s c stpT resultT ) => a -> ProofGeneratorT resultT stpT c r s m a
   pure x = ProofGenInternalT  $ pure x


   (<*>) :: (Monad m, Proof eL r s c stpT resultT) => ProofGeneratorT resultT stpT c r s m (a -> b)
                                           -> ProofGeneratorT resultT stpT c r s m a -> ProofGeneratorT resultT stpT c r s m b
   ProofGenInternalT  a <*> ProofGenInternalT  b = ProofGenInternalT  $ a <*> b




instance (Monoid r,Proof eL r s c stpT resultT, Monad m) => Monad (ProofGeneratorT resultT stpT c r s m) where
   (>>=) :: (Proof eL r s c stpT resultT, Monad m) => ProofGeneratorT resultT stpT c r s m a
                                           -> (a -> ProofGeneratorT resultT stpT c r s m b)
                                        -> ProofGeneratorT resultT stpT c r s m b
   ProofGenInternalT  y >>= g = ProofGenInternalT  (y >>= runProofGenTInternal . g)



instance (Monoid r,Proof eL r s c stpT resultT) =>  MonadTrans (ProofGeneratorT resultT stpT c r s) where
      lift :: (Monoid r, Monad m) => m a -> ProofGeneratorT resultT stpT c r s m a
      lift = ProofGenInternalT  . lift


getProofState :: (Monoid r, Proof eL r s c stpT resultT, Monad m) => ProofGeneratorT resultT stpT c r s m s
getProofState = ProofGenInternalT  get




instance (Monoid r,Proof eL r s c stpT resultT, Monad m, MonadThrow m) => MonadThrow (ProofGeneratorT resultT stpT c r s m) where
  throwM :: (Monoid r, Proof eL r s c stpT resultT, Monad m, MonadThrow m, HasCallStack, Exception e) =>
                 e -> ProofGeneratorT resultT stpT c r s m a
  throwM = ProofGenInternalT  . lift . throwM

instance (Proof eL r s c stpT resultT , Monoid r, MonadThrow m, MonadCatch m) 
                   => MonadCatch (ProofGeneratorT resultT stpT c r s m) where
       catch :: (Proof eL r s c stpT resultT, HasCallStack, MonadThrow m, MonadCatch m,Exception e) =>
            ProofGeneratorT resultT stpT c r s m a -> (e -> ProofGeneratorT resultT stpT c r s m a) 
                   -> ProofGeneratorT resultT stpT c r s m a
       catch z errhandler = ProofGenInternalT  (RWST \c s -> do
            (a,b,c,d,e)<-catch (runProofGeneratorTOpen z c s) (\err -> runProofGeneratorTOpen (errhandler err) c s)
            return (a,b,(c,d,e))
            )


instance (Monad m, Monoid r, Monad (ProofGeneratorT resultT stpT c r s m), Monoid stpT) 
            => MonadReader c (ProofGeneratorT resultT stpT c r s m) where
   ask ::  ProofGeneratorT resultT stpT c r s m c
   ask = ProofGenInternalT  ask
   local :: (c->c) -> ProofGeneratorT resultT stpT c r s m a -> ProofGeneratorT resultT stpT c r s m a
   local f (ProofGenInternalT  g) = ProofGenInternalT  $ local f g

data MonadifyProofException eL where
  MonadifyProofException :: eL -> MonadifyProofException eL
  deriving (Typeable, Show)


instance (Show eL,Typeable eL) => Exception (MonadifyProofException eL)
monadifyProof :: (Monoid r, Proof eL r s c stpT resultT, Monad m,  MonadThrow m, 
                 Show eL, Typeable eL) => r -> ProofGeneratorT resultT stpT c r s m (s,stpT, Maybe resultT)
monadifyProof p = ProofGenInternalT  $ do
                        c <- ask
                        u <- get
                        let proofResult = runProofOpen p c u
                        (resultState, newSteps, prfResult) <- either (lift . throwM . MonadifyProofException) return proofResult
                        put (u <> resultState)
                        tell (p,newSteps, prfResult)
                        return (resultState,newSteps, getLast prfResult)


modifyPS :: (Monad m, Monoid r1, Monoid r2,Proof eL1 r1 s c stpT resultT, 
             Proof eL2 r2 s c stpT resultT,  MonadThrow m, Typeable eL2, Show eL2)
             =>  (r1 -> r2) -> ProofGeneratorT resultT stpT c r1 s m a
                       -> ProofGeneratorT resultT stpT c r2 s m a
modifyPS g m1 = do
    c <- ask
    ps <- getProofState
    (datum,_,rules,steps, prfResult) <- lift $ runProofGeneratorTOpen m1 c ps
    monadifyProof $ g rules
    return datum


class Commentable stpT where
   buildCommentStep :: Text -> stpT

writeComment :: (Monad m,Commentable stpT, Monoid r, Monoid stpT) 
            => Text -> ProofGeneratorT resultT stpT c r s m ()
writeComment comment = ProofGenInternalT $ do
     let writeStep = buildCommentStep comment
     tell (mempty,writeStep,mempty)