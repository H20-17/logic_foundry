{-# LANGUAGE UndecidableInstances #-}
module IndexTracker (
    IndexTracker,
    newIndex,
    newIndices,
    dropIndices,
    runIndexTracker,
    BoundVarState(..)

)
  where
import Control.Monad.State
import Control.Monad.Accum (MonadAccum(add))
import Control.Monad (unless)
import Data.Monoid (Sum(..), getSum)
import GHC.Stats (RTSStats(cumulative_par_balanced_copied_bytes))
import Distribution.Simple (Bound)

type IndexTracker o =  State (Sum Int) o



class (Monad m,MonadState a m) => BoundVarState a m where
    bvsProject :: m (Sum Int)
    bvsEmbed :: Sum Int -> m ()
    
instance (Monad m,MonadState (Sum Int, [Int]) m) 
          => BoundVarState (Sum Int, [Int])  m where
    bvsProject :: m (Sum Int)
    bvsProject = do
        state <- get
        return $ fst state
    bvsEmbed :: Sum Int -> m ()
    bvsEmbed a = do
        (_,b) <- get
        put (a, b)            

instance (Monad m, MonadState (Sum Int) m) =>
           BoundVarState (Sum Int) m where
    bvsProject :: m (Sum Int)
    bvsProject = get
    bvsEmbed :: Sum Int -> m ()
    bvsEmbed = put





newIndex :: (MonadState s m, BoundVarState s m) => m Int
newIndex = do
    currentIndex <- bvsProject
    bvsEmbed $ currentIndex + ((Sum 1):: Sum Int)
    return $ getSum currentIndex



newIndices :: (MonadState s m, BoundVarState s m) => Int -> m [Int]
newIndices n = do
    currentIndex <- bvsProject
    let currentIndexInt = getSum currentIndex
    bvsEmbed $ currentIndex + (Sum n)
    return [currentIndexInt + i | i <- [0 .. n - 1]]


dropIndices :: (MonadState s m, BoundVarState s m) => Int -> m ()
dropIndices n = do
    currentIndex <- bvsProject
    bvsEmbed $ currentIndex - ((Sum n):: Sum Int)




runIndexTracker :: IndexTracker a -> a
runIndexTracker tracker = 
    let 
         (final_state, _) = runState tracker (Sum 0)
    in
         final_state


