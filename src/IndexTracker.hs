module IndexTracker (
    IndexTracker,
    newIndex,
    newIndices,
    dropIndices,
    runIndexTracker

)
  where
import Control.Monad.State
import Control.Monad.Accum (MonadAccum(add))
import Control.Monad (unless)
import Data.Monoid (Sum(..), getSum)
import GHC.Stats (RTSStats(cumulative_par_balanced_copied_bytes))

type IndexTracker o =  State (Sum Int) o



newIndex :: (MonadState (Sum Int) m) => m Int
newIndex = do
    currentIndex <- get
    put (currentIndex + Sum 1)
    return $ getSum currentIndex


newIndices :: (MonadState (Sum Int) m) => Int -> m [Int]
newIndices n = do
    currentIndex <- get
    let currentIndexInt = getSum currentIndex
    put (currentIndex + Sum n)
    return [currentIndexInt + i | i <- [0 .. n - 1]]


dropIndices :: (MonadState (Sum Int) m) => Int -> m ()
dropIndices n = do
    currentIndex <- get
    put (currentIndex - Sum n)




runIndexTracker :: IndexTracker a -> a
runIndexTracker tracker = 
    let 
         (final_state, _) = runState tracker (Sum 0)
    in
         final_state


