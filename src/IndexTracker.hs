module IndexTracker (
    IndexTracker,
    newIndex,
    dropIndices,
    runIndexTracker,
    setBaseIndex

)
  where
import Control.Monad.State
import Control.Monad.Accum (MonadAccum(add))
import Control.Monad (unless)
import Data.Monoid (Sum(..), getSum)

type IndexTracker o =  State (Sum Int) o



newIndex :: (MonadState (Sum Int) m) => m Int
newIndex = do
    currentIndex <- get
    put (currentIndex + Sum 1)
    return $ getSum currentIndex

dropIndices :: (MonadState (Sum Int) m) => Int -> m ()
dropIndices n = do
    currentIndex <- get
    put (currentIndex - Sum n)




runIndexTracker :: IndexTracker a -> a
runIndexTracker tracker =
    let initialIndex = 0
    in evalState tracker initialIndex


setBaseIndex :: (MonadState (Sum Int) m) => [Int] -> m ()
setBaseIndex idxs = do
    let baseIdx = if null idxs then 0 else maximum idxs + 1
    put (Sum baseIdx)

