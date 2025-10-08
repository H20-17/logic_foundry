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

type IndexTracker o =  State (Sum Int) o



newIndex :: (MonadState (Sum Int) m) => m Int
newIndex = do
    currentIndex <- get
    put (currentIndex + Sum 1)
    return $ getSum currentIndex


newIndices :: (MonadState (Sum Int) m) => Int -> m [Int]
newIndices n = do
    currentIndex <- get
    put (currentIndex + Sum n)
    let currentIndexInt = getSum currentIndex
    return $ [currentIndexInt .. currentIndexInt + n - 1]

dropIndices :: (MonadState (Sum Int) m) => Int -> m ()
dropIndices n = do
    currentIndex <- get
    put (currentIndex - Sum n)




runIndexTracker :: [Int] -> IndexTracker a -> a
runIndexTracker protectedIdxs tracker =
    let initialIndex = if null protectedIdxs then 0 else maximum protectedIdxs + 1
    in evalState tracker (Sum initialIndex)



