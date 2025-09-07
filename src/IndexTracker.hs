module IndexTracker (
    IndexTracker,
    newIndex,
    dropIndices,
    runIndexTracker
)
  where
import Control.Monad.State

type IndexTracker o =  State Int o



newIndex :: IndexTracker Int
newIndex = do
    currentIndex <- get
    put (currentIndex + 1)
    return currentIndex

dropIndices :: Int -> IndexTracker ()
dropIndices n = do
       currentIndex <- get
       put (currentIndex - n)

runIndexTracker :: IndexTracker a -> [Int] -> (a, Int)
runIndexTracker tracker idxSet =
    let initialIndex = if null idxSet then 0 else maximum idxSet + 1
    in runState tracker initialIndex