module IndexTracker (
    IndexTracker,
    newIndex,
    dropIndices,
    runIndexTracker,
    TemplateVarTracker(..)
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

runIndexTracker :: IndexTracker a -> (a, Int)
runIndexTracker tracker =
    let initialIndex = 0
    in runState tracker initialIndex

class TemplateVarTracker m where
    newTemplateVar :: m Int
    dropTemplateVars :: Int -> m ()
    runTemplateVarTracker :: m a -> (a, Int)

instance TemplateVarTracker (State Int)  where
    newTemplateVar :: IndexTracker Int
    newTemplateVar = newIndex
    dropTemplateVars :: Int -> IndexTracker ()
    dropTemplateVars = dropIndices
    runTemplateVarTracker :: IndexTracker a -> (a, Int)
    runTemplateVarTracker = runIndexTracker
