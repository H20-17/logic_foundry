module IndexTracker (
    IndexTracker,
    newIndex,
    dropIndices,
    addIndices,
    runIndexTracker,
    addTemplateVarsFromSet,
    TemplateVarTracker(..)
)
  where
import Control.Monad.State
import Control.Monad.Accum (MonadAccum(add))
import Control.Monad (unless)

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


addIndices :: Int -> IndexTracker ()
addIndices n = do
       currentIndex <- get
       put (currentIndex + n)


runIndexTracker :: IndexTracker a -> (a, Int)
runIndexTracker tracker =
    let initialIndex = 0
    in runState tracker initialIndex




class (Monad m) => TemplateVarTracker m where
    newTemplateVarIdx :: m Int
    dropTemplateVarIdxs :: Int -> m ()
    addTemplateVarIdxs :: Int -> m ()

instance TemplateVarTracker (State Int)  where
    newTemplateVarIdx :: State Int Int
    newTemplateVarIdx = newIndex
    dropTemplateVarIdxs :: Int -> State Int ()
    dropTemplateVarIdxs = dropIndices
    addTemplateVarIdxs :: Int -> State Int ()
    addTemplateVarIdxs = addIndices

addTemplateVarsFromSet :: (TemplateVarTracker m) => [Int] -> m ()
addTemplateVarsFromSet idxs = unless (null idxs) ((addTemplateVarIdxs . maximum) idxs)
