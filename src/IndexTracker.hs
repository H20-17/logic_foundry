module IndexTracker (
    IndexTracker,
    newIndex,
    dropIndices,
    runIndexTracker,
    setBaseIndexFromSet,
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


setBaseIndexFromSet :: [Int] -> IndexTracker ()
setBaseIndexFromSet idxs = do
    let newBase = if null idxs then 0 else maximum idxs + 1
    put newBase

class TemplateVarTracker m where
    newTemplateVarIdx :: m Int
    dropTemplateVarIdxs :: Int -> m ()
    setTemplateVarBaseFromSet :: [Int] -> m ()


instance TemplateVarTracker (State Int)  where
    newTemplateVarIdx :: State Int Int
    newTemplateVarIdx = newIndex
    dropTemplateVarIdxs :: Int -> State Int ()
    dropTemplateVarIdxs = dropIndices
    setTemplateVarBaseFromSet :: [Int] -> State Int ()
    setTemplateVarBaseFromSet = setBaseIndexFromSet
    
