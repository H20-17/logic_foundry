module RuleSets.PredLogicDevel
(
    runProofAtomic, 
    establishTmSilentM,
    runProofByUG,
    LogicRule(..)
) where

import RuleSets.Internal.PredLogic(
    runProofAtomic,
    LogicRule(..), 
    PredLogSchemaRule(..),
    establishTmSilentM,
    runProofByUG
  )