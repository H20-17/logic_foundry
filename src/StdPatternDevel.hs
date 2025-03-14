module StdPatternDevel(
    runProofOpen, PredLogSchemaRule(..), runSubproofM
) where

import Internal.StdPattern
    ( 
      runSubproofM,        

      PredLogSchemaRule(..)
     )
   
import Kernel(runProofOpen)