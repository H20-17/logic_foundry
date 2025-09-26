{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
module RuleSets.ZFC.Helpers
(
    specificationM,
    replacementM,
    integerMembershipM,
    integerNegationM,
    integerAdditionM,
    integerMultiplicationM,
    integerCompareM,
    integersAreUrelementsM,
    integerInequalityM,
    emptySetAxiomM,
    extensionalityAxiomM,
    emptySetNotIntM,
    regularityAxiomM,
    unionAxiomM,
    powerSetAxiomM,
    pairingAxiomM,
    axiomOfChoiceM,
    intOrderAntiSymmetryM,
    intOrderReflexivityM,
    intOrderTransitivityM,
    intOrderTotalityM,
    intAddClosureAxiomM,
    intMulClosureAxiomM,
    intNegClosureAxiomM,
    intAddAssociativityM,
    intAddCommutativityAxiomM,
    intAddIdentityAxiomM,
    intAddInverseAxiomM,
    intMulAssociativityAxiomM,
    intMulCommutativityAxiomM,
    intMulIdentityAxiomM,
    intDistributivityAxiomM,
    intOrderAddCompatibilityAxiomM,
    intOrderMulCompatibilityAxiomM,
    natWellOrderingAxiomM,
    powerSetInstantiateM,
    runProofByUGM,
    multiUGM,
    MetaRuleError(..),
    builderXM
) where


import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless,when )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
import Control.Applicative ( Alternative((<|>)) )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import GHC.Stack.Types ( HasCallStack )
import Data.Data (Typeable)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Control.Arrow ( left )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Reader ( MonadReader(ask) )
import Control.Monad.State ( MonadState(get) )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.Maybe ( isNothing )

import Kernel
import Internal.StdPattern

import RuleSets.BaseLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   HelperConstraints(..),
   SentConstraints(..))
import qualified RuleSets.BaseLogic.Core as REM

import RuleSets.PropLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   LogicSent,
   SubproofMException(..),
   MetaRuleError(..),
   HelperConstraints(..),
   SentConstraints(..))
import qualified RuleSets.PropLogic.Core as PL

import RuleSets.PredLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   LogicSent,
   SubproofMException(..),
   MetaRuleError(..),
   HelperConstraints(..),
   SentConstraints(..),
   MonadSent)
import qualified RuleSets.PredLogic.Core as PREDL
import qualified RuleSets.PredLogic.Helpers as PREDL
import GHC.Num (integerMul)
import RuleSets.ZFC.Core
import RuleSets.BaseLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PredLogic.Helpers hiding
     (MetaRuleError(..),
     runProofByUGM,
     multiUGM)
import RuleSets.PropLogic.Helpers hiding
     (MetaRuleError(..))

import IndexTracker


standardRuleM :: HelperConstraints sE s eL m r t
       => r -> ProofGenTStd () r s Text m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex



specificationM :: HelperConstraints sE s eL m r t
       => [Int] -> Int -> t -> s -> ProofGenTStd () r s Text m (s,[Int])
specificationM outerIdxs idx t s = standardRuleM (specification outerIdxs idx t s)



replacementM :: HelperConstraints sE s eL m r t
       => [Int] -> Int -> Int -> t -> s -> ProofGenTStd () r s Text m (s,[Int])
replacementM outerIdxs idx1 idx2 t s = standardRuleM (replacement outerIdxs idx1 idx2 t s)


integerMembershipM, integerNegationM :: HelperConstraints sE s eL m r t
       => Int -> ProofGenTStd () r s Text m (s,[Int])
integerMembershipM i = standardRuleM (integerMembership i)
integerNegationM i = standardRuleM (integerNegation i)

integerAdditionM, integerMultiplicationM, integerCompareM, integerInequalityM
 :: HelperConstraints sE s eL m r t
       => Int -> Int -> ProofGenTStd () r s Text m (s,[Int])
integerAdditionM i1 i2 = standardRuleM (integerAddition i1 i2)
integerMultiplicationM i1 i2 = standardRuleM (integerMultiplication i1 i2)
integerCompareM i1 i2 = standardRuleM (integerCompare i1 i2)
integerInequalityM i1 i2 = standardRuleM (integerInequality i1 i2)


integersAreUrelementsM, emptySetAxiomM, extensionalityAxiomM,emptySetNotIntM,regularityAxiomM, unionAxiomM,
             powerSetAxiomM, pairingAxiomM, axiomOfChoiceM, intOrderAntiSymmetryM,
             intOrderReflexivityM, intOrderTransitivityM, intOrderTotalityM,
             intAddClosureAxiomM, intMulClosureAxiomM, intNegClosureAxiomM,
             intAddAssociativityM, intAddCommutativityAxiomM, intAddIdentityAxiomM, intAddInverseAxiomM,
             intMulAssociativityAxiomM, intMulCommutativityAxiomM, intMulIdentityAxiomM,
             intDistributivityAxiomM,intOrderAddCompatibilityAxiomM, intOrderMulCompatibilityAxiomM,
             natWellOrderingAxiomM
       :: HelperConstraints sE s eL m r t
       => ProofGenTStd () r s Text m (s,[Int])
integersAreUrelementsM = standardRuleM integersAreUrelements
emptySetAxiomM = standardRuleM emptySetStatement
extensionalityAxiomM = standardRuleM extensionality
emptySetNotIntM = standardRuleM emptySetNotInt
regularityAxiomM = standardRuleM regularity
unionAxiomM = standardRuleM union
powerSetAxiomM = standardRuleM powerSetAxiom
pairingAxiomM = standardRuleM pairing
axiomOfChoiceM = standardRuleM choice
intOrderAntiSymmetryM = standardRuleM intOrderAntiSymmetry
intOrderReflexivityM = standardRuleM intOrderReflexivity
intOrderTransitivityM = standardRuleM intOrderTransitivity
intOrderTotalityM = standardRuleM intOrderTotality
intAddClosureAxiomM        = standardRuleM intAddClosure
intMulClosureAxiomM        = standardRuleM intMulClosure
intNegClosureAxiomM        = standardRuleM intNegClosure
intAddAssociativityM       = standardRuleM intAddAssociativity -- Was previously started
intAddCommutativityAxiomM  = standardRuleM intAddCommutativity
intAddIdentityAxiomM       = standardRuleM intAddIdentity
intAddInverseAxiomM        = standardRuleM intAddInverse
intMulAssociativityAxiomM  = standardRuleM intMulAssociativity
intMulCommutativityAxiomM  = standardRuleM intMulCommutativity
intMulIdentityAxiomM       = standardRuleM intMulIdentity
intDistributivityAxiomM    = standardRuleM intDistributivity
intOrderAddCompatibilityAxiomM = standardRuleM intOrderAddCompatibility
intOrderMulCompatibilityAxiomM = standardRuleM intOrderMulCompatibility
natWellOrderingAxiomM = standardRuleM natWellOrdering




-- | Helper to instantiate the power set axiom and return the power set.
-- |
-- | Note: This helper requires that 'isSet x' has already been proven
-- | in the current proof context.
-- |
-- | Proof Strategy:
-- | 1. Takes an object 'x' as an argument.
-- | 2. Assumes 'isSet x' is a proven premise in the current context.
-- | 3. Instantiates the Axiom of Power Set with 'x'. This proves: isSet(x) → ∃P(...)
-- | 4. Uses Modus Ponens with the proven 'isSet x' to derive the existential part of the axiom:
-- |    `∃P (isSet(P) ∧ ∀Y(Y∈P ↔ Y⊆x))`.
-- | 5. Uses Existential Instantiation (`eiHilbertM`) on this proposition. This introduces
-- |    the Hilbert term for the power set (`PowerSet(x)`) and proves its defining property:
-- |    `isSet(PowerSet(x)) ∧ ∀Y(...)`.
powerSetInstantiateM :: HelperConstraints sE s eL m r t =>
    t -> -- ^ The object 'x' for which to prove its power set is a set.
    ProofGenTStd () r s Text m (s, [Int], t)
powerSetInstantiateM x = do
    runProofBySubArgM $ do
        -- Step 1: Get the Axiom of Power Set from the ZFC rule set.
        (powerSetAxiom_proven, _) <- powerSetAxiomM

        -- Step 2: Instantiate the axiom with our object `x`.
        -- This proves: isSet(x) → ∃P (isSet(P) ∧ ...)
        (instantiatedAxiom, _) <- uiM x powerSetAxiom_proven

        -- Step 3: Use Modus Ponens. This relies on `isSet x` being already proven
        -- in the parent context where this helper is called.
        (exists_P, _) <- mpM instantiatedAxiom

        -- Step 4: Apply Hilbert's Existential Instantiation to the existential proposition.
        -- This introduces the `powerSet x` object and proves its property.
        -- `prop_of_powSet` is: isSet(powerSet x) ∧ ∀Y(...)
        (prop_of_powSet, _, powSet_obj) <- eiHilbertM exists_P
        return powSet_obj






runProofByUGM :: HelperConstraints sE s eL m r t
                 =>  ProofGenTStd () r s Text m x
                            -> ProofGenTStd () r s Text m (s, [Int])
runProofByUGM = PREDL.runProofByUGM ()

multiUGM :: HelperConstraints sE s eL m r t =>
    Int ->                             -- ^ Number of UG's
    ProofGenTStd () r s Text m x ->       -- ^ The core program. Its monadic return 'x' is discarded.
                                           --   It must set 'Last s' with the prop to be generalized.
    ProofGenTStd () r s Text m (s, [Int])  -- ^ Returns (final_generalized_prop, its_index).
multiUGM n = PREDL.multiUGM (replicate n ()) 


-- | Gives us properties of a builder set, as well as the builder set object,
-- | after builderInstantiateM has been called
-- | Reproduces some of the work of builderInstantiateM but allows
-- | us to pass less information to functions as a consequence.
builderXM ::  MonadSent s t m => 
    t ->  -- t: The instantiated set, with all of the original outer context
                --    variables instantiated
    (t -> s) -> -- p_pred: the original p_template expressed as a function (ObjDeBr -> PropDeBr),
                -- the application of which will contain instantiated free variables.
    m t -- the properties of the builderset and the builder set object      
builderXM t p_pred = do
    idx <- newIndex
    let  setObj = builderX idx t (p_pred (x idx))
    dropIndices 1
    return setObj


data MetaRuleError s where
   MetaRuleErrNotClosed :: s -> MetaRuleError s
   MetaRuleErrFreeVarsQuantCountMismatch :: MetaRuleError s

   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)


