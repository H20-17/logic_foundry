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
    builderInstantiateM,
    powerSetInstantiateM,
    MetaRuleError(..)
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
   runProofAtomic)
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
   MetaRuleError(..))
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
   MetaRuleError(..))
import qualified RuleSets.PredLogic.Core as PREDL
import GHC.Num (integerMul)
import RuleSets.ZFC.Core
import RuleSets.BaseLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PredLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PropLogic.Helpers hiding
     (MetaRuleError(..))

type HelperConstraints sE s eL o tType m r t =
    ( Monoid r
    , Monad m
    , Show sE, Typeable sE
    , Show s, Typeable s
    , Show eL, Typeable eL
    , MonadThrow m
    , Show o, Typeable o
    , Show tType, Typeable tType
    , TypedSent o tType sE s
    , Monoid (PrfStdState s o tType)
    , ProofStd s eL r o tType
    , StdPrfPrintMonad s o tType m
    , LogicRuleClass r s sE t
    , PREDL.LogicRuleClass r s t tType sE o
    , PREDL.SubproofRule r s o tType
    , ShowableSent s
    , PL.LogicRuleClass r s tType sE o
    , PL.SubproofRule r s
    , Typeable t
    , Show t
    , PREDL.LogicSent s t tType o
    , TypeableTerm t o tType sE
    , REM.LogicRuleClass r s o tType sE
    , StdPrfPrintMonad s o tType (Either SomeException)
    , REM.SubproofRule r s
    , PREDL.LogicTerm t
    )


standardRuleM :: HelperConstraints sE s eL o tType m r t
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex



specificationM :: HelperConstraints sE s eL o tType m r t
       => [Int] -> Int -> t -> s -> ProofGenTStd tType r s o m (s,[Int])
specificationM outerIdxs idx t s = standardRuleM (specification outerIdxs idx t s)



replacementM :: HelperConstraints sE s eL o tType m r t
       => [Int] -> Int -> Int -> t -> s -> ProofGenTStd tType r s o m (s,[Int])
replacementM outerIdxs idx1 idx2 t s = standardRuleM (replacement outerIdxs idx1 idx2 t s)


integerMembershipM, integerNegationM :: HelperConstraints sE s eL o tType m r t
       => Int -> ProofGenTStd tType r s o m (s,[Int])
integerMembershipM i = standardRuleM (integerMembership i)
integerNegationM i = standardRuleM (integerNegation i)

integerAdditionM, integerMultiplicationM, integerCompareM, integerInequalityM
 :: HelperConstraints sE s eL o tType m r t
       => Int -> Int -> ProofGenTStd tType r s o m (s,[Int])
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
       :: HelperConstraints sE s eL o tType m r t
       => ProofGenTStd tType r s o m (s,[Int])
integersAreUrelementsM = standardRuleM integersAreUrelements
emptySetAxiomM = standardRuleM emptySet
extensionalityAxiomM = standardRuleM extensionality
emptySetNotIntM = standardRuleM emptySetNotInt
regularityAxiomM = standardRuleM regularity
unionAxiomM = standardRuleM union
powerSetAxiomM = standardRuleM powerSet
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


-- | A generic and powerful helper that instantiates the Axiom of Specification with
-- | provided parameter terms, and then uses Existential Instantiation to construct
-- | the specified set object and prove its defining property.
-- |
-- | This function replaces the more complex `specificationFreeMBuilder`. The caller is now
-- | responsible for providing the terms to instantiate the parameters of the source set
-- | and predicate, which should use `X k` template variables for those parameters.
-- |
-- | @param instantiationTerms The list of `ObjDeBr` terms to instantiate with.
-- | @param outerTemplateIdxs  The list of `Int` indices for the `X` variables in the templates
-- |                           that will be universally quantified. The order must correspond
-- |                           to `instantiationTerms`.
-- | @param spec_var_X_idx     The `Int` index for the `X` variable that is the variable of specification
-- |                           (the 'x' in {x ∈ T | P(x)}).
-- | @param source_set_template The source set `T`, which may contain `X k` parameters.
-- | @param p_template         The predicate `P`, which uses `X spec_var_X_idx` for the specification
-- |                           variable and may contain `X k` parameters.
-- | @return A tuple containing the proven defining property of the new set, its proof index,
-- |         and and a tuple of type (ObjDeBr, ObjDeBr, PropDeBr) which is the newly built set,
-- |         the instantiated source set, and the instantiated p_template.
builderInstantiateM :: HelperConstraints sE s eL o tType m r t =>
    [t] ->    -- instantiationTerms
    [Int] ->        -- outerTemplateIdxs
    Int ->          -- spec_var_X_idx
    t ->      -- source_set_template
    s ->     -- p_template
    ProofGenTStd tType r s o m (s,[Int], (t,t,s))
builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_X_idx source_set_template p_template =
    runProofBySubArgM $ do
        -- Step 1: Get the closed, universally quantified Axiom of Specification.
        -- 'specificationM' quantifies over the parameters specified in 'outerTemplateIdxs'.
        (closedSpecAxiom, _) <- specificationM outerTemplateIdxs spec_var_X_idx source_set_template p_template

        -- Step 2: Use multiUIM to instantiate the axiom with the provided terms.
        -- This proves the specific existential statement for the given parameters.
        (instantiated_existential_prop, _) <- multiUIM closedSpecAxiom instantiationTerms

        -- Step 3: Apply Existential Instantiation to get the Hilbert object and its property.
        -- This is the final result of the construction.
        (defining_prop, prop_idx, built_obj) <- eiHilbertM instantiated_existential_prop

        let instantiated_source_set = termSubXs (zip outerTemplateIdxs instantiationTerms) source_set_template
        let instantiated_p_template = sentSubXs (zip outerTemplateIdxs instantiationTerms) p_template
         
        -- The runProofBySubArgM wrapper requires the 'do' block to return the 'extraData'
        -- that the caller of builderInstantiateM will receive.
        return (built_obj, instantiated_source_set, instantiated_p_template)


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
powerSetInstantiateM :: HelperConstraints sE s eL o tType m r t =>
    t -> -- ^ The object 'x' for which to prove its power set is a set.
    ProofGenTStd tType r s o m (s, [Int], t)
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

data MetaRuleError s where
   MetaRuleErrNotClosed :: s -> MetaRuleError s
   MetaRuleErrFreeVarsQuantCountMismatch :: MetaRuleError s

   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)


