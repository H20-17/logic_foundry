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
    builderXM,
    specificationMNew,
    aX, eX, hX, eXBang, multiAx, multiAXM, multiEXM, eXM, aXM, hXM,
    lambdaSpec,
    theoremSchemaMT


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
   MonadSent,
   aX, eX, hX, eXBang, multiAx,
   runProofByUGM)
import qualified RuleSets.PredLogic.Core as PREDL
import qualified RuleSets.PredLogic.Helpers as PREDL
import GHC.Num (integerMul)
import RuleSets.ZFC.Core
import RuleSets.BaseLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PredLogic.Helpers hiding
     (MetaRuleError(..),
     runProofByUGM,
     multiUGM, multiAXM, multiEXM, eXM, aXM, hXM)
import RuleSets.PropLogic.Helpers hiding
     (MetaRuleError(..))

import IndexTracker


standardRuleM :: HelperConstraints sE s eL m r t
       => r -> ProofGenTStd () r s Text () m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex



specificationM :: HelperConstraints sE s eL m r t
       => [Int] -> Int -> t -> s -> ProofGenTStd () r s Text ()m (s,[Int])
specificationM outerIdxs idx t s = standardRuleM (specification outerIdxs idx t s)


specificationMNew :: HelperConstraints sE s eL m r t
       => Int -> ([t] -> t) -> ([t] -> t -> s) -> ProofGenTStd () r s Text () m (s,[Int])
specificationMNew context_var_count t p_pred = do
    outerIdxs <- newIndices context_var_count
    unless (context_var_count >= 0) (error "specificationMNew: context_var_count must be nonnegative")
    let context_vars = Prelude.map x outerIdxs
    -- Add a new index for the specification variable
    let t_template = t context_vars
    
    spec_var_idx <- newIndex
    let spec_var = x spec_var_idx
    let p_template = p_pred context_vars spec_var
    result <- standardRuleM (specification outerIdxs spec_var_idx t_template p_template)
    dropIndices 1
    dropIndices context_var_count
    return result






replacementM :: HelperConstraints sE s eL m r t
       => [Int] -> Int -> Int -> t -> s -> ProofGenTStd () r s Text () m (s,[Int])
replacementM outerIdxs idx1 idx2 t s = standardRuleM (replacement outerIdxs idx1 idx2 t s)


integerMembershipM, integerNegationM :: HelperConstraints sE s eL m r t
       => Int -> ProofGenTStd () r s Text ()m (s,[Int])
integerMembershipM i = standardRuleM (integerMembership i)
integerNegationM i = standardRuleM (integerNegation i)

integerAdditionM, integerMultiplicationM, integerCompareM, integerInequalityM
 :: HelperConstraints sE s eL m r t
       => Int -> Int -> ProofGenTStd () r s Text () m (s,[Int])
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
       => ProofGenTStd () r s Text () m (s,[Int])
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
    ProofGenTStd () r s Text ()m (s, [Int], t)
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
                 =>  ProofGenTStd () r s Text () m x
                            -> ProofGenTStd () r s Text () m (s, [Int],x)
runProofByUGM = PREDL.runProofByUGM ()

multiUGM :: HelperConstraints sE s eL m r t =>
    Int ->                             -- ^ Number of UG's
    ProofGenTStd () r s Text () m x ->       -- ^ The core program. Its monadic return 'x' is discarded.
                                           --   It must set 'Last s' with the prop to be generalized.
    ProofGenTStd () r s Text () m (s, [Int],x)  -- ^ Returns (final_generalized_prop, its_index).
multiUGM n = PREDL.multiUGM (replicate n ()) 


-- | Gives us properties of a builder set, as well as the builder set object,
-- | after builderInstantiateM has been called
-- | Reproduces some of the work of builderInstantiateM but allows
-- | us to pass less information to functions as a consequence.
builderXM ::  MonadSent s t sE m => 
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


aX :: LogicSent s t => Int -> s -> s
aX idx s = PREDL.aX () idx s

eX :: LogicSent s t => Int -> s -> s
eX idx s = PREDL.eX () idx s

hX :: LogicSent s t => Int -> s -> t
hX idx s = PREDL.hX () idx s

eXBang :: LogicSent s t => Int -> s -> s
eXBang idx s = PREDL.eXBang () idx s

multiAx :: LogicSent s t => [Int] -> s -> s
multiAx idxs s = PREDL.multiAx (Prelude.map ((),) idxs) s


multiAXM :: MonadSent s t sE m => Int -> m s -> m s
multiAXM quantDepth inner = PREDL.multiAXM (replicate quantDepth ()) inner

multiEXM :: MonadSent s t sE m => Int -> m s -> m s
multiEXM quantDepth inner = PREDL.multiEXM (replicate quantDepth ()) inner


eXM :: MonadSent s t sE m => m s -> m s
eXM inner = PREDL.eXM () inner

aXM :: MonadSent s t sE m => m s -> m s
aXM inner = PREDL.aXM () inner


hXM :: MonadSent s t sE m => m s -> m t
hXM inner = PREDL.hXM () inner


lambdaSpec :: SentConstraints s t sE =>
    [Int] -> Int -> t -> s -> ([t]->t,[t] -> t -> s)
lambdaSpec contextIdxs specIdx source_template p_template =
    let 
        source_template_f = lambdaTermMulti contextIdxs source_template
        pred contextObjs specObj = lambdaSentMulti (specIdx:contextIdxs) p_template (specObj : contextObjs)

    in
        (source_template_f, pred)


-- | Worker employed by builderTheorem
specAxInstanceWorker :: (MonadSent s t sE m)  =>
    Int ->    -- param_n: The number of outer paramaters
    ([t] -> t) ->  -- t: The set, expressed a a function on the paramaters
    ([t] -> t -> s) -> -- p_pred

    m s -- the theorem
specAxInstanceWorker param_n t p_pred = do
    multiAXM param_n $ do
        paramVars <- getXVars param_n
        -- let paramVars = reverse paramVarsRev
        let t_tmplt = t paramVars
        let p_tmplt_pred = p_pred paramVars
        eXM $ do
            builderSet <- getXVar

            builder_props <- aXM $ do
                specVar <- getXVar
                return $ specVar `memberOf` builderSet
                          .<->. (p_tmplt_pred specVar .&&. (specVar `memberOf` t_tmplt))
            return $ isSet builderSet .&&. builder_props

specAxInstance :: SentConstraints s t sE =>
    Int ->    -- param_n: The number of outer paramaters
    ([t] -> t) ->  -- t: The set, expressed a a function on the paramaters
    ([t] -> t -> s) -> -- p
    s -- the theorem
specAxInstance param_n t p =
    runIndexTracker [] (specAxInstanceWorker param_n t p)




theoremSchemaMT :: HelperConstraints sE s eL m r t =>
    [s] -> ProofGenTStd () r s Text () m x -> [Text] -> 
             TheoremSchemaMT () r s Text () m x
theoremSchemaMT lemmas proof consts =
    let 
        constDict = Prelude.map (,()) consts
    in
        TheoremSchemaMT {
              constDictM = constDict
            , lemmasM = lemmas
            , proofM = proof
            , protectedXVars = []
            , contextVarTypes = []
        }

data MetaRuleError s where
   MetaRuleErrNotClosed :: s -> MetaRuleError s
   MetaRuleErrFreeVarsQuantCountMismatch :: MetaRuleError s

   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)


