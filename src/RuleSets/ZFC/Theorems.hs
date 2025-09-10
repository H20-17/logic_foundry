{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
module RuleSets.ZFC.Theorems
(
    unionEquivTheorem,
    binaryUnionExistsTheorem,
    binaryUnionExistsSchema,
    binaryIntersectionExistsTheorem,
    binaryUnionInstantiateM,
    proveUnionIsSetM,
    unionWithEmptySetSchema,
    unionWithEmptySetTheorem,
    specRedundancyTheorem,
    builderSubsetTheorem,
    builderSubsetTheoremSchema,
    specRedundancySchema,
    binaryIntersectionExistsSchema,
    binaryIntersectionInstantiateM,
    disjointSubsetIsEmptyTheorem,
    disjointSubsetIsEmptySchema,
    specAntiRedundancyTheorem,
    specAntiRedundancySchema,
    partitionEquivTheorem,
    builderSrcPartitionTheorem,
    builderSrcPartitionSchema,
    pairInUniverseTheorem,
    crossProductDefEquivTheorem,
    crossProductDefEquivSchema,
    crossProductExistsTheorem,
    crossProductExistsSchema,
    crossProductInstantiateM,
    strongInductionTheorem,
    strongInductionTheoremMSchema

) where


import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless,when )
import Data.Set (Set, fromList, toList)
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
   HelperConstraints(..))
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
   HelperConstraints(..))
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
   SentConstraints(..))
import qualified RuleSets.PredLogic.Core as PREDL
import RuleSets.ZFC.Core
import RuleSets.BaseLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PredLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PropLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.ZFC.Helpers hiding
     (MetaRuleError(..))
import Text.XHtml (target)
import Control.Exception (throw)
import Data.Type.Equality (outer)
import IndexTracker 



----begin binary union section------

-- | This is the lemma
-- | ∀A ∀B ( (isSet A ∧ isSet B) → ( (∃U (isSet U ∧ ∀x(x ∈ U ↔ ∃Y(Y ∈ {A,B} ∧ x ∈ Y)))) 
-- |    ↔ (∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∨ x ∈ B)))) ) )
unionEquivTheorem :: SentConstraints s t => s
unionEquivTheorem =
    let
        tmpl_A_idx = 0; tmpl_B_idx = 1; tmpl_S_idx = 2; tmpl_U_idx = 2; tmpl_Y_idx = 3; tmpl_x_idx = 4
                      
        -- Construct the two existential statements using these Int indices.
        prop_from_union_axiom = eX tmpl_U_idx (isSet (x tmpl_U_idx) .&&.
                                          aX tmpl_x_idx ((x tmpl_x_idx `memberOf` x tmpl_U_idx) .<->.
                                              eX tmpl_Y_idx ((x tmpl_Y_idx `memberOf` roster [x tmpl_A_idx, x tmpl_B_idx]) .&&. (x tmpl_x_idx `memberOf` x tmpl_Y_idx))))
        canonical_body = (x tmpl_x_idx `memberOf` x tmpl_A_idx) .||. (x tmpl_x_idx `memberOf` x tmpl_B_idx)
        canonical_prop = eX tmpl_S_idx (isSet (x tmpl_S_idx) .&&.
                                          aX tmpl_x_idx ((x tmpl_x_idx `memberOf` x tmpl_S_idx) .<->. canonical_body))
            
        thm_antecedent = isSet (x tmpl_A_idx) .&&. isSet (x tmpl_B_idx)
    in    
        multiAx [tmpl_A_idx, tmpl_B_idx] (thm_antecedent .->. (prop_from_union_axiom .<->. canonical_prop))



-- | Constructs the PropDeBr term for the closed theorem of binary union existence.
-- | The theorem is: ∀A ∀B ((isSet A ∧ isSet B) → ∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∨ x ∈ B))))
binaryUnionExistsTheorem :: SentConstraints s t  => s
binaryUnionExistsTheorem =
    let
        -- Define the integer indices for the template variables (X k).
        -- These will be bound by the quantifiers.
        a_idx = 0 -- Represents set A
        b_idx = 1 -- Represents set B
        s_idx = 2 -- Represents the union set S
        x_idx = 3 -- Represents an element x

        -- Construct the inner part of the formula: x ∈ S ↔ (x ∈ A ∨ x ∈ B)
        x_in_S = x x_idx `memberOf` x s_idx
        x_in_A = x x_idx `memberOf` x a_idx
        x_in_B = x x_idx `memberOf` x b_idx
        x_in_A_or_B = x_in_A .||. x_in_B
        biconditional = x_in_S .<->. x_in_A_or_B

        -- Quantify over x: ∀x(x ∈ S ↔ (x ∈ A ∨ x ∈ B))
        forall_x_bicond = aX x_idx biconditional

        -- Construct the property of the union set S: isSet(S) ∧ ∀x(...)
        isSet_S = isSet (x s_idx)
        property_of_S = isSet_S .&&. forall_x_bicond

        -- Quantify over S: ∃S (isSet(S) ∧ ∀x(...))
        exists_S = eX s_idx property_of_S

        -- Construct the antecedent of the main implication: isSet(A) ∧ isSet(B)
        isSet_A = isSet (x a_idx)
        isSet_B = isSet (x b_idx)
        antecedent = isSet_A .&&. isSet_B

        -- Construct the main implication
        implication = antecedent .->. exists_S

    in
        -- Universally quantify over A and B to create the final closed theorem.
        -- multiAx [0, 1] is equivalent to aX 0 (aX 1 (...))
        multiAx [a_idx, b_idx] implication




-- | Proves the theorem defined in 'binaryUnionExistsTheorem'
-- |
-- | Proof Strategy:
-- | 1. Use Universal Generalization for A and B.
-- | 2. Assume the antecedent: isSet(A) ∧ isSet(B).
-- | 3. Use the Axiom of Pairing to prove the existence of the pair set {A, B}.
-- | 4. Use `eiHilbertM` to instantiate this pair set, getting an object `pairSetAB` and a proof of `isSet(pairSetAB)`.
-- | 5. Use the Axiom of Union, instantiating it with `pairSetAB`.
-- | 6. Use Modus Ponens with `isSet(pairSetAB)` to prove `∃U (isSet U ∧ ∀x(x∈U ↔ ∃Y(Y∈{A,B} ∧ x∈Y)))`.
-- |    This U is the union A ∪ B.
-- | 7. The property `∀x(x∈U ↔ ∃Y(Y∈{A,B} ∧ x∈Y))` is logically equivalent to the canonical
-- |    property `∀x(x∈U ↔ (x∈A ∨ x∈B))`. We assert this known equivalence using `fakePropM`.
-- | 8. This results in the desired existential statement for the binary union.
-- | Note that 'union_equiv_theorem' is a required lemma.

proveBinaryUnionExistsM :: HelperConstraints sE s eL m r t =>
    ProofGenTStd () r s Text m ()
proveBinaryUnionExistsM = do
    -- Universally generalize over A and B.
    multiUGM (replicate 2 ()) $ do
        -- Inside the UG, we have free variables (V_i) corresponding to A and B.
        -- We will use these variables to represent the sets A and B.
        
        -- Get the top free variables for A and B.
        v_Av_B <- getTopFreeVars 2
        let setA = head v_Av_B
        let setB = v_Av_B!!1
        -- Prove the implication by assuming the antecedent.
        runProofByAsmM (isSet setA .&&. isSet setB) $ do
            -- Now, isSet(A) and isSet(B) are proven assumptions in this context.

            -- Step 1: Use the Axiom of Pairing to prove ∃P. isSet(P) ∧ P = {A,B}.
            (pairAxiom,_) <- pairingAxiomM
            (pairAxiom_inst,_) <- multiUIM pairAxiom [setA, setB]


            -- Step 2: Instantiate this pair set with a Hilbert term `pairSetAB`.
            -- `pair_prop` is isSet({A,B}) ∧ ∀z(z∈{A,B} ↔ z=A ∨ z=B).
            (pair_prop, _, pairSetAB) <- eiHilbertM pairAxiom_inst
            (isSet_pair_proven, _) <- simpLM pair_prop

            -- Step 3: Use the Axiom of Union on the proven set `pairSetAB`.
            (unionAxiom,_) <- unionAxiomM
            (unionAxiom_inst, _) <- uiM pairSetAB unionAxiom

            -- Step 4: Use Modus Ponens with `isSet(pairSetAB)` to derive the existence of the union.
            -- `exists_U` is ∃U(isSet U ∧ ∀x(x∈U ↔ ∃Y(Y∈{A,B} ∧ x∈Y))).
            (exists_U, _) <- mpM unionAxiom_inst
            -- Step 5: Assert a general, CLOSED theorem about the equivalence of the two forms of union.
            -- Thm: ∀A,B. (isSet A ∧ isSet B) → ( (∃U. from Axiom of Union on {A,B}) ↔ (∃S. with canonical binary union prop) )
            -- We build the two existential statements as templates first.

            let tmpl_A_idx = 0; tmpl_B_idx = 1; tmpl_S_idx = 2; tmpl_U_idx = 2; tmpl_Y_idx = 3; tmpl_x_idx = 4
                      

            -- Step 6: Instantiate the theorem with our specific sets A and B.
            (instantiated_thm, _) <- multiUIM unionEquivTheorem [setA, setB]

            -- Step 7: Use Modus Ponens with our assumption `isSet A ∧ isSet B`.
            (proven_biconditional, _) <- mpM instantiated_thm

            -- Step 8: From the equivalence and the proven `exists_U`, derive the target existential.
            (forward_imp, _) <- bicondElimLM proven_biconditional

            mpM forward_imp -- This proves the target_existential

    return ()


-- | The schema that houses 'proveBinaryUnionExistsM'.
-- | The schema stipulates that:
-- | "union_equiv_theorem" is a required lemma.
binaryUnionExistsSchema ::  HelperConstraints sE s eL m r t => 
     TheoremSchemaMT () r s Text m ()
binaryUnionExistsSchema =       
    TheoremSchemaMT [] [unionEquivTheorem] proveBinaryUnionExistsM 



-- | Helper to instantiate the binary union theorem and return the union set.
-- | For this helper to work, the theorem defined by 'binaryUnionExistsTheorem' must be proven
-- | beforehand, which is likely done in the global context.
binaryUnionInstantiateM ::  HelperConstraints sE s eL m r t =>
    t -> t -> ProofGenTStd () r s Text m (s, [Int], t)
binaryUnionInstantiateM setA setB = do
    runProofBySubArgM $ do
        -- This helper relies on isSet(setA) and isSet(setB) being proven in the outer context.

        -- Step 1: Instantiate the 'binaryUnionExistsTheorem' theorem with the specific sets A and B.
        (instantiated_thm, _) <- multiUIM binaryUnionExistsTheorem [setA, setB]
        -- The result is the proven proposition: (isSet A ∧ isSet B) → ∃S(...)

        -- Step 3: Prove the antecedent of the instantiated theorem.
        -- We assume isSet A and isSet B are proven in the parent context.
        (isSet_A_proven, _) <- repM (isSet setA)
        (isSet_B_proven, _) <- repM (isSet setB)
        (antecedent_proven, _) <- adjM isSet_A_proven isSet_B_proven

        -- Step 4: Use Modus Ponens to derive the existential statement.
        (exists_S_proven, _) <- mpM instantiated_thm

        -- Step 5: Use Existential Instantiation (eiHilbertM) to get the property of the union set.
        -- The Hilbert term created here, `unionObj`, is definitionally A U B.
        (prop_of_union, _, unionObj) <- eiHilbertM exists_S_proven
        -- prop_of_union is: isSet(unionObj) ∧ ∀x(x∈unionObj ↔ (x∈A ∨ x∈B))
        return unionObj


-- BEGIN BINARY INTERSECTION EXISTS SECTION

-- | Constructs the PropDeBr term for the closed theorem of binary intersection existence.
-- | The theorem is: ∀A ∀B ((isSet A ∧ isSet B) → ∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∧ x ∈ B))))
binaryIntersectionExistsTheorem :: SentConstraints s t => s
binaryIntersectionExistsTheorem =
    let
        -- Define integer indices for the template variables (X k).
        a_idx = 0 -- Represents set A
        b_idx = 1 -- Represents set B
        s_idx = 2 -- Represents the intersection set S
        x_idx = 3 -- Represents an element x

        -- Construct the inner part of the formula: x ∈ S ↔ (x ∈ A ∧ x ∈ B)
        x_in_S = x x_idx `memberOf` x s_idx
        x_in_A = x x_idx `memberOf` x a_idx
        x_in_B = x x_idx `memberOf` x b_idx
        x_in_A_and_B = x_in_A .&&. x_in_B
        biconditional = x_in_S .<->. x_in_A_and_B

        -- Quantify over x: ∀x(x ∈ S ↔ (x ∈ A ∧ x ∈ B))
        forall_x_bicond = aX x_idx biconditional

        -- Construct the property of the set S: isSet(S) ∧ ∀x(...)
        isSet_S = isSet (x s_idx)
        property_of_S = isSet_S .&&. forall_x_bicond

        -- Quantify over S: ∃S (isSet(S) ∧ ∀x(...))
        exists_S = eX s_idx property_of_S

        -- Construct the antecedent of the main implication: isSet(A) ∧ isSet(B)
        isSet_A = isSet (x a_idx)
        isSet_B = isSet (x b_idx)
        antecedent = isSet_A .&&. isSet_B

        -- Construct the main implication
        implication = antecedent .->. exists_S

    in
        -- Universally quantify over A and B to create the final closed theorem.
        multiAx [a_idx, b_idx] implication



-- | Proves the theorem defined in 'binaryIntersectionExistsTheorem'.
-- |
-- | The proof strategy is to use the Axiom of Specification. For any two sets A and B,
-- | we can specify a new set S from the source set A using the predicate "is an element of B".
-- | The resulting set S = {x ∈ A | x ∈ B} is precisely the intersection A ∩ B.
-- | The `builderInstantiateM` helper encapsulates this application of the axiom.
proveBinaryIntersectionExistsM :: HelperConstraints sE s eL m r t =>
    ProofGenTStd () r s Text m ()
proveBinaryIntersectionExistsM = do
    -- The theorem is universally quantified over two sets, A and B.
    multiUGM [(), ()] $ do
        -- Inside the UG, free variables v_A and v_B are introduced.
        v_Av_B <- getTopFreeVars 2
        let setA = head v_Av_B
        let setB = v_Av_B !! 1

        -- Prove the main implication by assuming the antecedent: isSet(A) ∧ isSet(B).
        runProofByAsmM (isSet setA .&&. isSet setB) $ do
            -- Within this subproof, isSet(A) and isSet(B) are proven assumptions.

            -- Step 1: Define the templates for the Axiom of Specification.
            -- The source set T will be A. The predicate P(x) will be (x ∈ B).
            -- The parameters to our templates are A and B.
            let a_param_idx = 0
            let b_param_idx = 1
            let spec_var_idx = 2 -- The 'x' in {x ∈ T | P(x)}

            let source_set_template = x a_param_idx
            let p_template = x spec_var_idx `memberOf` x b_param_idx

            -- Step 2: Use builderInstantiateM to apply the Axiom of Specification.
            -- It will construct the set {x ∈ A | x ∈ B} and prove its defining property.
            -- The instantiation terms [setA, setB] correspond to the template params [X 0, X 1].
            (defining_prop, _, (intersectionObj,_,_)) <- builderInstantiateM
                [setA, setB]                         -- instantiationTerms
                [a_param_idx, b_param_idx]           -- outerTemplateIdxs
                spec_var_idx                         -- spec_var_X_idx
                source_set_template                  -- source_set_template (A)
                p_template                           -- p_template (x ∈ B)

            -- 'defining_prop' is: isSet(B) ∧ ∀x(x∈B ↔ (x∈A ∧ x∈B)), where B is the new intersectionObj.
            -- This is exactly the property required for the existential statement.

            -- Step 3: Construct the target existential statement from the theorem definition.
            let target_existential = eX 0 (isSet (x 0) .&&. aX 1 (x 1 `memberOf` x 0 .<->. 
                                          (x 1 `memberOf` setB .&&. x 1 `memberOf` setA)))
            -- target_existential is the statement ∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∧ x ∈ B))))


            -- Step 4: Apply Existential Generalization.
            -- This works because 'defining_prop' is the instantiated version of the
            -- property inside the target existential statement.
            egM intersectionObj target_existential
    return ()

-- | The schema that houses 'proveBinaryIntersectionExistsM'.
-- | This theorem has no other high-level theorems as lemmas; it is proven
-- | directly from the Axiom of Specification (via the builderInstantiateM helper).
binaryIntersectionExistsSchema :: HelperConstraints sE s eL m r t =>
     TheoremSchemaMT () r s Text m ()
binaryIntersectionExistsSchema =
    TheoremSchemaMT [] [] proveBinaryIntersectionExistsM



-- | Helper to instantiate the binary intersection theorem and return the intersection set object.
-- | For this helper to work, the theorem defined by 'binaryIntersectionExistsTheorem' must be proven
-- | beforehand (e.g., in the global context by running its schema).
binaryIntersectionInstantiateM ::  HelperConstraints sE s eL m r t =>
    t -> t -> ProofGenTStd () r s Text m (s, [Int], t)
binaryIntersectionInstantiateM setA setB = do
    runProofBySubArgM $ do
        -- This helper relies on isSet(setA) and isSet(setB) being proven in the outer context.

        -- Step 1: Instantiate the 'binaryIntersectionExistsTheorem' with the specific sets A and B.
        (instantiated_thm, _) <- multiUIM binaryIntersectionExistsTheorem [setA, setB]

        -- Step 2: Prove the antecedent of the instantiated theorem.
        (isSet_A_proven, _) <- repM (isSet setA)
        (isSet_B_proven, _) <- repM (isSet setB)
        (antecedent_proven, _) <- adjM isSet_A_proven isSet_B_proven

        -- Step 3: Use Modus Ponens to derive the existential statement.
        (exists_S_proven, _) <- mpM instantiated_thm

        -- Step 4: Use Existential Instantiation (eiHilbertM) to get the property of the intersection set.
        -- The Hilbert term created here, `intersectionObj`, is definitionally A ∩ B.
        (prop_of_intersection, _, intersectionObj) <- eiHilbertM exists_S_proven

        return intersectionObj





-- END BINARY INTERSECTION EXISTS SECTION



-- | Helper to prove that if A and B are sets,
-- | then their union (A ∪ B) is also a set.
-- | This version takes advantage of the `binaryUnionInstantiateM` helper.
-- |
-- | Note: This helper requires that `isSet setA` and `isSet setB` have already been
-- | proven in the current proof context.
-- | It also relies on the theorem `binaryUnionExistsTheorem` being proven beforehand.
proveUnionIsSetM :: HelperConstraints sE s eL m r t =>
    t -> t -> ProofGenTStd () r s Text m (s, [Int])
proveUnionIsSetM setA setB = do
    (resultProp,idx,_) <- runProofBySubArgM $ do
        (prop_of_union, _, unionObj) <- binaryUnionInstantiateM setA setB
        (isSet_union_proven, _) <- simpLM prop_of_union
        return ()
    return (resultProp,idx)


------end binary union section------------

-----begin union with emptyset section


-- | Constructs the PropDeBr term for the theorem stating that for any set x,
-- | the union of x with the empty set is x itself.
-- |
-- | Theorem: ∀x (isSet x → (x ∪ ∅ = x))
unionWithEmptySetTheorem :: SentConstraints s t => s
unionWithEmptySetTheorem =
    let
        x_idx = 0
        setX = x x_idx
        
        -- The equality: x U emptySet == x
        equality = (setX .\/. emptySet) .==. setX
        
        -- The antecedent: isSet x
        antecedent = isSet setX
        
        -- The implication
        implication = antecedent .->. equality
    in
        -- Universally quantify over x
        aX x_idx implication



-- | Proves the theorem defined by 'unionWithEmptySetTheorem'.
-- |
-- | This proof relies on the Axiom of Extensionality and the
-- | 'binaryUnionExists' theorem. To prove A = B, we must show:
-- |   isSet(A) ∧ isSet(B) ∧ ∀y(y ∈ A ↔ y ∈ B)
proveUnionWithEmptySetM :: HelperConstraints sE s eL m r t =>
    ProofGenTStd () r s Text m ()
proveUnionWithEmptySetM = do
    -- Prove the theorem: ∀x (isSet x → x ∪ ∅ = x)
    runProofByUGM () $ do
        -- Inside UG, a free variable 'v' is introduced for 'x'.
        v <- getTopFreeVar
        
        -- Prove the implication by assuming the antecedent.
        runProofByAsmM (isSet v) $ do
            -- Now, `isSet v` is a proven assumption.

            -- Step 1: Define the objects we are working with.
            let unionObj = v .\/. emptySet

            -- Step 2: Prove the necessary `isSet` properties for Extensionality.
            -- We already have `isSet v` by assumption.
            -- We need to prove `isSet (v ∪ ∅)`.

            -- (isSet_EmptySet_axiom, _) <- ZFC.emptySetAxiomM

            (forall_not_in_empty, _) <- emptySetAxiomM

            -- (isSet_EmptySet_proven, _) <- simpLM isSet_EmptySet_axiom
            
            (isSet_EmptySet_proven, _) <- emptySetNotIntM

            -- proveUnionIsSetM requires isSet v and isSet ∅ to be proven.
            (isSet_unionObj_proven, _) <- proveUnionIsSetM v emptySet

            -- Step 3: Prove ∀y (y ∈ v ↔ y ∈ (v ∪ ∅))
            (forall_bicond, _) <- runProofByUGM () $ do
                y <- getTopFreeVar

               -- Direction 1: y ∈ v → y ∈ (v ∪ ∅)
                (dir1, _) <- runProofByAsmM (y `memberOf` v) $ do
                    -- This is a simple Disjunction Introduction.
                    disjIntroLM (y `memberOf` v) (y `memberOf` emptySet)

                    -- Now, use the definition of union to get back to y ∈ (v ∪ ∅)
                    (def_prop_union, _, _) <- binaryUnionInstantiateM v emptySet
                    (forall_union_bicond, _) <- simpRM def_prop_union
                    (inst_union_bicond, _) <- uiM y forall_union_bicond
                    (imp_to_union, _) <- bicondElimRM inst_union_bicond
                    
                    -- Apply Modus Ponens to get the final conclusion of this subproof.
                    mpM imp_to_union
                    return ()

                -- To prove the biconditional, we prove each direction.
                -- Direction 2: y ∈ (v ∪ ∅) → y ∈ v
                (dir2, _) <- runProofByAsmM (y `memberOf` unionObj) $ do
                    -- Get the defining property of the union.
                    (def_prop_union, _, _) <- binaryUnionInstantiateM v emptySet
                    (forall_union_bicond, _) <- simpRM def_prop_union
                    (inst_union_bicond, _) <- uiM y forall_union_bicond
                    (imp_from_union, _) <- bicondElimLM inst_union_bicond
                    -- We have now proven: y ∈ (v ∪ ∅) → (y ∈ v ∨ y ∈ ∅)
                    (y_in_v_or_empty, _) <- mpM imp_from_union

                    -- We need a proof of ¬(y ∈ ∅) to use Disjunctive Syllogism.

                    (not_y_in_empty, _) <- uiM y forall_not_in_empty

                    -- Use the Disjunctive Syllogism argument to prove y_in_v.

                    disjunctiveSyllogismM y_in_v_or_empty

                    -- y_in_v should now be proved
   

                -- Combine the two directions.
                bicondIntroM dir1 dir2

            -- Step 4: Apply the Axiom of Extensionality.
            (ext_axiom, _) <- extensionalityAxiomM
            (ext_inst, _) <- multiUIM ext_axiom [v, unionObj]
            (adj1,_) <- adjM isSet_unionObj_proven forall_bicond
            (full_antecedent,_) <- adjM (isSet v) adj1

            mpM ext_inst

    return ()



-- | The schema that houses the proof for 'unionWithEmptySetTheorem'.
-- | It declares its dependencies on other theorems.
unionWithEmptySetSchema :: HelperConstraints sE s eL m r t =>
     TheoremSchemaMT () r s Text m ()
unionWithEmptySetSchema =
    let
        -- The lemmas required for this proof.
        lemmas_needed = [
            binaryUnionExistsTheorem -- Needed by proveUnionIsSetM and binaryUnionInstantiateM
          ]
    in
        TheoremSchemaMT {
            lemmasM = lemmas_needed,
            proofM = proveUnionWithEmptySetM,
            constDictM = [] -- No specific object constants needed
        }

--------END UNION WITH EMPTY SET

--------DISJOINT SUBSETISEMPTY THEOREM

disjointSubsetIsEmptyTheorem :: SentConstraints s t => s
disjointSubsetIsEmptyTheorem = aX 0 (aX 1 (isSet (x 0) .&&. (x 0 ./\. x 1) .==. emptySet .&&. (x 1 `subset` x 0) .->. x 1 .==. emptySet))



-- | Proves the theorem defined by 'disjointSubsetIsEmptyTheorem'.
-- |
-- | The proof strategy is as follows:
-- | 1. Assume the antecedent: isSet(a), a ∩ b = ∅, and b ⊆ a.
-- | 2. To prove b = ∅, we must show they are extensionally equal: ∀x(x ∈ b ↔ x ∈ ∅).
-- | 3. This is equivalent to showing ∀x(¬(x ∈ b)), since nothing is in ∅.
-- | 4. We prove ∀x(¬(x ∈ b)) by contradiction. Assume ∃x(x ∈ b).
-- | 5. Let 'y' be such an element in 'b'.
-- | 6. Since b ⊆ a, it follows that y ∈ a.
-- | 7. Since y ∈ a and y ∈ b, it follows that y ∈ (a ∩ b).
-- | 8. But this contradicts the premise that a ∩ b = ∅.
-- | 9. Therefore, our assumption must be false, so ¬∃x(x ∈ b), which is ∀x(¬(x ∈ b)).
-- | 10. With ∀x(x ∈ b ↔ x ∈ ∅) proven, the Axiom of Extensionality gives b = ∅.
proveDisjointSubsetIsEmptyM :: HelperConstraints sE s eL m r t =>
    ProofGenTStd () r s Text m ()
proveDisjointSubsetIsEmptyM = do
    -- Prove: ∀a ∀b (isSet(a) ∧ a ∩ b = ∅ ∧ b ⊆ a → b=∅)
    multiUGM [(), ()] $ do
        -- Inside UG, free variables for a and b are introduced (v_a, v_b).
        v_Av_B <- getTopFreeVars 2
        let v_a = head v_Av_B
        let v_b = v_Av_B!!1


        -- Prove the main implication by assuming the antecedent.
        let antecedent = isSet v_a .&&. ((v_a ./\. v_b) .==. emptySet) .&&. (v_b `subset` v_a)
        runProofByAsmM antecedent $ do
            -- Step 1: Deconstruct the antecedent assumption.
            (isSet_a_proven, _) <- simpLM antecedent
            (rest1,_) <- simpRM antecedent
            (intersection_is_empty, subset_b_a) <- simpLM rest1
            (subset_b_a,_) <- simpRM rest1 

            -- Step 2: Prove ∀x(¬(x ∈ v_b)) by contradiction.
            (forall_not_in_b, _) <- runProofByUGM () $ do
                x_var <- getTopFreeVar
                (x_in_b_implies_false, _) <- runProofByAsmM (x_var `memberOf` v_b) $ do
                    -- From b ⊆ a and x ∈ b, we get x ∈ a.
                    (isSet_b, _) <- simpLM subset_b_a
                    (forall_imp, _) <- simpRM subset_b_a
                    (x_in_b_implies_x_in_a, _) <- uiM x_var forall_imp
                    (x_in_a, _) <- mpM x_in_b_implies_x_in_a

                    -- From x ∈ a and x ∈ b, we get x ∈ (a ∩ b).
                    (def_prop_inter, _, _) <- binaryIntersectionInstantiateM v_a v_b
                    (forall_inter_bicond, _) <- simpRM def_prop_inter
                    (inst_inter_bicond, _) <- uiM x_var forall_inter_bicond
                    (imp_to_inter, _) <- bicondElimRM inst_inter_bicond
                    (x_in_a_and_b, _) <- adjM x_in_a (x_var `memberOf` v_b)
                    (x_in_intersection, _) <- mpM imp_to_inter

                    -- From a ∩ b = ∅ and x ∈ (a ∩ b), we get x ∈ ∅.
                    let eqSubstTmplt = x_var `memberOf` x 0
                    --(x_in_empty, _) <- eqSubstM 1 (X 0 :==: X 1 :->: ((x `In` X 0) :->: (x `In` X 1)))
                    --                         [v_a ./\. v_b, EmptySet]
                    (x_in_empty, _) <- eqSubstM 0 eqSubstTmplt intersection_is_empty


                    -- But we know from the empty set axiom that ¬(x ∈ ∅).
                    (forall_not_in_empty, _) <- emptySetAxiomM
                    (not_x_in_empty, _) <- uiM x_var forall_not_in_empty

                    -- This is a contradiction.
                    contraFM x_in_empty
                
                -- From (x ∈ b → False), we derive ¬(x ∈ b).
                absurdM x_in_b_implies_false

            -- Step 3: Use the result from Step 2 to prove ∀x(x ∈ b ↔ x ∈ ∅).
            (forall_bicond, _) <- runProofByUGM () $ do
                x <- getTopFreeVar
                (not_in_b, _) <- uiM x forall_not_in_b
                (forall_not_in_empty, _) <- emptySetAxiomM
                (not_in_empty, _) <- uiM x forall_not_in_empty

                (dir1, _) <- runProofByAsmM (neg (x `memberOf` v_b))
                                            (repM not_in_empty)

                (dir2, _) <- runProofByAsmM (neg (x `memberOf` emptySet))
                                   (repM not_in_b)
                (bicond_of_negs,_) <- bicondIntroM dir1 dir2

                -- Use our tautology helper to get the positive biconditional.
                negBicondToPosBicondM bicond_of_negs

            -- Step 4: Apply the Axiom of Extensionality to prove b = ∅.
            (isSet_b, _) <- simpLM subset_b_a
            (isSet_empty, _) <- emptySetNotIntM
            (ext_axiom, _) <- extensionalityAxiomM
            (ext_inst, _) <- multiUIM ext_axiom [v_b, emptySet]
            
            (adj1, _) <- adjM isSet_empty forall_bicond
            (full_antecedent, _) <- adjM isSet_b adj1
            
            mpM ext_inst
            return ()
    return ()


-- | The schema that houses the proof for 'disjointSubsetIsEmptyTheorem'.
-- | It declares its dependencies on other theorems.
disjointSubsetIsEmptySchema :: HelperConstraints sE s eL m r t =>
     TheoremSchemaMT () r s Text m ()
disjointSubsetIsEmptySchema =
    let
        -- The lemmas required for this proof.
        lemmas_needed = [
            binaryIntersectionExistsTheorem
          ]
    in
        TheoremSchemaMT {
            lemmasM = lemmas_needed,
            proofM = proveDisjointSubsetIsEmptyM,
            constDictM = [] -- No specific object constants needed
        }

--------END DISJOINT SUBSET IS EMPTY THEOREM

---- BEGIN BUILDER SUBSET THEOREM ---
-- | Constructs the PropDeBr term for the general theorem that any set constructed
-- | via specification is a subset of its domain, universally quantified over any parameters.
-- |
-- | The constructed theorem has the form:
-- |   ∀(params...) ( {x ∈ D(params) | P(x,params)} ⊆ D(params) )
-- |
-- | @param outerTemplateIdxs  The list of `Int` indices for the `X` variables in the templates
-- |                           that act as parameters to be universally quantified.
-- | @param spec_var_X_idx     The `Int` index for the `X` variable that is the variable of specification
-- |                           (the 'x' in {x ∈ T | P(x)}).
-- | @param source_set_template The source set `T`, which may contain `X k` parameters from `outerTemplateIdxs`.
-- | @param p_template         The predicate `P`, which uses `X spec_var_X_idx` for the specification
-- |                           variable and may contain `X k` parameters from `outerTemplateIdxs`.
builderSubsetTheorem :: SentConstraints s t => [Int] -> Int -> t -> s -> s
builderSubsetTheorem outerTemplateIdxs spec_var_X_idx source_set_template p_template =
    -- Step 1: Construct the builder object term from the templates.
    -- This represents {x ∈ D(params) | P(x,params)}.
    let builtObj = builderX spec_var_X_idx source_set_template p_template
    in
    -- Step 2: Construct the core proposition, which is the subset relation.
    -- This asserts that the built object is a subset of its source set template.
    let subset_prop = builtObj `subset` source_set_template
    in
    -- Step 3: Universally quantify over all parameters to create the final closed theorem.
    -- This binds all the X k variables from outerTemplateIdxs that appear in the templates.
    multiAx outerTemplateIdxs subset_prop



-- | Given the instantiated source set, 'dom', and 
-- | instantiated predicate 'p_template' returned from from `builderInstantiateM`, this function proves that
-- | { x ∈ dom | p_template(x)} is a subset of dom
-- | said set is a subset of its original domain (`domainSet`).
-- | It encapsulates the entire proof within a single sub-argument.
-- | When we say that p_template is instantiated, we mean that all of the template variables,
-- | *other than the its specification variable*, are assumed to have already been instantiated.
proveBuilderIsSubsetOfDomMFree :: HelperConstraints sE s eL m r t =>    
    Int -> -- spec_var_idx 
    t ->   -- sourceSet: The ObjDeBr for the set B, i.e., {x ∈ dom | P(x)}
    s -> -- p_tmplt
    ProofGenTStd () r s Text m (s,[Int],())
proveBuilderIsSubsetOfDomMFree spec_var_idx sourceSet p_tmplt =
    -- runProofBySubArgM will prove the last statement from its 'do' block (the subset proposition)
    -- and return (proven_subset_prop, index_of_this_subargument, ()).
    
    runProofBySubArgM $ do
        -- The final goal is to prove the proposition corresponding to 'builderSet `subset` domainSet'
        let (definingProperty,builderSet) = builderPropsFree spec_var_idx sourceSet p_tmplt
        
        -- let targetSubsetProp = builderSet `subset` domainSet


        -- Step 1: Deconstruct the given 'definingProperty' to get its two main parts.
        (isSet_B_proven, _) <- simpLM definingProperty         -- isSet(B) is now proven
        (forall_bicond, _) <- simpRM definingProperty       -- ∀x(x∈B ↔ P(x)∧x∈dom) is now proven

        -- Step 2: Prove the universal implication part of the subset definition: ∀x(x ∈ B → x ∈ dom).
        -- This is done using Universal Generalization (UG).
        -- The '()' for runProofByUGM's type argument assumes the element type is not tracked
        -- in the context, which is common in your ZFC setup.
        (forall_implication, _) <- runProofByUGM () $ do
            -- Inside the UG subproof, a new free variable 'v' is introduced into the context.
            -- getTopFreeVar retrieves this variable.
            v <- getTopFreeVar -- Needs to be implemented, e.g., 'V . length . freeVarTypeStack <$> ask'

            -- We now need to prove 'v ∈ B → v ∈ dom'. This is done with an assumption subproof.
            runProofByAsmM (v `memberOf` builderSet) $ do
                -- Inside this assumption, 'v In builderSet' is proven.

                -- a. Instantiate the universally quantified biconditional with 'v'.
                (instantiated_bicond, _) <- uiM v forall_bicond

                -- b. From the proven biconditional 'v∈B ↔ (P(v)∧v∈dom)', get the forward implication.
                (forward_imp, _) <- bicondElimLM instantiated_bicond -- Proves (v∈B) → (P(v)∧v∈dom)

                -- c. Use Modus Ponens with our assumption 'v∈B' to get 'P(v) ∧ v∈dom'.
                (p_and_v_in_dom, _) <- mpM forward_imp

                -- d. From 'P(v) ∧ v∈dom', simplify to get 'v∈dom'.
                (v_in_dom, _) <- simpRM p_and_v_in_dom

                -- The subproof concludes with 'v_in_dom'.
                -- 'runProofByAsmM' will therefore prove '(v In builderSet) -> v_in_dom'.
                return ()

        -- After 'runProofByUGM', 'forall_implication' is the proven proposition ∀x(x ∈ B → x ∈ dom).

        -- Step 3: Adjoin 'isSet(B)' and '∀x(x ∈ B → x ∈ dom)' to form the final subset definition.
        (final_subset_prop, _) <- adjM isSet_B_proven forall_implication
        
        -- As a sanity check, ensure the proven proposition matches the definition of subset.
        --guard (final_subset_prop == targetSubsetProp)

        -- The last proven statement is 'final_subset_prop'. 'runProofBySubArgM' will pick this
        -- up as its consequent. The () here is the monadic return value 'x', which is discarded.
        return ()



-- | Proves the general theorem that any set constructed via specification is a subset of its domain,
-- | universally quantified over any parameters in the specification.
-- |
-- | This helper proves a closed theorem of the form:
-- |   ∀(params...) ( {x ∈ D(params) | P(x,params)} ⊆ D(params) )
-- |
-- | It achieves this by composing 'builderInstantiateM' (to construct the set and get its
-- | defining property) and 'proveBuilderIsSubsetOfDomMFree' (to prove the subset relation
-- | from that property), all within the scope of universal generalizations for the parameters.
-- |
-- | @param outerTemplateIdxs  The list of `Int` indices for the `X` variables in the templates
-- |                           that act as parameters to be universally quantified.
-- | @param spec_var_X_idx     The `Int` index for the `X` variable that is the variable of specification
-- |                           (the 'x' in {x ∈ T | P(x)}).
-- | @param source_set_template The source set `T`, which may contain `X k` parameters from `outerTemplateIdxs`.
-- | @param p_template         The predicate `P`, which uses `X spec_var_X_idx` for the specification
-- |                           variable and may contain `X k` parameters from `outerTemplateIdxs`.
proveBuilderSubsetTheoremM :: HelperConstraints sE s eL m r t =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    t ->  -- source_set_template
    s -> -- p_template
    ProofGenTStd () r s Text m ()
proveBuilderSubsetTheoremM outerTemplateIdxs spec_var_X_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters.
    -- The number of quantifiers is determined by the length of 'outerTemplateIdxs'.
    multiUGM (replicate (length outerTemplateIdxs) ()) $ do
        
        -- Step 1: Get the list of free variables. All will be active since
        -- the source_set_template and the p_template would be deemed insane
        -- in the context of testing a theorem, if they had any free variables
        -- of their own.

        freeVars <- getTopFreeVars (length outerTemplateIdxs)
        -- The order of the freeVars will effect the quantifier order.
        -- Perhaps this list should be reversed for esthetic reasons but in any case
        -- the sentences produced will be logically equivalent.


        -- Step 2: Get the defining property of this specific builtObj, as well as builtObj.
        -- We call builderInstantiateM, which handles the spec axiom, UI, and EI steps.
        -- It needs the original templates and the list of terms to instantiate with.
        (definingProperty, _, (builtObj, instantiated_source_set,instantiated_predicate)) <- builderInstantiateM freeVars outerTemplateIdxs spec_var_X_idx source_set_template p_template

        -- Step 3: Now call the helper that proves the subset relation from the defining property.
        -- The result of this call (the proven subset relation) will become the conclusion
        -- of the multiUGM block.
        (subset_prop, _, _) <- proveBuilderIsSubsetOfDomMFree spec_var_X_idx instantiated_source_set
                                                instantiated_predicate
        
        -- The last proven statement is now `builtObj ⊆ instantiated_source_set`.
        -- `multiUGM` will generalize this over all the parameter variables.
        return ()
    
    -- The outer `do` block implicitly returns (), as multiUGM does.
    -- The final universally quantified theorem is now the last proven statement.
    return ()

builderSubsetTheoremSchema :: HelperConstraints sE s eL m r t => 
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    t ->  -- source_set_template
    s -> -- p_template
    TheoremSchemaMT () r s Text m ()
builderSubsetTheoremSchema outerTemplateIdxs spec_var_X_idx source_set_template p_template =
    let
      source_set_tmplt_consts = extractConstsTerm source_set_template
      p_tmplt_consts = extractConstsSent p_template
      all_consts = source_set_tmplt_consts `Set.union` p_tmplt_consts
      typed_consts = Prelude.map (, ()) (Data.Set.toList all_consts)
    in   
      TheoremSchemaMT typed_consts [] (proveBuilderSubsetTheoremM outerTemplateIdxs spec_var_X_idx source_set_template p_template)

----- END BUILDER SUBSET THEOREM

----- BUILDER SRC PARTITION

-- | Constructs the PropDeBr term for the theorem stating that for any set S and predicate P,
-- | an element x is in S if and only if it's in the part of S satisfying P or the part not satisfying P.
-- |
-- | Theorem: ∀(params...)∀x ( x∈S(params) ↔ ( (x∈S(params) ∧ P(x,params)) ∨ (x∈S(params) ∧ ¬P(x,params)) ) )
partitionEquivTheorem :: SentConstraints s t => [Int] -> Int -> t -> s -> s
partitionEquivTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- The left-hand side of the biconditional: x ∈ S
        lhs = x spec_var_idx `memberOf` source_set_template

        -- The right-hand side of the biconditional: (x∈S ∧ P(x)) ∨ (x∈S ∧ ¬P(x))
        -- Note that p_template already contains X spec_var_idx for the variable x.
        x_in_S_and_P = p_template .&&. (x spec_var_idx `memberOf` source_set_template) 
        x_in_S_and_NotP = neg p_template .&&. (x spec_var_idx `memberOf` source_set_template) 
        rhs = x_in_S_and_P .||. x_in_S_and_NotP

        -- The core biconditional for a specific x and specific params
        biconditional = lhs .<->. rhs

        -- Quantify over the main variable x
        forall_x_bicond = aX spec_var_idx biconditional

    in
        -- Universally quantify over all parameters to create the final closed theorem.
        multiAx outerTemplateIdxs forall_x_bicond



-- | Constructs the PropDeBr term for the theorem that a set S is partitioned
-- | by a predicate P and its negation.
-- |
-- | Theorem: ∀(params...) ( isSet(S) → ( (S = {x∈S|P(x)} ∪ {x∈S|¬P(x)}) ∧ ({x∈S|P(x)} ∩ {x∈S|¬P(x)} = ∅) ) )
builderSrcPartitionTheorem :: SentConstraints s t => [Int] -> Int -> t -> s -> s
builderSrcPartitionTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- Construct the two builder sets from the templates
        builderSet_P = builderX spec_var_idx source_set_template p_template
        builderSet_NotP = builderX spec_var_idx source_set_template (neg p_template)

        -- Part 1: The union equality: S = {x|P(x)} ∪ {x|¬P(x)}
        union_of_builders = builderSet_P .\/. builderSet_NotP
        union_equality = source_set_template .==. union_of_builders

        -- Part 2: The intersection equality: {x|P(x)} ∩ {x|¬P(x)} = ∅
        intersection_of_builders = builderSet_P ./\. builderSet_NotP
        intersection_equality = intersection_of_builders .==. emptySet

        -- Combine the two equalities into a single conjunction
        partition_conjunction = union_equality .&&. intersection_equality

        -- Construct the antecedent for the main implication: isSet(S)
        antecedent = isSet source_set_template

        -- Form the main implication
        implication = antecedent .->. partition_conjunction

    in
        -- Universally quantify over all parameters to create the final closed theorem.
        multiAx outerTemplateIdxs implication



-- | Proves that a source set S is equal to the union of two subsets partitioned by a predicate P.
-- | Theorem: S = {x ∈ S | P(x)} ∪ {x ∈ S | ¬P(x)}
-- |
-- | Note: This helper requires that several premises are already proven in the current proof context:
-- |   1. `isSet sourceSet`
-- |   2. The instantiated partition equivalence theorem: `v∈S ↔ ((v∈S∧P(v))∨(v∈S∧¬P(v)))`
-- |   3. The instantiated builder subset theorems: `{x∈S|P(x)} ⊆ S` and `{x∈S|¬P(x)} ⊆ S`
-- |   4. The binary union exists theorem, stated with 'binaryUnionExists'
-- | It also requires that the sets {x∈S|P(x)} and {x∈S|¬P(x)}
-- | have already been instantied with builderInstantiateM
proveBuilderSrcPartitionUnionMFree :: HelperConstraints sE s eL m r t =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    t ->  -- sourceSet: The set S
    s -> -- p_tmplt: The predicate P(x), which uses X spec_var_idx for x.
    ProofGenTStd () r s Text m (s,[Int],())
proveBuilderSrcPartitionUnionMFree spec_var_idx sourceSet p_tmplt =
              -- partition_equiv_theorem_free =
    runProofBySubArgM $ do
        let partition_equiv_theorem_free = partitionEquivTheorem [] spec_var_idx sourceSet p_tmplt
        let (def_prop_P,builderSet_P) = builderPropsFree spec_var_idx sourceSet p_tmplt
        let (def_prop_NotP,builderSet_NotP) = builderPropsFree spec_var_idx sourceSet (neg p_tmplt)

        -- Assumed premise: isSet sourceSet

        -- Step 1: Construct the union of the builder sets.
        let union_of_builders = builderSet_P .\/. builderSet_NotP

        -- Step 2: Prove that the builder sets and their union are sets.
        -- This is done by assuming the relevant instances of the builder subset theorem are proven.
        let subset_P_prop = builderSet_P `subset` sourceSet
        let subset_NotP_prop = builderSet_NotP `subset` sourceSet

        

        (subset_P_proven, _) <- repM subset_P_prop
        (isSet_builder_P, _) <- simpLM subset_P_proven
        (subset_NotP_proven, _) <- repM subset_NotP_prop
        (isSet_builder_NotP, _) <- simpLM subset_NotP_proven
        (isSet_union, _) <- proveUnionIsSetM builderSet_P builderSet_NotP
        -- Step 3: Prove ∀x (x ∈ sourceSet ↔ x ∈ union_of_builders)
        (forall_bicond, _) <- runProofByUGM () $ do
            v <- getTopFreeVar
            
            -- Construct the specific instance of the partition equivalence lemma that we need.
            let p_of_v = sentSubX spec_var_idx v p_tmplt
            
            -- This proof assumes the above equivalence is already proven in the context.
            -- We use repM to formally bring it into this subproof's context.
            (tm_statement, _) <- repM partition_equiv_theorem_free
            (proven_equiv_thm,_) <- uiM v tm_statement

            (def_prop_Union, _, _) <- binaryUnionInstantiateM builderSet_P builderSet_NotP

            -- Goal: Prove v ∈ sourceSet ↔ v ∈ union_of_builders
            -- Direction 1: (v ∈ sourceSet) → (v ∈ union_of_builders)
            (dir1, _) <- runProofByAsmM (v `memberOf` sourceSet) $ do
                (equiv_imp, _) <- bicondElimLM proven_equiv_thm
                (partition_disj, _) <- mpM equiv_imp
                
                (case1_imp, _) <- runProofByAsmM (p_of_v .&&. (v `memberOf` sourceSet)) $ do
                    (forall_p, _) <- simpRM def_prop_P
                    (def_p_inst, _) <- uiM v forall_p
                    (def_p_imp, _) <- bicondElimRM def_p_inst

                    (v_in_sp, _) <- mpM def_p_imp
                    (v_in_sp_or_snotp, _) <- disjIntroLM v_in_sp (v `memberOf` builderSet_NotP)
                    (forall_union, _) <- simpRM def_prop_Union
                    (def_union_inst, _) <- uiM v forall_union
                    (def_union_imp, _) <- bicondElimRM def_union_inst
                    mpM def_union_imp
                
                (case2_imp, _) <- runProofByAsmM (neg p_of_v .&&. (v `memberOf` sourceSet)) $ do
                    (forall_notp, _) <- simpRM def_prop_NotP
                    (def_notp_inst, _) <- uiM v forall_notp
                    (def_notp_imp, _) <- bicondElimRM def_notp_inst
                    (v_in_s_notp, _) <- mpM def_notp_imp
                    (v_in_sp_or_snotp, _) <- disjIntroRM (v `memberOf` builderSet_P) v_in_s_notp
                    (forall_union, _) <- simpRM def_prop_Union
                    (def_union_inst, _) <- uiM v forall_union
                    (def_union_imp, _) <- bicondElimRM def_union_inst
                    mpM def_union_imp
                disjElimM partition_disj case1_imp case2_imp

            -- Direction 2: (v ∈ union_of_builders) → (v ∈ sourceSet)
            (dir2, _) <- runProofByAsmM (v `memberOf` union_of_builders) $ do
                (forall_union, _) <- simpRM def_prop_Union
                (def_union_inst, _) <- uiM v forall_union
                (def_union_imp, _) <- bicondElimLM def_union_inst
                (v_in_sp_or_snotp, _) <- mpM def_union_imp
                
                (forall_subset_p, _) <- simpRM subset_P_proven
                (subset_P_imp, _) <- uiM v forall_subset_p
                
                (forall_subset_notp, _) <- simpRM subset_NotP_proven
                (subset_NotP_imp, _) <- uiM v forall_subset_notp
                
                (case1_imp_dir2, _) <- runProofByAsmM (v `memberOf` builderSet_P) $ mpM subset_P_imp
                (case2_imp_dir2, _) <- runProofByAsmM (v `memberOf` builderSet_NotP) $ mpM subset_NotP_imp
                disjElimM v_in_sp_or_snotp case1_imp_dir2 case2_imp_dir2
            
            -- Combine the two directions into the final biconditional.
            bicondIntroM dir1 dir2

        -- Step 4: Apply the Axiom of Extensionality to get the final equality.
        (ext_axiom, _) <- extensionalityAxiomM
        (ext_inst, _) <- multiUIM ext_axiom [sourceSet, union_of_builders]

        (isSet_Union_and_forall_bicond,_) <- adjM isSet_union forall_bicond
        (full_adj,_) <- adjM (isSet sourceSet) isSet_Union_and_forall_bicond

        (imp1, _) <- mpM ext_inst

        return ()

-- | Proves that the intersection of two disjoint subsets partitioned by a predicate P is the empty set.
-- | Theorem: {x ∈ S | P(x)} ∩ {x ∈ S | ¬P(x)} = ∅
-- |
-- | Note: This helper requires that the following be
-- | already proven:
-- |   1. `isSet sourceSet` has already been proven.
-- |   2. The instantiated builder subset theorems: `{x∈S|P(x)} ⊆ S` and `{x∈S|¬P(x)} ⊆ S`
-- |   3. The 'Binary Intersection Exists' theorem, as stated by 'binaryIntersectionExists'.
-- | It also requires that the sets {x∈S|P(x)} and {x∈S|¬P(x)}
-- | have already been instantied with builderInstantiateM
proveBuilderSrcPartitionIntersectionEmptyMFree ::  HelperConstraints sE s eL m r t =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    t ->  -- sourceSet: The set S
    s -> -- p_tmplt: The predicate P(x), which uses X spec_var_idx for x.
    ProofGenTStd () r s Text m (s,[Int],())
proveBuilderSrcPartitionIntersectionEmptyMFree spec_var_idx sourceSet p_tmplt
           =
    runProofBySubArgM $ do
        let (def_prop_P,builderSet_P) = builderPropsFree spec_var_idx sourceSet p_tmplt
        let (def_prop_NotP,builderSet_NotP) = builderPropsFree spec_var_idx sourceSet (neg p_tmplt)
        -- Assumed premise: isSet sourceSet

        -- Step 1: Construct the two builder sets and their intersection.
        -- et builderSet_P = builderX spec_var_idx sourceSet p_tmplt
        -- let builderSet_NotP = builderX spec_var_idx sourceSet (neg p_tmplt)
        let intersection_of_builders = builderSet_P ./\. builderSet_NotP

        -- Step 2: Prove that the builder sets and their intersection are sets.
        -- This is done by assuming the relevant instances of the builder subset theorem are proven.
        let subset_P_prop = builderSet_P `subset` sourceSet
        let subset_NotP_prop = builderSet_NotP `subset` sourceSet

        repM subset_P_prop
        (isSet_builder_P, _) <- simpLM subset_P_prop

        repM subset_NotP_prop
        (isSet_builder_NotP, _) <- simpLM subset_NotP_prop
        remarkM "ICI 5"
        (intersection_props, _, _) <- binaryIntersectionInstantiateM builderSet_P builderSet_NotP
        (isSet_intersection,_) <- simpLM intersection_props


        -- Step 3: Prove ∀y (¬(y ∈ intersection_of_builders))
        -- This is equivalent to proving the intersection is empty.
        (forall_not_in_intersection, _) <- runProofByUGM () $ do
            v <- getTopFreeVar
            -- We prove ¬(v ∈ intersection) by assuming (v ∈ intersection) and deriving a contradiction.
            (absurd_imp,_) <- runProofByAsmM (v `memberOf` intersection_of_builders) $ do
                -- Get the defining properties of the sets.
                (def_prop_Intersection, _, _) <- binaryIntersectionInstantiateM builderSet_P builderSet_NotP

                -- From `v ∈ A ∩ B`, we can derive `v ∈ A` and `v ∈ B`.
                (forall_inter, _) <- simpRM def_prop_Intersection
                (inter_inst, _) <- uiM v forall_inter
                (inter_imp, _) <- bicondElimLM inter_inst
                (v_in_P_and_NotP, _) <- mpM inter_imp

                -- From `v ∈ {x∈S|P(x)}`, derive `P(v)`.
                (v_in_P, _) <- simpLM v_in_P_and_NotP
                (forall_p, _) <- simpRM def_prop_P
                (p_inst, _) <- uiM v forall_p
                (p_imp, _) <- bicondElimLM p_inst
                (p_and_v_in_s, _) <- mpM p_imp
                (p_of_v, _) <- simpLM p_and_v_in_s

                -- From `v ∈ {x∈S|¬P(x)}`, derive `¬P(v)`.
                (v_in_NotP, _) <- simpRM v_in_P_and_NotP
                (forall_notp, _) <- simpRM def_prop_NotP
                (notp_inst, _) <- uiM v forall_notp
                (notp_imp, _) <- bicondElimLM notp_inst
                (notp_and_v_in_s, _) <- mpM notp_imp
                (notp_of_v, _) <- simpLM notp_and_v_in_s

                -- We have now proven P(v) and ¬P(v), which is a contradiction.
                contraFM p_of_v
            absurdM absurd_imp
        -- `runProofByAsmM` proves `(v ∈ intersection) → False`. `absurdM` turns this into `¬(v ∈ intersection)`.
        -- `runProofByUGM` then generalizes it.

        -- Step 4: Prove the final equality using the Axiom of Extensionality.

        (isSet_Empty_prop, _) <- emptySetAxiomM -- Extracts ∀x. ¬(x ∈ ∅)
        -- We need to prove ∀y (y ∈ intersection ↔ y ∈ ∅).
        -- Since both sides are always false, the biconditional is always true.
        (forall_bicond, _) <- runProofByUGM () $ do
            v <- getTopFreeVar
            (not_in_inter, _) <- uiM v forall_not_in_intersection
            (not_in_empty, _) <- uiM v isSet_Empty_prop
            -- Since ¬(v ∈ intersection) and ¬(v ∈ ∅) are both proven,
            -- we can trivially prove the implications needed for the biconditional.
            (dir1, _) <- runProofByAsmM not_in_inter $ repM not_in_empty
            (dir2, _) <- runProofByAsmM not_in_empty $ repM not_in_inter
            (bicond_of_negs, _) <- bicondIntroM dir1 dir2


            negBicondToPosBicondM bicond_of_negs
            -- This gives us the biconditional: y ∈ intersection ↔ y ∈ ∅
        (ext_axiom, _) <- extensionalityAxiomM
        (ext_inst, _) <- multiUIM ext_axiom [intersection_of_builders, emptySet]
        (isSetEmptySet,_) <- emptySetNotIntM
        (adj1, _) <- adjM isSetEmptySet forall_bicond
        (full_antecedent_for_ext, _) <- adjM isSet_intersection adj1
        
        mpM ext_inst


        return ()


-- | Proves the theorem defined by 'builderSrcPartitionTheorem'.
-- |
-- | This helper proves the closed theorem:
-- |   ∀(params...) ( isSet(S) → ( (S = {x∈S|P(x)} ∪ {x∈S|¬P(x)}) ∧ ({x∈S|P(x)} ∩ {x∈S|¬P(x)} = ∅) ) )
-- |
-- | It works by composing the proofs for each conjunct. It calls:
-- |   1. `proveBuilderSrcPartitionUnionMFree` to prove the union equality.
-- |   2. `proveBuilderSrcPartitionIntersectionEmptyMFree` to prove the intersection equality.
-- |   3. `adjM` to conjoin the two results.
-- | The entire proof is wrapped in `multiUGM` to universally quantify over the parameters.
proveBuilderSrcPartitionTheoremM :: HelperConstraints sE s eL m r t =>
    [Int] ->    -- outerTemplateIdxs: Parameters for the source set and predicate.
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}.
    t ->  -- source_set_template: The source set S, which may contain X_k parameters.
    s -> -- p_template: The predicate P(x), which may contain X_k parameters.
    ProofGenTStd () r s Text m ()
proveBuilderSrcPartitionTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters.
    multiUGM (replicate (length outerTemplateIdxs) ()) $ do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.

        instantiationTerms <- getTopFreeVars (length outerTemplateIdxs)


        -- Step 1:
        -- instantiate both builder sets of the partition, and acquire the specific source_set and
        -- p_tmplt for this context.
        (_,_,(_,sourceSet,p_tmplt)) <- builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template p_template 

        builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template (neg p_template) 

        -- Step 2:
        -- Instantiate the context-dependent lemmas with the context-dependent free variables.
        let lemma1 = builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        multiUIM lemma1 instantiationTerms
        let lemma2 = builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template (neg p_template)
        multiUIM lemma2 instantiationTerms
        let lemma3 = partitionEquivTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        multiUIM lemma3 instantiationTerms

        -- The sub-helpers `proveBuilderSrcPartitionUnionMFree` and `proveBuilderSrcPartitionIntersectionEmptyMFree`
        -- assume these premises are available in the context and will use `repM` to access them.


        -- Step 3: Prove the main implication by assuming the antecedent, `isSet sourceSet`.
        runProofByAsmM (isSet sourceSet) $ do
            -- Within this subproof, `isSet sourceSet` is a proven assumption.
            
            
            -- Step 4: Prove the first conjunct (the union equality).
            (union_equality_proven, _, _) <- proveBuilderSrcPartitionUnionMFree spec_var_idx sourceSet p_tmplt 


            -- Step 5: Prove the second conjunct (the intersection equality).
            (intersection_equality_proven, _, _) <- proveBuilderSrcPartitionIntersectionEmptyMFree spec_var_idx sourceSet p_tmplt

            -- Step 6: Adjoin the two proven equalities to form the final conclusion.
            adjM union_equality_proven intersection_equality_proven
            
            -- The last proven statement is the conjunction. 'runProofByAsmM' will form the implication.
            return ()

    -- The outer 'do' block implicitly returns (), as multiUGM does.
    -- The final universally quantified theorem is now the last proven statement.
    return ()

-- | The schema that houses the proof for 'builderSrcPartitionTheorem'.
-- | It formally declares the other theorems that this proof depends on as lemmas.
builderSrcPartitionSchema :: HelperConstraints sE s eL m r t =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_idx
    t ->  -- source_set_template
    s -> -- p_template
    TheoremSchemaMT () r s Text m ()
builderSrcPartitionSchema outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- The main theorem being proven by this schema.
        main_theorem = builderSrcPartitionTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        -- The proof program for the main theorem.
        proof_program = proveBuilderSrcPartitionTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template

        -- The required lemmas for the proof program.
        -- Lemma 1: The builder subset theorem for P(x).
        lemma1 = builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        -- Lemma 2: The builder subset theorem for ¬P(x).
        lemma2 = builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template (neg p_template)
        -- Lemma 3: The partition equivalence theorem.
        lemma3 = partitionEquivTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        -- Lemma 4: binaryUnionExistsTheorem
        -- needed because the proveUnionIsSet helper is used.
        lemma4 = binaryUnionExistsTheorem
        -- Lemma 5: binaryIntersectionExistsTheorem
        lemma5 = binaryIntersectionExistsTheorem

        -- Extract constants for the schema from the templates.
        source_set_tmplt_consts = extractConstsTerm source_set_template
        p_tmplt_consts = extractConstsSent p_template
        all_consts = source_set_tmplt_consts `Set.union` p_tmplt_consts
        typed_consts = zip (Data.Set.toList all_consts) (repeat ())
    in
        TheoremSchemaMT {
            lemmasM = [lemma1, lemma2, lemma3, lemma4, lemma5],
            proofM = proof_program,
            constDictM = typed_consts
        }

----- END BUILDER SRC PARTITION






-------- SPEC REDUNDANCY


-- | Constructs the PropDeBr term for the theorem stating that a specification
-- | over a set S with predicate P is redundant (i.e., results in S) if and only if
-- | all elements of S already satisfy P.
-- |
-- | Theorem: ∀(params...) (isSet(S(params)) → ({x ∈ S(params) | P(x,params)} = S(params) ↔ ∀x(x ∈ S(params) → P(x,params))))
specRedundancyTheorem :: SentConstraints s t => [Int] -> Int -> t -> s -> s
specRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- Part 1: The LHS of the biconditional: {x ∈ S | P(x)} = S
        builderSet = builderX spec_var_idx source_set_template p_template
        lhs_equality = builderSet .==. source_set_template

        -- Part 2: The RHS of the biconditional: ∀x(x ∈ S → P(x))
        -- Note that p_template already uses X spec_var_idx for the variable x.
        x_in_S = x spec_var_idx `memberOf` source_set_template
        implication_body = x_in_S .->. p_template
        rhs_forall = aX spec_var_idx implication_body

        -- Combine the two sides into the core biconditional
        biconditional = lhs_equality .<->. rhs_forall

        -- Construct the antecedent for the main implication: isSet(S)
        antecedent = isSet source_set_template

        -- Form the main implication for the body of the theorem
        implication = antecedent .->. biconditional

    in
        -- Universally quantify over all parameters to create the final closed theorem.
        multiAx outerTemplateIdxs implication


-- | Given an instantiated source set, predicate, and the proven defining property of a builder set,
-- | this function proves the biconditional: {x ∈ S | P(x)} = S ↔ ∀x(x ∈ S → P(x)).
-- | It encapsulates the core logical derivation for the spec redundancy theorem.
-- | This function requires that
-- |   1. `isSet sourceSet` is already proven in the context.
-- |   2. The set {x ∈ S | P(x)} has already been instantiated with builderInstantiateM.
-- |   3. The instantiated builder subset theorem (i.e. {x ∈ S | P(x)} ⊆ S) is already proven in the context.
-- |   4. The theorem ∀𝑥₂(∀𝑥₁(∀𝑥₀(𝑥₁ = 𝑥₀ → 𝑥₂ ∈ 𝑥₁ → 𝑥₂ ∈ 𝑥₀))) is already asserted, probably as a theorem lemma.
-- |      This function is defined by the function, eqSubstTheorem.
proveSpecRedundancyMFree :: HelperConstraints sE s eL m r t =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    t ->  -- sourceSet: The instantiated source set S
    s -> -- p_tmplt: The instantiated predicate P(x)
    -- PropDeBr -> -- def_prop_B: The proven defining property of the builder set
    ProofGenTStd () r s Text m (s,[Int])
proveSpecRedundancyMFree spec_var_idx sourceSet p_tmplt 
         -- def_prop_B 
         = do
    let (def_prop_B, builderSet) = builderPropsFree spec_var_idx sourceSet p_tmplt
    let builderSubsetTmInst = builderSubsetTheorem [] spec_var_idx sourceSet p_tmplt
    (resultProp,idx,_) <- runProofBySubArgM $ do
        repM (isSet sourceSet) -- We assert this here to emphasize that it should already be proven in the context.
        repM def_prop_B -- We assert this here to emphasize that {x ∈ S | P(x)} has already been instantiated with builderInstantiateM.
        repM builderSubsetTmInst -- We assert this here to emphasize that the instantiated builder subset theorem should
                                 -- already be proven in the context.

        -- The proof is a biconditional, so we prove each direction separately.

        -- == Direction 1: ({x ∈ S | P(x)} = S) → (∀x(x ∈ S → P(x))) ==
        (dir1_implication, _) <- runProofByAsmM (builderSet .==. sourceSet) $ do
            -- Assume B = S. Goal: ∀x(x ∈ S → P(x))
            runProofByUGM () $ do
                v <- getTopFreeVar
                -- Goal: v ∈ S → P(v)
                runProofByAsmM (v `memberOf` sourceSet) $ do
                    let substTmplt = v `memberOf` x 0
                    (s_eq_b, _) <- eqSymM (builderSet .==. sourceSet)
                    -- This proves S=B from B=S.
                    (v_in_B,_) <- eqSubstM 0 substTmplt s_eq_b
                    -- This proves v ∈ B from v ∈ S.

                    -- Now that we have `v ∈ B`, we can use the defining property of B to get P(v).
                    (forall_bicond_B, _) <- simpRM def_prop_B
                    (inst_bicond_B, _) <- uiM v forall_bicond_B
                    (imp_B_to_P, _) <- bicondElimLM inst_bicond_B
                    (p_and_v_in_s, _) <- mpM imp_B_to_P
                    (p_of_v, _) <- simpLM p_and_v_in_s
                    return ()

        -- == Direction 2: (∀x(x ∈ S → P(x))) → ({x ∈ S | P(x)} = S) ==
        (dir2_implication, _) <- runProofByAsmM (aX spec_var_idx ((x spec_var_idx `memberOf` sourceSet) .->. p_tmplt)) $ do
            -- Assume ∀x(x ∈ S → P(x)). Goal: B = S.
            (isSet_B, _) <- simpLM builderSubsetTmInst

            (forall_bicond_sets, _) <- runProofByUGM () $ do
                v <- getTopFreeVar
                (forall_subset_imp, _) <- simpRM builderSubsetTmInst

                (imp_B_to_S, _) <- uiM v forall_subset_imp
                (imp_S_to_B, _) <- runProofByAsmM (v `memberOf` sourceSet) $ do
                    let forall_S_implies_P = aX spec_var_idx ((x spec_var_idx `memberOf` sourceSet) .->. p_tmplt)
                    (instantiated_imp, _) <- uiM v forall_S_implies_P
                    (p_of_v, _) <- mpM instantiated_imp
                    (v_in_S_and_P, _) <- adjM (v `memberOf` sourceSet) p_of_v
                    (forall_bicond_B, _) <- simpRM def_prop_B
                    (inst_bicond_B, _) <- uiM v forall_bicond_B
                    (imp_to_B, _) <- bicondElimRM inst_bicond_B
                    adjM p_of_v (v `memberOf` sourceSet)
                    mpM imp_to_B
                    return ()
                bicondIntroM imp_B_to_S imp_S_to_B
            (ext_axiom, _) <- extensionalityAxiomM
            (ext_inst, _) <- multiUIM ext_axiom [builderSet, sourceSet]
            (ante1, _) <- adjM (isSet sourceSet) forall_bicond_sets
            (full_antecedent, _) <- adjM isSet_B ante1
            (imp1, _) <- mpM ext_inst
            return ()

        -- Final Step: Combine the two main implications into the final biconditional.
        bicondIntroM dir1_implication dir2_implication
        return ()
    return (resultProp,idx)


-- | Proves the theorem defined by 'specRedundancyTheorem'.
-- | This version correctly composes the `proveSpecRedundancyMFree` helper.
proveSpecRedundancyTheoremM :: HelperConstraints sE s eL m r t  =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    t ->  -- source_set_template
    s -> -- p_template
    ProofGenTStd () r s Text m ()
proveSpecRedundancyTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters specified in outerTemplateIdxs.
    multiUGM (replicate (length outerTemplateIdxs) ()) $ do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.

        instantiationTerms <- getTopFreeVars (length outerTemplateIdxs)

        -- Establish the properties of the builderSet here
        -- and acquire the instantiated templates with the free variables for this specific proof context.
        (_,_,(_,sourceSet,p_tmplt)) <- builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template p_template
        builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template (neg p_template)
        let lemma2 = builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        multiUIM lemma2 instantiationTerms
        

        -- Step 2: Prove the main implication by assuming its antecedent, `isSet sourceSet`.
        runProofByAsmM (isSet sourceSet) $ do
            



            -- Now that `isSet sourceSet` is a proven assumption in this context,
            -- we can call the specific proof helper `proveSpecRedundancyMFree`.
            -- That helper will create its own sub-argument and prove the biconditional.
            
            (bicond_proven, _) <- proveSpecRedundancyMFree spec_var_idx sourceSet p_tmplt
            
            -- The last proven statement is the desired biconditional.
            -- `runProofByAsmM` will use this to conclude the implication.
            return ()

    -- The outer `do` block implicitly returns (), as multiUGM does.
    -- The final universally quantified theorem is now the last proven statement.
    return ()

-- | The schema that houses the proof for 'specRedundancyTheorem'.
-- | This theorem is proven from axioms and does not depend on other high-level theorems.
specRedundancySchema :: HelperConstraints sE s eL m r t=>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    t ->  -- source_set_template
    s -> -- p_template
    TheoremSchemaMT () r s Text m ()
specRedundancySchema outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- The main theorem being proven by this schema.
        main_theorem = specRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        -- The proof program for the main theorem.
        proof_program = proveSpecRedundancyTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template

        -- Extract constants for the schema from the templates.
        source_set_tmplt_consts = extractConstsTerm source_set_template
        p_tmplt_consts = extractConstsSent p_template
        all_consts = source_set_tmplt_consts `Set.union` p_tmplt_consts
        typed_consts = Prelude.map (, ()) (Data.Set.toList all_consts)
    in
        TheoremSchemaMT {
            lemmasM = [ 
                       builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template p_template],
            proofM = proof_program,
            constDictM = typed_consts
        }


--END SPEC REDUNDANCY

--SPEC ANTI-REDUNDANCY THEOREM


-- | Constructs the PropDeBr term for the theorem stating that a specification
-- | over a set S with predicate ¬P is identical with the empty set if and only if
-- | all elements of S already satisfy P.
-- |
-- | Theorem: ∀(params...) (isSet(S(params)) → ({x ∈ S(params) | ¬P(x,params)} = ∅ ↔ ∀x(x ∈ S(params) → P(x,params))))
specAntiRedundancyTheorem ::  SentConstraints s t => [Int] -> Int -> t -> s -> s
specAntiRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- Part 1: The LHS of the biconditional: {x ∈ S | ¬P(x)} = ∅
        builderSet = builderX spec_var_idx source_set_template (neg p_template)
        lhs_equality = builderSet .==. emptySet

        -- Part 2: The RHS of the biconditional: ∀x(x ∈ S → P(x))
        -- Note that p_template already uses X spec_var_idx for the variable x.
        x_in_S = x spec_var_idx `memberOf` source_set_template
        implication_body = x_in_S .->. p_template
        rhs_forall = aX spec_var_idx implication_body

        -- Combine the two sides into the core biconditional
        biconditional = lhs_equality .<->. rhs_forall

        -- Construct the antecedent for the main implication: isSet(S)
        antecedent = isSet source_set_template

        -- Form the main implication for the body of the theorem
        implication = antecedent .->. biconditional

    in
        -- Universally quantify over all parameters to create the final closed theorem.
        multiAx outerTemplateIdxs implication



-- | Given an instantiated source set, predicate, and the proven defining property of a builder set,
-- | this function proves the biconditional: {x ∈ S | ¬P(x)} = ∅ ↔ ∀x(x ∈ S → P(x)).
-- | It encapsulates the core logical derivation for the spec redundancy theorem.
-- | This function requires that
-- |   1. `isSet sourceSet` is already proven in the context.
-- |   2. The set {x ∈ S | P(x)} has already been instantiated with builderInstantiateM.
-- |   3. The set {x ∈ S | ¬P(x)} has already been instantiated with builderInstantiateM.
-- |   3. The following instance of the builder subset theorem is alread proven:
-- |       {x ∈ S | ¬P(x)} ⊆ S
-- |   4. The instatinated builderSrcPartition theorem is already proven in this context:
-- |       isSet(S) → S = ({𝑥₀ ∈ S | P(𝑥₀)} ∪ {𝑥₀ ∈ S | ¬P(𝑥₀)}) ∧ ({𝑥₀ ∈ S | P(𝑥₀)} ∩ {𝑥₀ ∈ S | ¬P(𝑥₀)}) = ∅
-- |   5. The instantiated spec redundancy theorem is already proven in the context (i.e
-- |        isSet(S) → {𝑥₀ ∈ S | P(𝑥₀)} = S ↔ ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀)) 
-- |   6. The disjoingSubsetIsEmpty theoremm, ∀a (∀b(isSet(a) ∧ a ∩ b = ∅ ∧ b ⊆ a → b=∅)), is already proven.
proveSpecAntiRedundancyMFree :: HelperConstraints sE s eL m r t =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    t ->  -- sourceSet: The instantiated source set S
    s -> -- p_tmplt: The instantiated predicate P(x)
    ProofGenTStd () r s Text m (s,[Int])
proveSpecAntiRedundancyMFree spec_var_idx sourceSet p_tmplt 
         -- def_prop_B 
         = do
    let (anti_spec_prop, negBuilderSet) = builderPropsFree spec_var_idx sourceSet (neg p_tmplt)
    let (spec_prop, builderSet) = builderPropsFree spec_var_idx sourceSet p_tmplt
    let negBuilderSubsetTmInst = builderSubsetTheorem [] spec_var_idx sourceSet (neg p_tmplt)
    let builderSrcPartitionTmInst = builderSrcPartitionTheorem [] spec_var_idx sourceSet p_tmplt
    let specRedundancyTmInst = specRedundancyTheorem [] spec_var_idx sourceSet p_tmplt
    (resultProp,idx,_) <- runProofBySubArgM $ do
        repM disjointSubsetIsEmptyTheorem
            -- We assert the following which should already be proven: ∀a (∀b(isSet(a) ∧ a ∩ b = ∅ ∧ b ⊆ a → b=∅))
        repM (isSet sourceSet) -- We assert this here to emphasize that it should already be proven in the context.

        repM anti_spec_prop -- We assert this here to emphasize that {x ∈ S | ¬P(x)} has already been instantiated with builderInstantiateM.
 
        repM negBuilderSubsetTmInst 
        -- We assert this here to emphasize that {x ∈ S | ¬P(x)} ⊆ S has already been asserted as a lemma.

        repM specRedundancyTmInst -- We assert this here to emphasize that the instantiated spec redundancy theorem should
                                 -- already be proven in the context.

        repM builderSrcPartitionTmInst -- We assert this here to emphasize that the instantiated builder source partition theorem should
                                 -- already be proven in the context.
        (builderSrcPartitionTmInstMain,_) <- mpM builderSrcPartitionTmInst
        -- We have now proven: S = ({𝑥₀ ∈ S | P(𝑥₀)} ∪ {𝑥₀ ∈ S | ¬P(𝑥₀)}) ∧ ({𝑥₀ ∈ S | P(𝑥₀)} ∩ {𝑥₀ ∈ S | ¬P(𝑥₀)}) = ∅

        (specRedundancyTmInstMain,_) <- mpM specRedundancyTmInst
        -- We have now proven: {𝑥₀ ∈ S | P(𝑥₀)} = S ↔ ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀)) 

        -- The proof is a biconditional, so we prove each direction separately.

        -- == Direction 1: ({x ∈ S | ¬P(x)} = ∅) → (∀x(x ∈ S → P(x))) ==
        let cond_ls = negBuilderSet .==. emptySet
        (dir1_implication, _) <- runProofByAsmM cond_ls $ do
            -- Assume {x ∈ S | ¬P(x)} = ∅. Goal: ∀x(x ∈ S → P(x)).
            simpLM builderSrcPartitionTmInstMain
            -- We have now proven: S = ({𝑥₀ ∈ S | P(𝑥₀)} ∪ {𝑥₀ ∈ S | ¬P(𝑥₀)})
            let substTmplt = sourceSet .==. (builderSet .\/. x 0)
            eqSubstM 0 substTmplt cond_ls
            -- We have now proven: S = ({𝑥₀ ∈ S | P(𝑥₀)} ∪ ∅)
            (unionWithEmptySetTmInstance,_) <- uiM builderSet unionWithEmptySetTheorem
            -- We have now proven:  IsSet ({𝑥₀ ∈ S | P(𝑥₀)}) → ({𝑥₀ ∈ S | P(𝑥₀)} ∪ ∅) = {𝑥₀ ∈ S | P(𝑥₀)} 
            (negBuilderSet_isSet,_) <- simpLM spec_prop
            -- We have now proven: IsSet  ({𝑥₀ ∈ S | P(𝑥₀)}) 
            (actual_union_w_emptyset,_) <- mpM unionWithEmptySetTmInstance
            -- We have now proven: ({𝑥₀ ∈ S | P(𝑥₀)} ∪ ∅) = {𝑥₀ ∈ S | P(𝑥₀)}
            let substTmplt = sourceSet .==. x 0
            (specRedCond,_) <- eqSubstM 0 substTmplt actual_union_w_emptyset
            -- We have proven: S = {𝑥₀ ∈ S | 𝑥₀ = 𝑥₀}
            eqSymM specRedCond
            -- We have now proven: {𝑥₀ ∈ S | P(𝑥₀)} = S
            (final_imp,_) <- bicondElimLM specRedundancyTmInstMain
            -- We have now proven: {𝑥₀ ∈ S | P(𝑥₀)} = S → ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀))
            mpM final_imp
            -- We have now proven: ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀))

        -- == Direction 2: (∀x(x ∈ S → P(x))) → ({x ∈ S | ¬P(x)} = ∅) ==
        let cond_rs = aX spec_var_idx ((x spec_var_idx `memberOf` sourceSet) .->. p_tmplt)
        (dir2_implication,_) <- runProofByAsmM cond_rs $ do
            -- Assume ∀x(x ∈ S → P(x)). Goal: {x ∈ S | ¬P(x)} = ∅.
            (specRedImpBwd,_) <- bicondElimRM specRedundancyTmInstMain
            (builderSetEqSrcSet,_) <- mpM specRedImpBwd
            -- We have now proven: {x ∈ S | P(x)} = S

            
            (partDisjoint,_) <- simpRM builderSrcPartitionTmInstMain
            -- We have now proven: ({𝑥₀ ∈ S | P(𝑥₀)} ∩ {𝑥₀ ∈ S | ~P(𝑥₀)}) = ∅
            let eqSubstTemplate = (x 0 ./\. negBuilderSet) .==. emptySet
            (sourceNegBuilderDisjoint,_) <- eqSubstM 0 eqSubstTemplate builderSetEqSrcSet
            -- We have now proven: S ∩ {𝑥₀ ∈ S | ~P(𝑥₀)} = ∅
            
            (finalImp,_) <- multiUIM disjointSubsetIsEmptyTheorem [sourceSet, negBuilderSet]
            -- We have now proven: isSet(S) ∧ S ∩ {x ∈ S | ¬P(x)} = ∅ ∧ {x ∈ S | ¬P(x)} ⊆ S → {x ∈ S | ¬P(x)} =∅
            
            (adj1,_) <- adjM sourceNegBuilderDisjoint negBuilderSubsetTmInst
            (adj2,_) <- adjM (isSet sourceSet) adj1

            -- We have now proven: isSet(S) ∧ S ∩ {x ∈ S | ¬P(x)} = ∅ ∧ {x ∈ S | ¬P(x)} ⊆ S
            mpM finalImp
            -- We have now proven: {x ∈ S | ¬P(x)} = ∅

 
        -- Final Step: Combine the two main implications into the final biconditional.
        bicondIntroM dir1_implication dir2_implication
        return ()
    return (resultProp,idx)

-- | Proves the theorem defined by 'specAntiRedundancyTheorem'.
-- | This version correctly composes the `proveSpecAntiRedundancyMFree` helper.
proveSpecAntiRedundancyTheoremM :: HelperConstraints sE s eL m r t  =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    t ->  -- source_set_template
    s -> -- p_template
    ProofGenTStd () r s Text m ()
proveSpecAntiRedundancyTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters specified in outerTemplateIdxs.
    multiUGM (replicate (length outerTemplateIdxs) ()) $ do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.
        instantiationTerms <- getTopFreeVars (length outerTemplateIdxs)
        -- Establish the properties of the builderSet here
        -- and acquire the instantiated templates with the free variables for this specific proof context.
        (_,_,(_,sourceSet,p_tmplt)) <- builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template p_template
        builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template (neg p_template)

        multiUIM (builderSrcPartitionTheorem outerTemplateIdxs spec_var_idx source_set_template p_template) instantiationTerms
        multiUIM (specRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template) instantiationTerms
        multiUIM (builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template (neg p_template)) instantiationTerms



        -- Step 2: Prove the main implication by assuming its antecedent, `isSet sourceSet`.
        runProofByAsmM (isSet sourceSet) $ do
            



            -- Now that `isSet sourceSet` is a proven assumption in this context,
            -- we can call the specific proof helper `proveSpecRedundancyMFree`.
            -- That helper will create its own sub-argument and prove the biconditional.
            
            (bicond_proven, _) <- proveSpecAntiRedundancyMFree spec_var_idx sourceSet p_tmplt
            
            -- The last proven statement is the desired biconditional.
            -- `runProofByAsmM` will use this to conclude the implication.
            return ()

    -- The outer `do` block implicitly returns (), as multiUGM does.
    -- The final universally quantified theorem is now the last proven statement.
    return ()


-- | The schema that houses the proof for 'specAntiRedundancyTheorem'.
-- | This theorem is proven from axioms and does not depend on other high-level theorems.
specAntiRedundancySchema :: HelperConstraints sE s eL m r t =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    t ->  -- source_set_template
    s -> -- p_template
    TheoremSchemaMT () r s Text m ()
specAntiRedundancySchema outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- The main theorem being proven by this schema.
        main_theorem = specAntiRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        -- The proof program for the main theorem.
        proof_program = proveSpecAntiRedundancyTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template

        -- Extract constants for the schema from the templates.
        source_set_tmplt_consts = extractConstsTerm source_set_template
        p_tmplt_consts = extractConstsSent p_template
        all_consts = source_set_tmplt_consts `Set.union` p_tmplt_consts
        typed_consts = zip (Data.Set.toList all_consts) (repeat ())
    in
        TheoremSchemaMT {
            lemmasM = [--eqSubstTheorem, 
                       builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template (neg p_template),
                       
                       specRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template,
                       builderSrcPartitionTheorem outerTemplateIdxs spec_var_idx source_set_template p_template,
                       unionWithEmptySetTheorem,
                       disjointSubsetIsEmptyTheorem],
            proofM = proof_program,
            constDictM = typed_consts
        }





-- END SPEC ANTIREDUNDANCY THEOREM


-- CROSS PROD EXISTS THEOREM

-- crossProductDefEquiv theorem won't have it's own section.
-- It is a theorem probably used exclusively by crossProductExists





-- | This function composes the "tuple equality theorems":
-- | If tuple_len = 0, the theorem composed is:
-- |    ∅ = ∅
-- | If tuple len = n > 0, the theorem composed is:
-- |    ∀𝑥_<2n-1>(∀𝑥_<2n-2>...(∀𝑥_<1>(∀𝑥_<0>((𝑥_<2n-1>,...,𝑥_<n>) = (𝑥_<n-1>,...,𝑥_<0>) ↔ 𝑥_<2n-1> = 𝑥_<n-1> ∧ .... ∧ 𝑥_<n> = 𝑥_<0>))))
-- |
-- | For instance:
-- | tupleEqTheorem 0 is:
-- |    ∅ = ∅
-- | tupleEqTheorem 1 is:
-- |    ∀𝑥₁(∀𝑥₀(𝑥₁ = 𝑥₀ ↔ 𝑥₁ = 𝑥₀))
-- | tupleEqTheorem 2 is:
-- |    ∀𝑥₃(∀𝑥₂(∀𝑥₁(∀𝑥₀((𝑥₃,𝑥₂) = (𝑥₁,𝑥₀) ↔ 𝑥₃ = 𝑥₁ ∧ 𝑥₂ = 𝑥₀))))
-- | tupleEqTheorem 3 is:
-- |    ∀𝑥₅(∀𝑥₄(∀𝑥₃(∀𝑥₂(∀𝑥₁(∀𝑥₀((𝑥₅,𝑥₄,𝑥₃) = (𝑥₂,𝑥₁,𝑥₀) ↔ 𝑥₅ = 𝑥₂ ∧ 𝑥₄ = 𝑥₁ ∧ 𝑥₃ = 𝑥₀))))))
tupleEqTheorem :: SentConstraints s t => Int -> s
tupleEqTheorem tuple_len =
    if tuple_len > 0 then
        let
            -- Create a list of component-wise equalities, e.g., [x₀=xₙ, x₁=xₙ₊₁, ...]
            subexps = fmap (\i -> x i .==. x (tuple_len + i)) [0 .. tuple_len - 1]
            -- Correctly join the list of equalities into a single conjunction.
            conjunction = foldr1 (.&&.) subexps
            
            -- The right tuple uses variables from n to 2n-1.
            right_tuple = tuple (fmap x [tuple_len .. tuple_len*2 - 1])
            -- The left tuple uses variables from 0 to n-1.
            left_tuple = tuple (fmap x [0 .. tuple_len - 1])
        in
            -- Universally quantify over all 2n variables.
            multiAx [0..tuple_len*2 - 1]
            (left_tuple .==. right_tuple .<->. conjunction)
    else
        -- The base case for a 0-length tuple is true by definition.
        emptySet .==. emptySet





-- | A high-level tactic that performs substitution based on an equality between tuples.
-- |
-- | This function takes a list of template variable indices, a proven equality between
-- | two tuples of the same length, and a template sentence.
-- |
-- | It requires that the template, when substituted with the components of the LEFT-hand
-- | side of the tuple equality, is already a proven proposition in the context.
-- |
-- | It then formally proves that the template also holds when substituted with the
-- | components of the RIGHT-hand side of the tuple equality.
-- |
-- | @param indices A list of the template variable indices used in the template.
-- | @param tuple_eq_sent The proven proposition `(t₁,...,tₙ) = (u₁,...,uₙ)`.
-- | @param template_sent The template sentence `P(xᵢ₁, xᵢ₂, ...)` where i_k ∈ indices.
-- | @return The proven proposition `P(u₁,...,uₙ)`.
tupleSubstM :: (HelperConstraints sE s eL m r1 t)  =>
    [Int] -> s -> s -> ProofGenTStd () r1 s Text m (s, [Int])
tupleSubstM indices tuple_eq_sent template_sent = do
    (substituted,idx,_) <- runProofBySubArgM $ do
        let n = length indices
        
        -- Step 1: Parse the tuple equality. This will throw an error if the input
        -- is not a valid equality of two n-tuples.


        (lhs_tuple_term, rhs_tuple_term) <- maybe (throwM (MetaRuleErrTupleSubstNotAnEquality tuple_eq_sent)) return (parseEq tuple_eq_sent)

        lhs_components <- maybe (throwM (MetaRuleErrTupleSubstIncorrectLHS n lhs_tuple_term)) return (parseTupleFixed lhs_tuple_term n)
        rhs_components <- maybe (throwM (MetaRuleErrTupleSubstIncorrectRHS n rhs_tuple_term)) return (parseTupleFixed rhs_tuple_term n)

        -- Step 2: Acknowledge the required premises from the outer context.
        repM tuple_eq_sent
        let tuple_eq_thm = tupleEqTheorem n
        repM tuple_eq_thm

        -- Step 3: Instantiate the tuple equality theorem with the components of our tuples.
        -- The instantiation terms must match the variable order in the theorem definition.
        let instantiation_terms = lhs_components ++ rhs_components
        (instantiated_thm, _) <- multiUIM tuple_eq_thm instantiation_terms
        
        -- We now have a proof of: (lhs_tuple = rhs_tuple) ↔ (lhs₁=rhs₁ ∧ ...)

        -- Step 4: Use the instantiated theorem to prove the conjunction of component equalities.
        (forward_imp, _) <- bicondElimLM instantiated_thm
        (conjoined_equalities, _) <- mpM forward_imp

        -- Step 5: Deconstruct the proven conjunction into a list of individual proven equalities.
        -- A conjunction of n items has n-1 '∧' operators.
        let num_splits = if n > 0 then n - 1 else 0
        component_equalities_proofs <- deconstructMultiAdjM conjoined_equalities num_splits

        -- Step 6: Use eqSubstMultiM to perform the final substitution.
        -- The required premise for eqSubstMultiM (the template substituted with the LHS
        -- components) is assumed to already be proven in the outer context.
        let substitutions = zip indices (Prelude.map fst component_equalities_proofs)
        eqSubstMultiM substitutions template_sent
        return ()
    return (substituted, idx)

-- | This function composes the "pair in universe theorem":
-- |
-- |  ∀𝑥₃(∀𝑥₂(∀𝑥₁(∀𝑥₀(isSet(𝑥₃) ∉ ℤ ∧ isSet(𝑥₂) ∧ 𝑥₁ ∈ 𝑥₃ ∧ 𝑥₀ ∈ 𝑥₂ 
-- |         → (𝑥₁,𝑥₀) ∈ 𝒫(𝒫(𝑥₃ ∪ 𝑥₂))))))
-- |
pairInUniverseTheorem :: SentConstraints s t => s
pairInUniverseTheorem =
    let thm_A=0; thm_B=1; thm_x=2; thm_y=3
        thm_univ = powerSet (powerSet (x thm_A .\/. x thm_B))
        thm_pair_univ_antecedent = isSet (x thm_A) .&&. isSet (x thm_B) .&&. (x thm_x `memberOf` x thm_A) .&&. (x thm_y `memberOf` x thm_B)
        thm_pair_univ_consequent = pair (x thm_x) (x thm_y) `memberOf` thm_univ
        pair_in_universe_theorem_closed = multiAx [thm_A, thm_B, thm_x, thm_y] (thm_pair_univ_antecedent .->. thm_pair_univ_consequent)
    in
        pair_in_universe_theorem_closed



predicateP :: SentConstraints s t => t -> t -> t -> IndexTracker s
predicateP setA setB var = do
    -- Create the indices for the existential quantifiers.
    x_idx <- newIndex
    y_idx <- newIndex

    -- Construct the predicate P(z) := ∃x∃y (z = <x,y> ∧ x ∈ A ∧ y ∈ B)
    let pred = eX x_idx (eX y_idx (
            (var .==. pair (x x_idx) (x y_idx))
                    .&&. (x x_idx `memberOf` setA)
                    .&&. (x y_idx `memberOf` setB)
            ))
    dropIndices 2
    return pred


-- | Constructs the PropDeBr term for the closed theorem stating that the property
-- | of a cross product derived via the Axiom of Specification implies the
-- | canonical property of a cross product.
-- |
-- | 'binaryUnionExistsTheorem' is a required lemma for this theorem.
-- | Theorem: ∀A∀B((isSet A ∧ isSet B) → (SpecProp(A,B) → CanonicalProp(A,B)))
crossProductDefEquivTheorem :: SentConstraints s t => s
crossProductDefEquivTheorem =
    fst $ runIndexTracker (
        do
            -- Define integer indices for the template variables (X k).
            -- These will be bound by the outermost quantifiers for A and B.
            a_idx <- newIndex
            b_idx <- newIndex

            let setA = x a_idx
            let setB = x b_idx

            -- Define the inner predicate P(z) used in the specification.
            -- P(z) := ∃x∃y (z = <x,y> ∧ x ∈ A ∧ y ∈ B)
            let predicateQ var = do
                    spec_x_idx <- newIndex
                    spec_y_idx <- newIndex
                    let pred = eX spec_x_idx (eX spec_y_idx (
                            (var .==. pair (x spec_x_idx) (x spec_y_idx))
                                    .&&. (x spec_x_idx `memberOf` setA)
                                    .&&. (x spec_y_idx `memberOf` setB)
                            ))
                    dropIndices 2
                    return pred


 
            -- Define the universe set U = P(P(A U B))
            let universeSet = powerSet (powerSet (setA .\/. setB))

            -- Define the cross product object B via the builder shorthand, which
            -- is equivalent to the Hilbert term from specification.
            -- B := {z ∈ U | P(z)}
            spec_z_idx <- newIndex
            propP <- predicateP setA setB (x spec_z_idx)
            let crossProdObj = builderX spec_z_idx universeSet propP
            dropIndices 1 -- Drop spec_z_idx

            -- Now, construct the two main properties that form the implication.

            -- 1. SpecProp(A,B): The defining property of B as derived from specification.
            --    isSet(B) ∧ ∀z(z∈B ↔ (P(z) ∧ z∈U))
            spec_prop_z_idx <- newIndex
            propP <- predicateP setA setB (x spec_prop_z_idx)
            let spec_prop_body = (x spec_prop_z_idx `memberOf` crossProdObj) .<->.
                             (propP .&&. (x spec_prop_z_idx `memberOf` universeSet))
            let spec_prop = isSet crossProdObj .&&. aX spec_prop_z_idx spec_prop_body

            dropIndices 1 -- Drop spec_prop_z_idx


            -- 2. CanonicalProp(A,B): The standard definition of the property of A × B.
            --    isSet(B) ∧ ∀x∀y(<x,y>∈B ↔ (x∈A ∧ y∈B))
            canon_x_idx <- newIndex
            canon_y_idx <- newIndex
            let canon_element_prop = (x canon_x_idx `memberOf` setA) .&&. (x canon_y_idx `memberOf` setB)
            let canon_pair_in_b = pair (x canon_x_idx) (x canon_y_idx) `memberOf` crossProdObj
            let canon_quantified_bicond = aX canon_x_idx (aX canon_y_idx (canon_element_prop .<->. canon_pair_in_b))
            dropIndices 2 -- Drop canon_x_idx, canon_y_idx
            let canonical_prop = isSet crossProdObj .&&. canon_quantified_bicond

            -- Construct the main implication of the theorem: SpecProp(A,B) → CanonicalProp(A,B)
            let spec_implies_canonical = spec_prop .->. canonical_prop

            -- Construct the antecedent for the entire theorem: isSet(A) ∧ isSet(B)
            let isSet_A = isSet setA
            let isSet_B = isSet setB
            let theorem_antecedent = isSet_A .&&. isSet_B

            -- Form the implication for the body of the theorem
            let theorem_body = theorem_antecedent .->. spec_implies_canonical
            let returnSent = multiAx [a_idx, b_idx] theorem_body

            dropIndices 2 -- Drop a_idx, b_idx

            return returnSent
        )

    

-- | Proves "crossProductDefEquivTheorem".
proveCrossProductDefEquivM :: (HelperConstraints sE s eL m r t)  =>
    ProofGenTStd () r s Text m ()
proveCrossProductDefEquivM = do
    -- Universally generalize over A and B
    multiUGM [(), ()] $ do
        -- Inside UG, free variables v_A and v_B are introduced
        v_Av_B <- getTopFreeVars 2
        let setB = head v_Av_B
        let setA = v_Av_B!!1

        -- Prove the main implication by assuming the antecedent
        runProofByAsmM (isSet setA .&&. isSet setB) $ do
            -- Within this subproof, isSet A and isSet B are proven assumptions.
            -- Construct all necessary terms and properties internally.
            let universeSet = powerSet (powerSet (setA .\/. setB))
            let z_idx = 0; x_idx = 1; y_idx = 2; setA_idx = 3; setB_idx = 4
            let universeSet_tmplt = powerSet (powerSet (x setA_idx .\/. x setB_idx))
            -- let predicate_P = eX x_idx (eX y_idx (
            --                      (x z_idx .==. pair (x x_idx) (x y_idx))
            --                      .&&. (x x_idx `memberOf` setA)
            --                      .&&. (x y_idx `memberOf` setB)
            --                  ))
            let predicate_P_tmplt = eX x_idx (eX y_idx (
                                  (x z_idx .==. pair (x x_idx) (x y_idx))
                                  .&&. (x x_idx `memberOf` x setA_idx)
                                  .&&. (x y_idx `memberOf` x setB_idx)
                              ))
 
            -- Correctly use specificationFreeMBuilder, which is designed to handle
            -- the free variables v_A and v_B present in 'setA', 'setB', and thus in 'predicate_P'.
            (definingProp_of_B, _, (crossProdObj,_,_)) <- 
                 builderInstantiateM [setA, setB] [setA_idx, setB_idx] z_idx universeSet_tmplt predicate_P_tmplt

            crossProdObj_txt <- showTermM crossProdObj
            remarkM $ "Cross Product Object from Builder: " <> crossProdObj_txt
            
            -- Now, prove the implication: definingProp_of_B → canonical_prop_of_B
            runProofByAsmM definingProp_of_B $ do
                -- This inner proof derives the canonical property from the specification property.
                (isSet_B_proven, _) <- simpLM definingProp_of_B
                (spec_forall_bicond, _) <- simpRM definingProp_of_B
                (quantified_bicond_derived, _) <- multiUGM [(), ()] $ do
                    v_x_innerV_y_inner <- getTopFreeVars 2
                    let v_x_inner = head v_x_innerV_y_inner
                    let v_y_inner = v_x_innerV_y_inner !! 1
                    (dir1,_) <- runProofByAsmM (pair v_x_inner v_y_inner `memberOf` crossProdObj) $ do
                        (spec_inst,_) <- uiM (pair v_x_inner v_y_inner) spec_forall_bicond
                        (imp,_) <- bicondElimLM spec_inst
                        (inU_and_P,_) <- mpM imp
                        (p_of_pair,_) <- simpLM inU_and_P

                        -- CORRECTED: Perform existential instantiation twice for the nested quantifiers.
                        -- First, instantiate the outer ∃a from ∃a(∃b.P(a,b)).
                        (p_inst_for_b, _, v_a_h) <- eiHilbertM p_of_pair

                        -- Second, instantiate the inner ∃b from the resulting proposition.
                        (p_inst_final, _, v_b_h) <- eiHilbertM p_inst_for_b

                        -- 'p_inst_final' is now the fully instantiated body:
                        -- (<v_x,v_y> = <v_a_h,v_b_h>) ∧ v_a_h∈A ∧ v_b_h∈B

                        ((pairEqRev,_),(preSub,_)) <- deconstructAdjM p_inst_final
                        (pairEq,_) <- eqSymM pairEqRev
                        let substTmplt = x 0 `memberOf` setA .&&. x 1 `memberOf` setB

                        tupleSubstM [0,1] pairEq substTmplt

                    (dir2,_) <- runProofByAsmM ((v_x_inner `memberOf` setA) .&&. (v_y_inner `memberOf` setB)) $ do
                        -- Goal: Prove <x,y> ∈ B. This means proving P(<x,y>) ∧ <x,y>∈U.

                        -- Part 1: Prove P(<x,y>), which is ∃a∃b(<x,y>=<a,b> ∧ a∈A ∧ b∈B).
                        -- We prove this by witnessing with a=v_x and b=v_y.
                        (vx_in_A_p, _) <- simpLM ((v_x_inner `memberOf` setA) .&&. (v_y_inner `memberOf` setB))
                        (vy_in_B_p, _) <- simpRM ((v_x_inner `memberOf` setA) .&&. (v_y_inner `memberOf` setB))
                        (refl_pair, _) <- eqReflM (pair v_x_inner v_y_inner)

                        (in_A_and_in_B, _) <- adjM vx_in_A_p vy_in_B_p
                        (p_vx_vy_instantiated_body, _) <- adjM refl_pair in_A_and_in_B


                        let p_ab_template = (pair v_x_inner v_y_inner .==. pair (x 0) (x 1)) .&&. ((x 0 `memberOf` setA) .&&. (x 1 `memberOf` setB))
                        let p_vx_y_template = sentSubX 0 v_x_inner p_ab_template
                        let eg_target_y = eX 1 p_vx_y_template
                        (exists_y_prop, _) <- egM v_y_inner eg_target_y

                        let p_x_b_template = eX 1 (sentSubX 0 (x 0) p_ab_template)
                        let eg_target_x = eX 0 p_x_b_template
                        (p_of_pair_proven, _) <- egM v_x_inner eg_target_x

                        -- Instantiate the pair in universe theorem and use it.
                        (instantiated_thm, _) <- multiUIM pairInUniverseTheorem [setA, setB, v_x_inner, v_y_inner]


                        (conj3_4, _) <- adjM vx_in_A_p vy_in_B_p
                        (isSetB_p, _) <- simpRM (isSet setA .&&. isSet setB)
                        (conj2_3_4, _) <- adjM isSetB_p conj3_4
                        (isSetA_p, _) <- simpLM (isSet setA .&&. isSet setB)
                        (full_antecedent, _) <- adjM isSetA_p conj2_3_4
                        (pair_in_U_proven, _) <- mpM instantiated_thm
                        -- Part 3: Combine proofs for P(<x,y>) and <x,y>∈U to match the spec property.
                        (in_U_and_P, _) <- adjM p_of_pair_proven pair_in_U_proven
                        
                        -- Part 4: Use the spec property to conclude <x,y> ∈ B
                        (spec_bicond_inst, _) <- uiM (pair v_x_inner v_y_inner) spec_forall_bicond
                        (spec_imp_backward, _) <- bicondElimRM spec_bicond_inst
                        mpM spec_imp_backward
                        return ()
                    bicondIntroM dir1 dir2
                -- Adjoin isSet(B) to complete the canonical property
                adjM isSet_B_proven quantified_bicond_derived
    return ()


-- | The schema that houses 'proveCrossProductDefEquivM'.
-- | The schema stipulates that:
-- | "binaryUnionExistsTheorem" is a required lemma.
crossProductDefEquivSchema :: (HelperConstraints sE s eL m r t) => 
     TheoremSchemaMT () r s Text m ()
crossProductDefEquivSchema = 
    TheoremSchemaMT [] 
                    [binaryUnionExistsTheorem
                    , tupleEqTheorem 2
                    , pairInUniverseTheorem] 
                    proveCrossProductDefEquivM




-- | Constructs the PropDeBr term for the closed theorem of Cartesian product existence.
-- | The theorem is: ∀A ∀B ((isSet A ∧ isSet B) → ∃S (isSet S ∧ ∀x∀y(<x,y>∈S ↔ (x∈A ∧ y∈B))))
crossProductExistsTheorem :: SentConstraints s t => s
crossProductExistsTheorem =
    let
        -- Define integer indices for the template variables (X k).
        -- These will be bound by the quantifiers in nested scopes.
        a_idx = 0 -- Represents set A
        b_idx = 1 -- Represents set B
        s_idx = 2 -- Represents the cross product set S
        x_idx = 3 -- Represents an element x from A
        y_idx = 4 -- Represents an element y from B

        -- Construct the inner part of the formula: <x,y> ∈ S ↔ (x ∈ A ∧ y ∈ B)
        pair_xy = pair (x x_idx) (x y_idx)
        pair_in_S = pair_xy `memberOf` x s_idx
        
        x_in_A = x x_idx `memberOf` x a_idx
        y_in_B = x y_idx `memberOf` x b_idx
        x_in_A_and_y_in_B = x_in_A .&&. y_in_B

        biconditional = x_in_A_and_y_in_B .<->. pair_in_S

        -- Quantify over x and y: ∀x∀y(<x,y> ∈ S ↔ (x ∈ A ∧ y ∈ B))
        quantified_xy_bicond = aX x_idx (aX y_idx biconditional)

        -- Construct the property of the set S: isSet(S) ∧ ∀x∀y(...)
        isSet_S = isSet (x s_idx)
        property_of_S = isSet_S .&&. quantified_xy_bicond

        -- Quantify over S: ∃S (isSet(S) ∧ ∀x∀y(...))
        exists_S = eX s_idx property_of_S

        -- Construct the antecedent of the main implication: isSet(A) ∧ isSet(B)
        isSet_A = isSet (x a_idx)
        isSet_B = isSet (x b_idx)
        antecedent = isSet_A .&&. isSet_B

        -- Construct the main implication
        implication = antecedent .->. exists_S

    in
        -- Universally quantify over A and B to create the final closed theorem.
        -- multiAx [0, 1] is equivalent to aX 0 (aX 1 (...))
        multiAx [a_idx, b_idx] implication



-- | Proves the theorem: 'crossProductExistsTheorem'.
-- | 'crossProductDefEquivTheorem' is a required lemma for this proof.
proveCrossProductExistsM :: (HelperConstraints sE s eL m r t) =>
    ProofGenTStd () r s Text m ()
proveCrossProductExistsM = do
    -- The theorem is universally quantified over two sets, A and B.
    -- We use multiUGM to handle the two ∀ quantifiers.
    multiUGM [(), ()] $ do
        -- Inside the UG, free variables v_B (most recent) and v_A are introduced.
        v_Av_B <- getTopFreeVars 2
        let setB = head v_Av_B
        let setA = v_Av_B!!1
 

        -- Step 1: Define the predicate P(z) for specification.
        let z_idx = 0; x_idx = 1; y_idx = 2; 
                setA_idx = 3; setB_idx = 4
        let universeSet_tmplt = powerSet (powerSet (x setA_idx .\/. x setB_idx))
        -- Define the predicate P(z) as ∃x

        let predicate_P_tmplt = eX x_idx (eX y_idx (
                                  (x z_idx .==. pair (x x_idx) (x y_idx))
                                  .&&. (x x_idx `memberOf` x setA_idx)
                                  .&&. (x y_idx `memberOf` x setB_idx)
                              ))
        predicate_P_txt <- showSentM predicate_P_tmplt
        remarkM $ "Predicate P(z): " <> predicate_P_txt
        (definingProp_of_B, _, (crossProdObj,_,_)) <- builderInstantiateM [setA, setB]
                         [setA_idx, setB_idx] z_idx universeSet_tmplt predicate_P_tmplt

        -- Step 2: Use the theorem about definition equivalence to get the canonical property.

        (thm_equiv_inst1, _) <- uiM setA crossProductDefEquivTheorem
        (thm_equiv_inst2, _) <- uiM setB thm_equiv_inst1
        let asm = isSet setA .&&. isSet setB
        -- Step 3: Prove the main implication by assuming the antecedent.
        runProofByAsmM asm $ do

            (imp_equiv, _) <- mpM thm_equiv_inst2
            mpM imp_equiv

        
            -- Step 4: Construct the target existential statement using the explicit template method.
            let s_idx_final = 0; x_idx_final = 1; y_idx_final = 2
            let element_prop_final = x x_idx_final `memberOf` setA .&&. x y_idx_final `memberOf` setB
            let pair_in_s_final = pair (x x_idx_final) (x y_idx_final) `memberOf` x s_idx_final
            let quantified_bicond_final = aX x_idx_final (aX y_idx_final (element_prop_final .<->. pair_in_s_final))
            let target_property_for_S = isSet (x s_idx_final) .&&. quantified_bicond_final
            let target_existential = eX s_idx_final target_property_for_S

            -- Step 5: Apply Existential Generalization.
            crossProdObjTxt <- showTermM crossProdObj
            remarkM $ "CROSSPRODOBJ IS" <> crossProdObjTxt
            egM crossProdObj target_existential
    return ()


-- | The schema that houses 'proveCrossProductExistsM'.
-- | The schema stipulates that:
-- | "crossProductDefEquivTheorem" is a required lemma.
crossProductExistsSchema :: HelperConstraints sE s eL m r t => 
     TheoremSchemaMT () r s Text m ()
crossProductExistsSchema = 
    TheoremSchemaMT [] [binaryUnionExistsTheorem,crossProductDefEquivTheorem] proveCrossProductExistsM


-- | Helper to instantiate the cross product existence theorem and return the
-- | resulting cartesian product set.
-- | For this helper to work, the theorem defined by 'crossProductExistsTheorem' must be proven
-- | beforehand, which will likely be done in the global context.
crossProductInstantiateM ::  HelperConstraints sE s eL m r t =>
    t -> t -> ProofGenTStd () r s Text m (s, [Int], t)
crossProductInstantiateM setA setB = do
    runProofBySubArgM $ do
        -- This helper relies on isSet(setA) and isSet(setB) being proven in the outer context.

        -- Step 1: Instantiate the 'crossProductExistsTheorem' theorem with the specific sets A and B.
        (instantiated_thm, _) <- multiUIM crossProductExistsTheorem [setA, setB]
        -- The result is the proven proposition: (isSet A ∧ isSet B) → ∃S(...)

        -- Step 2: Prove the antecedent of the instantiated theorem.
        (isSet_A_proven, _) <- repM (isSet setA)
        (isSet_B_proven, _) <- repM (isSet setB)
        (antecedent_proven, _) <- adjM isSet_A_proven isSet_B_proven

        -- Step 3: Use Modus Ponens to derive the existential statement.
        (exists_S_proven, _) <- mpM instantiated_thm

        -- Step 4: Use Existential Instantiation (eiHilbertM) to get the property of the cross product set.
        -- The Hilbert term created here, `crossProdObj`, is definitionally A × B.
        (prop_of_crossProd, _, crossProdObj) <- eiHilbertM exists_S_proven
        
        -- The runProofBySubArgM wrapper will pick up 'prop_of_crossProd' as the 'consequent'
        -- from the Last s writer state. The monadic return value of this 'do' block
        -- will be returned as the 'extraData' component of runProofBySubArgM's result.
        return crossProdObj






-- END CROS PROD EXISTS THEOREM

-- BEGIN STRONG INDUCTION SECTION

-- isRelWellFoundedOn Dom Rel
-- Assumes Rel is a set of pairs, and Dom is the set it's well-founded on.
-- Forall S ((S subset Dom /\ S /= EmptySet) ->
--            Exists x (x In S /\ Forall y (y In S -> not (y Rel x))) )
-- Example usage:
-- let myDomain = Constant "MySet"
-- let myRelation = Constant "MyRelation" -- Assume this is a set of pairs
-- let wellFoundedStatement = isRelWellFoundedOn myDomain myRelation
isRelWellFoundedOn :: SentConstraints s t => t -> t -> IndexTracker s
isRelWellFoundedOn dom rel = do

    idx_S <- newIndex -- Represents the subset S of 'dom'
    idx_x <- newIndex -- Represents the minimal element x in S
    idx_y <- newIndex -- Represents any element y in S for comparison


        -- Antecedent for the main implication: S is a non-empty subset of 'dom'
    let s_is_subset_dom = subset (x idx_S) dom  -- S subset dom
    let s_is_not_empty  = neg ( x idx_S .==. emptySet ) -- S /= EmptySet
    let antecedent_S    = s_is_subset_dom .&&. s_is_not_empty

    -- Consequent: Exists an R-minimal element x in S
    -- x In S
    let x_is_in_S       = x idx_x `memberOf` x idx_S
    -- y Rel x  (pair <y,x> In rel)
    let y_rel_x         = pair (x idx_y) (x idx_x) `memberOf` rel
    -- Forall y (y In S -> not (y Rel x))
    let x_is_minimal_in_S = aX idx_y ( (x idx_y `memberOf` x idx_S) .->. neg y_rel_x )
    -- Exists x (x In S /\ x_is_minimal_in_S)
    let consequent_exists_x = eX idx_x ( x_is_in_S .&&. x_is_minimal_in_S )
    let resultSent = aX idx_S ( antecedent_S .->. consequent_exists_x )
    dropIndices 3
    return resultSent




-- strongInductionPremiseOnRel P_template idx Dom Rel
-- Forall n (n In Dom -> ( (Forall k (k In Dom /\ k Rel n -> P(k))) -> P(n) ) )
-- Example usage:
-- let myProperty = X idx :==: X idx -- P(x) is x=x
-- let myDomain = natSetObj
-- let lessThanRel = builderX 0 -- This needs to be defined, e.g. {<x,y> | x < y & x,y in natSetObj}
--                  (crossProd natSetObj natSetObj) -- Source set for pairs
--                  ( (project 2 0 (X 0)) .<. (project 2 1 (X 0)) ) -- Property X 0 is a pair <a,b> and a < b
-- let premise = strongInductionPremiseOnRel myProperty myDomain lessThanRel

strongInductionPremiseOnRel :: SentConstraints s t => s ->  Int -> t -> IndexTracker s
strongInductionPremiseOnRel p_template idx rel = do
    n_idx <- newIndex -- The main induction variable 'n'
    k_idx <- newIndex -- The universally quantified variable 'k' such that k Rel n

    -- P(n) - using X n_idx for n.
    -- Since P_template uses X idx, we substitute X idx in P_template with X n_idx.
    let p_n = sentSubX idx (x n_idx) p_template

        -- P(k) - using X k_idx for k.
        -- Substitute X idx in P_template with X k_idx.
    let p_k = sentSubX idx (x k_idx) p_template

    -- Inner hypothesis: k Rel n -> P(k)
    -- Here, n is X n_idx and k is X k_idx
    let k_rel_n     = pair (x k_idx) (x n_idx) `memberOf` rel -- k Rel n
    let hyp_antecedent = k_rel_n
    let hyp_body    = hyp_antecedent .->. p_k

    -- Forall k (hyp_body)
    -- This is the "for all predecessors k of n, P(k) holds" part.
    let forall_k_predecessors_hold_P = aX k_idx hyp_body

    -- Inductive Step (IS) for a specific n: (Forall k predecessors...) -> P(n)
    -- Here, n is X n_idx
    let inductive_step_for_n = forall_k_predecessors_hold_P .->. p_n

    -- Body of the main Forall n: (IS_for_n)
    let main_forall_body = inductive_step_for_n
    let resultSent = aX n_idx main_forall_body
    dropIndices 2
    return resultSent


-- | A monadic helper that applies the definition of a well-founded relation.
-- |
-- | Given a domain D, a relation R, and a subset S, this function proves that
-- | S has a minimal element.
-- |
-- | Note: This helper requires that the following premises have already been proven
-- | in the current proof context:
-- |   1. `isRelWellFoundedOn domainD relationR`
-- |   2. `subsetS ⊆ domainD ∧ subsetS ≠ ∅`
-- |
-- | @param subsetS The specific non-empty subset of the domain.
-- | @param domainD The domain over which the relation is well-founded.
-- | @param relationR The well-founded relation.
-- | @return The proven proposition `hasMinimalElement subsetS relationR`.
applyWellFoundednessM :: HelperConstraints sE s eL m r t =>
    t ->  -- subsetS
    t ->  -- domainD
    t ->  -- relationR
    ProofGenTStd () r s Text m ((s, [Int]), (s, [Int]), t)
applyWellFoundednessM subsetS domainD relationR = do
    let builderSubsetTmFree = subsetS `subset` domainD
    let absurd_asm = subsetS ./=. emptySet
    (has_minimal_proven,_,_) <- runProofBySubArgM $ do
        adjM builderSubsetTmFree absurd_asm
        -- We have proven {𝑥₀ ∈ S | ¬P(𝑥₀)} ⊆ S ∧ {𝑥₀ ∈ S | ¬P(𝑥₀)} ≠ ∅ 
        -- Step 1: Formally acknowledge the required premises from the outer context.
        -- The proof will fail if these are not already proven.
        let (wellFoundedProp,_) = runIndexTracker ( 
                 isRelWellFoundedOn domainD relationR

             )      
        -- let wellFoundedProp = isRelWellFoundedOn [] domainD relationR
        (isRelWellFounded_proven, _) <- repM wellFoundedProp
        -- This is the assertion ∀𝑥₂(𝑥₂ ⊆ S ∧ 𝑥₂ ≠ ∅ → ∃𝑥₁(𝑥₁ ∈ 𝑥₂ ∧ ∀𝑥₀(𝑥₀ ∈ 𝑥₂ → 𝑥₀ ≮ 𝑥₁))) 
        let subset_and_nonempty_prop = (subsetS `subset` domainD) .&&. (subsetS ./=. emptySet)
        (subset_and_nonempty_proven, _) <- repM subset_and_nonempty_prop
        -- This is the assertion {𝑥₀ ∈ S | ¬P(𝑥₀)} ⊆ S ∧ {𝑥₀ ∈ S | ¬P(𝑥₀)} ≠ ∅ 

        -- Step 2: The proposition `isRelWellFounded_proven` is definitionally
        -- equivalent to ∀s((s⊆D ∧ s≠∅) → hasMinimalElement s R).
        -- We instantiate this with our specific subset `subsetS`.
        (instantiated_imp, _) <- uiM subsetS isRelWellFounded_proven
        -- `instantiated_imp` is now the proven proposition:
        -- (subsetS ⊆ domainD ∧ subsetS ≠ ∅) → hasMinimalElement subsetS relationR
        -- This is the assertion 
        --      {𝑥₀ ∈ S | ¬P(𝑥₀)} ⊆ S ∧ {𝑥₀ ∈ S | ¬P(𝑥₀)} ≠ ∅  
        --               → ∃𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ∧ ∀𝑥₀(𝑥₀ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → 𝑥₀ ≮ 𝑥₁))

        -- Step 3: Apply Modus Ponens. The antecedent for this implication is
        -- `subset_and_nonempty_proven`, which we acknowledged in Step 1.
        (has_minimal_proven, _) <- mpM instantiated_imp
        
        -- The last proven statement is now `hasMinimalElement subsetS relationR`, which is our goal.
        -- This is the assertion 
        --   ∃𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ∧ ∀𝑥₀(𝑥₀ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → 𝑥₀ ≮ 𝑥₁))

        

        -- The () is the 'extraData' returned by the sub-argument.
        return ()
    (min_assertion, _, min_element) <- eiHilbertM has_minimal_proven
    -- This is the assertion
    --  (min ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ∧ ∀𝑥₀(𝑥₀ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → 𝑥₀ ≮ min))
    (a,b) <- deconstructAdjM min_assertion
    return (a,b, min_element)


-- | A monadic helper that is employed by strongInductionTheoremProgFree.
-- |
-- |
deriveInductiveContradictionM :: HelperConstraints sE s eL m r t =>
    t ->  -- counterexamples
    t ->  -- dom
    t ->  -- rel_obj
    s -> -- induction_premise
    s -> -- spec_prop
    ProofGenTStd () r s Text m (s, [Int], ())
deriveInductiveContradictionM counterexamples dom rel_obj induction_premise spec_prop 
           =
    runProofBySubArgM $ do
        let absurd_asm = counterexamples./=. emptySet
        let rel_is_relation = rel_obj `subset` (dom `crossProd` dom)
        (proves_false,_) <- runProofByAsmM absurd_asm $ do
            -- The assumption is that {𝑥₀ ∈ S | ¬P(𝑥₀)} ≠ ∅
            ((min_element_in_counterexamples,_),
             (counterexample_elems_not_below_min,_),
             min_element) <- applyWellFoundednessM counterexamples dom rel_obj 
            -- we have proven 
            -- 1. min ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ∧ 
            -- 2. ∀𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → 𝑥₁ ≮ min)  
            repM spec_prop
            -- We are asserting the already-proven statement 
            -- IsSet ({𝑥₀ ∈ S | C ≠ 𝑥₀}) ∧ ∀𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ↔ ¬P(𝑥₁) ∧ 𝑥₁ ∈ S)
            (spec_prop_main,_) <- simpRM spec_prop
            -- We have proven ∀𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ↔ ¬P(𝑥₁) ∧ 𝑥₁ ∈ S)
            (spec_prop_inst_min_el,_) <- uiM min_element spec_prop_main
            -- We have proven
            -- min ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ↔ ¬P(min) ∧ min ∈ S
            (spec_prop_inst_min_el_fwd,_) <- bicondElimLM spec_prop_inst_min_el
            -- We have proven
            -- min ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → ¬P(min) ∧ min ∈ S
            (min_element_prop,_) <- mpM spec_prop_inst_min_el_fwd
            -- We have proven
            -- ¬P(min) ∧ min ∈ S
            simpLM min_element_prop
            -- We have proven ¬P(min)
            (induction_premise_on_min,idxA) <- uiM min_element induction_premise
            -- We have proven that ∀𝑥₀(𝑥₀ < min → P(𝑥₀)) → P(min)
            (x,_) <- modusTollensM induction_premise_on_min
            -- We have proven that ¬∀𝑥₀(𝑥₀ < min → P(𝑥₀))
            (exists_statement, idx) <- aNegIntroM x
            -- We have proven that ∃𝑥₀¬(𝑥₀ < min → P(𝑥₀))
            (sub_min_element_prop_pre,_, submin_element) <- eiHilbertM exists_statement 
            -- We have proven that
            --   ¬(submin < min → P(submin))
            (sub_min_element_prop,_) <- negImpToConjViaEquivM sub_min_element_prop_pre
            -- We have proven that
            --   submin < min ∧ ¬P(submin)
            (submin_lt_min,_) <- simpLM sub_min_element_prop
            -- We have proven: submin < min

            (notPsubmin,_) <- simpRM sub_min_element_prop
            -- We have proven: ¬P(submin)
            -- let submin_element_in_n = submin_element `memberOf` natSet
            (rel_prop,_) <- simpRM rel_is_relation
            -- We have proven: ∀𝑥₀(𝑥₀ ∈ (<) → 𝑥₀ ∈ S ⨯ S)
            let xobj = pair submin_element min_element
            (relprop_instance,_) <- uiM xobj rel_prop
            -- We have proven that: submin < min → (submin,min) ∈ S ⨯ S)
            mpM relprop_instance
            -- We have proven that (submin,min) ∈ S ⨯ S

            (domXdomProps,_,domXdom)<- crossProductInstantiateM dom dom
            -- We have proven that:
            -- isSet(S ⨯ S) ∧ ∀𝑥₁(∀𝑥₀(𝑥₁ ∈ S ∧ 𝑥₀ ∈ S ↔ (𝑥₁,𝑥₀) ∈ S ⨯ S))
            (crossProdProp, _) <- simpRM domXdomProps
            -- We have proven that: ∀𝑥₁(∀𝑥₀(𝑥₁ ∈ S ∧ 𝑥₀ ∈ S ↔ (𝑥₁,𝑥₀) ∈ S ⨯ S))
            (crossProdPropInst,_) <- multiUIM crossProdProp [submin_element,min_element]
            -- We have proven that: min ∈ S ∧ submin ∈ S ↔ (min,submin) ∈ S ⨯ S)
            (crossProdPropInstFwd,_) <- bicondElimRM crossProdPropInst
            -- We have proven that: (min,submin) ∈ S ⨯ S → min ∈ S ∧ submin ∈ S

            (min_in_s_and_submin_in_s, _) <- mpM crossProdPropInstFwd
            -- We have proven that: min ∈ S ∧ submin ∈ S
            (min_in_s,_) <- simpLM min_in_s_and_submin_in_s
            -- We have proven that: min ∈ S
            adjM notPsubmin min_in_s
            -- We have proven that: ¬P(submin) ∧ min ∈ S
            repM spec_prop_main
            -- We are reasserting: ∀𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ↔ ¬P(𝑥₁) ∧ 𝑥₁ ∈ S)
            (spec_prop_inst_submin_el,_) <- uiM submin_element spec_prop_main
            -- We have proven that submin ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} ↔ ¬P(submin) ∧ submin ∈ S

            (spec_prop_inst_submin_el_bwd,_) <- bicondElimRM spec_prop_inst_submin_el
            -- We have proven that: ¬P(submin) ∧ submin ∈ S → submin ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)}
            final_ante <- mpM spec_prop_inst_submin_el_bwd
            -- We have proven that: submin ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)}
            repM counterexample_elems_not_below_min
            -- We are reasserting: ∀𝑥₁(𝑥₁ ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → 𝑥₁ ≮ min)
            (final_imp,_) <- uiM submin_element counterexample_elems_not_below_min
            -- We have proven that: submin ∈ {𝑥₀ ∈ S | ¬P(𝑥₀)} → submin ≮ min
            (not_submin_lt_min,_) <- mpM final_imp
            -- We have proven that: submin ≮ min
            repM submin_lt_min
            -- We are reasserting: submin < min
            contraFM submin_lt_min
            -- We have proven: ⊥
        return ()


strongInductionTheorem :: SentConstraints s t =>
               [Int] -> Int -> t -> s -> s
strongInductionTheorem outerTemplateIdxs idx dom_template p_template =
    let 
        (theorem_body_tmplt,_) = runIndexTracker (do
            setTemplateVarBaseFromSet (idx:outerTemplateIdxs)
            rel_idx <- newIndex
            -- The theorem states:
            -- For any set S and property P, if there exists a well-founded relation < on S such that
            -- the strong induction premise holds for < over S, then P holds for all elements of S.
            wellFoundedExp <- isRelWellFoundedOn dom_template (x rel_idx)
            strongInductionExp <- strongInductionPremiseOnRel p_template idx (x rel_idx)
            let theorem_body_tmplt = 
                    isSet dom_template .&&.
                    eX rel_idx (
                           (x rel_idx `subset` (dom_template `crossProd` dom_template))
                               .&&. wellFoundedExp
                                .&&. strongInductionExp
                       )
                           .->. 
                    aX idx ( (x idx `memberOf` dom_template) .->. p_template)
            dropIndices 1
            return theorem_body_tmplt
            )
        theorem_body = multiAx outerTemplateIdxs theorem_body_tmplt
    in
        theorem_body

strongInductionTheoremProgFree::HelperConstraints sE s eL m r t => 
               Int -> t -> s -> ProofGenTStd () r s Text m (s,[Int])
strongInductionTheoremProgFree idx dom p_pred = do
    let (asmMain,_) = runIndexTracker (do
        setTemplateVarBaseFromSet [idx]
        rel_idx <- newIndex
        wellFoundedExp <- isRelWellFoundedOn dom (x rel_idx)
        strongInductionExp <- strongInductionPremiseOnRel p_pred idx (x rel_idx)
        let asmMain = eX rel_idx (
                       x rel_idx `subset` (dom `crossProd` dom)
                           .&&. wellFoundedExp
                            .&&. strongInductionExp)
        dropIndices 1
        return asmMain
        )    
    let (anti_spec_prop,anti_counterexamples) = builderPropsFree idx dom p_pred
    let (spec_prop, counterexamples) = builderPropsFree idx dom (neg p_pred)
    let builderSubsetTmFree = builderSubsetTheorem [] idx dom (neg p_pred)
    let specAntiRedundancyTmFreeConditional = specAntiRedundancyTheorem [] idx dom p_pred
    (specAntiRedundancyTmFree,_) <- mpM specAntiRedundancyTmFreeConditional
    runProofByAsmM asmMain $ do
        (asm_after_ei,_,rel_obj) <- eiHilbertM asmMain
        -- We have established: (<) ⊆ S ⨯ S ∧ ∀𝑥₂(𝑥₂ ⊆ S ∧ 𝑥₂ ≠ ∅ → ∃𝑥₁(𝑥₁ ∈ 𝑥₂ ∧ ∀𝑥₀(𝑥₀ ∈ 𝑥₂ → 𝑥₀ ≮ 𝑥₁))) 
        --                                     ∧ ∀𝑥₁(∀𝑥₀(𝑥₀ < 𝑥₁ → P(𝑥₀)) → P(𝑥₁))
        -- I.e. (<) is a relation over S,
        -- S is well-founded on (<),
        -- and the induction premise holds for (<) over S.
        (rel_is_relation,rel_is_relation_idx) <- simpLM asm_after_ei
        -- We have established that
        --  (<) ⊆ S ⨯ S
        (bAndC,_) <- simpRM asm_after_ei
        (well_founded,well_founded_idx) <- simpLM bAndC
        -- We have established that
        --  ∀𝑥₂(𝑥₂ ⊆ S ∧ 𝑥₂ ≠ ∅ → ∃𝑥₁(𝑥₁ ∈ 𝑥₂ ∧ ∀𝑥₀(𝑥₀ ∈ 𝑥₂ → 𝑥₀ ≮ 𝑥₁))) 
        -- This is the assertion that S is well-founded on (<).
        (induction_premise,induction_premise_idx) <- simpRM bAndC
        -- We have established that
        -- ∀𝑥₁(∀𝑥₀(𝑥₀ < 𝑥₁ → P(𝑥₀)) → P(𝑥₁))
        -- This is the induction premise.
        remarkM $   (pack . show) rel_is_relation_idx <> " asserts that rel is a relation over S.\n" 
                    <> (pack . show) well_founded_idx <> " asserts that rel is well-founded over S.\n"
                    <> (pack . show) induction_premise_idx <> " asserts that the induction premise holds for S"
                
        (proves_false,_,()) <- deriveInductiveContradictionM counterexamples dom rel_obj 
                    induction_premise spec_prop
        -- We have proven that {𝑥₀ ∈ S | ¬P(𝑥₀)} ≠ ∅ → ⊥
        (double_neg,_) <- absurdM proves_false
        -- We have proven that ¬¬{𝑥₀ ∈ S | ¬P(𝑥₀)} = ∅
        (final_generalization_set_version,_) <- doubleNegElimM double_neg
        -- We have proven that {𝑥₀ ∈ S | ¬P(𝑥₀)} = ∅
        (final_imp,_) <- bicondElimLM specAntiRedundancyTmFree
        -- We have proven that {𝑥₀ ∈ S | ¬P(𝑥₀)} = ∅ → ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀))
                
        mpM final_imp
                -- We have proven that ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀))


strongInductionTheoremProg:: HelperConstraints sE s eL m r t => 
               [Int] -> Int -> t -> s -> ProofGenTStd () r s Text m ()
strongInductionTheoremProg outerTemplateIdxs idx dom_template p_template = do



    let builderSubsetTmInstance = builderSubsetTheorem outerTemplateIdxs idx dom_template (neg p_template)
    let specAntiRedundancyTmInstance = specAntiRedundancyTheorem outerTemplateIdxs idx dom_template p_template
    
    txt <- showSentM (strongInductionTheorem outerTemplateIdxs idx dom_template p_template)
    remarkM $ "Strong Induction Theorem to be proven: " <> txt


    multiUGM (replicate (length outerTemplateIdxs) ()) $ do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.
        instantiationTermsRev <- getTopFreeVars (length outerTemplateIdxs)
        let instantiationTerms = reverse instantiationTermsRev



        (_,_,(_,dom,_)) <- builderInstantiateM instantiationTerms outerTemplateIdxs idx 
                          dom_template (neg p_template)
        (_,_,(_,_,p_pred)) <- 
                          builderInstantiateM instantiationTerms outerTemplateIdxs idx dom_template p_template



        multiUIM builderSubsetTmInstance instantiationTerms
        multiUIM specAntiRedundancyTmInstance instantiationTerms


        let isSetDom = isSet dom
        (main_imp, _) <- runProofByAsmM isSetDom $ do
            strongInductionTheoremProgFree idx dom p_pred
        let (asmMain,_) = runIndexTracker (do
            setTemplateVarBaseFromSet [idx]
            rel_idx <- newIndex
            wellFoundedExp <- isRelWellFoundedOn dom (x rel_idx)
            strongInductionExp <- strongInductionPremiseOnRel p_pred idx (x rel_idx)
            let asmMain = eX rel_idx (
                           x rel_idx `subset` (dom `crossProd` dom)
                               .&&. wellFoundedExp
                                .&&. strongInductionExp)
            dropIndices 1
            return asmMain
            )
        let full_asm = isSetDom .&&. asmMain
        runProofByAsmM full_asm $ do
            (isSet_dom,_) <- simpLM full_asm
            (sub_imp,_) <- mpM main_imp
            (inductive_asm,_) <- simpRM full_asm
            mpM sub_imp
    return ()



strongInductionTheoremMSchema :: HelperConstraints sE s eL m r t => 
     [Int] -> Int -> t -> s -> TheoremSchemaMT () r s Text m ()
strongInductionTheoremMSchema outerTemplateIdxs spec_var_idx dom p_template= 
    let
      dom_tmplt_consts = extractConstsTerm dom
      p_tmplt_consts = extractConstsSent p_template
      all_consts = dom_tmplt_consts `Set.union` p_tmplt_consts
      typed_consts = Prelude.map (, ()) (Data.Set.toList all_consts) 
    in
      TheoremSchemaMT typed_consts [crossProductExistsTheorem
                              , builderSubsetTheorem outerTemplateIdxs spec_var_idx dom (neg p_template)
                              , specAntiRedundancyTheorem outerTemplateIdxs spec_var_idx dom p_template
                             ] (strongInductionTheoremProg outerTemplateIdxs spec_var_idx dom p_template)


-- END STRONG INDUCTION SECTION


data MetaRuleError s where
   MetaRuleErrTupleSubstNotAnEquality :: s -> MetaRuleError s
   MetaRuleErrTupleSubstIncorrectLHS :: Int -> s-> MetaRuleError s
   MetaRuleErrTupleSubstIncorrectRHS :: Int -> s -> MetaRuleError s

   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)


