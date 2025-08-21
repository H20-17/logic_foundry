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
    binaryIntersectionInstantiateM
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
   HelperConstraints(..))
import qualified RuleSets.PredLogic.Core as PREDL
import RuleSets.ZFC.Core
import RuleSets.BaseLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PredLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.PropLogic.Helpers hiding
     (MetaRuleError(..))
import RuleSets.ZFC.Helpers
import Text.XHtml (target)

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



--data MetaRuleError s where
--   MetaRuleErrNotClosed :: s -> MetaRuleError s
--   MetaRuleErrFreeVarsQuantCountMismatch :: MetaRuleError s

--   deriving(Show,Typeable)


-- instance (Show s, Typeable s) => Exception (MetaRuleError s)


