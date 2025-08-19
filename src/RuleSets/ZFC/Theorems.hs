{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
module RuleSets.ZFC.Theorems
(
    unionEquivTheorem,
    binaryUnionExistsTheorem,
    binaryUnionExistsSchema,
    binaryUnionInstantiateM,
    proveUnionIsSetM,
    unionWithEmptySetSchema,
    unionWithEmptySetTheorem,
    specRedundancyTheorem
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
        
--NEED MORE STUFF HERE
--END SPEC REDUNDANCY


--data MetaRuleError s where
--   MetaRuleErrNotClosed :: s -> MetaRuleError s
--   MetaRuleErrFreeVarsQuantCountMismatch :: MetaRuleError s

--   deriving(Show,Typeable)


-- instance (Show s, Typeable s) => Exception (MetaRuleError s)


