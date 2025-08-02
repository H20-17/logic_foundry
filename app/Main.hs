{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DoAndIfThenElse #-}


module Main where

import Data.Monoid ( Last(..) )
import Control.Monad ( foldM, unless, forM, guard )
import Control.Monad.RWS
    ( MonadTrans(..),
      MonadReader(ask, local),
      MonadState(put, get),
      MonadWriter(tell),
      RWST(..) )
import Data.Set (Set, fromList,toList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map, toList )
import Data.Maybe ( isNothing )
import Control.Applicative ( Alternative((<|>)) )
import Control.Arrow ( ArrowChoice(left) )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadCatch(..), MonadThrow(..), Exception )
import GHC.Stack.Types ( HasCallStack )
import Data.Data (Typeable)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import StdPattern
import RuleSets.BaseLogic.Core hiding
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..))
import qualified RuleSets.BaseLogic.Core as BASE
import RuleSets.PropLogic hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..))
import qualified RuleSets.PropLogic as PL
import RuleSets.PredLogic hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..))
import qualified RuleSets.PredLogic as PRED
import qualified RuleSets.ZFC as ZFC
import RuleSets.ZFC
    ( axiomOfChoiceM,specificationM, MetaRuleError(..), powerSetAxiomM)
import Langs.BasicUntyped
import Distribution.Compat.Lens (set)
import RuleSets.BaseLogic.Helpers



testTheoremMSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => TheoremSchemaMT () [PredRuleDeBr] PropDeBr Text m ()
testTheoremMSchema = TheoremSchemaMT  [("N",())] [z1,z2] theoremProg 
  where
    z1 = aX 99 ((X 99 `In` Constant "N") :&&: (X 99 :<=: Integ 10) :->: (X 99 :<=: Integ 0))
    z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ 0))


-- | Constructs the PropDeBr term for the theorem stating that for any set x,
-- | the union of x with the empty set is x itself.
-- |
-- | Theorem: ∀x (isSet x → (x ∪ ∅ = x))
unionWithEmptySetTheorem :: PropDeBr
unionWithEmptySetTheorem =
    let
        x_idx = 0
        setX = X x_idx
        
        -- The equality: x U emptySet == x
        equality = (setX .\/. EmptySet) .==. setX
        
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
proveUnionWithEmptySetM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveUnionWithEmptySetM = do
    -- Prove the theorem: ∀x (isSet x → x ∪ ∅ = x)
    multiUGM [()] do
        -- Inside UG, a free variable 'v' is introduced for 'x'.
        v <- getTopFreeVar
        
        -- Prove the implication by assuming the antecedent.
        runProofByAsmM (isSet v) do
            -- Now, `isSet v` is a proven assumption.

            -- Step 1: Define the objects we are working with.
            let unionObj = v .\/. EmptySet

            -- Step 2: Prove the necessary `isSet` properties for Extensionality.
            -- We already have `isSet v` by assumption.
            -- We need to prove `isSet (v ∪ ∅)`.

            -- (isSet_EmptySet_axiom, _) <- ZFC.emptySetAxiomM

            (forall_not_in_empty, _) <- ZFC.emptySetAxiomM

            -- (isSet_EmptySet_proven, _) <- simpLM isSet_EmptySet_axiom
            
            (isSet_EmptySet_proven, _) <- ZFC.emptySetNotIntM

            -- proveUnionIsSetM requires isSet v and isSet ∅ to be proven.
            (isSet_unionObj_proven, _) <- proveUnionIsSetM v EmptySet

            -- Step 3: Prove ∀y (y ∈ v ↔ y ∈ (v ∪ ∅))
            (forall_bicond, _) <- runProofByUGM () do
                y <- getTopFreeVar

               -- Direction 1: y ∈ v → y ∈ (v ∪ ∅)
                (dir1, _) <- runProofByAsmM (y `In` v) do
                    -- This is a simple Disjunction Introduction.
                    disjIntroLM (y `In` v) (y `In` EmptySet)

                    -- Now, use the definition of union to get back to y ∈ (v ∪ ∅)
                    (def_prop_union, _, _) <- binaryUnionInstantiateM v EmptySet
                    (forall_union_bicond, _) <- simpRM def_prop_union
                    (inst_union_bicond, _) <- uiM y forall_union_bicond
                    (imp_to_union, _) <- bicondElimRM inst_union_bicond
                    
                    -- Apply Modus Ponens to get the final conclusion of this subproof.
                    mpM imp_to_union
                    return ()

                -- To prove the biconditional, we prove each direction.
                -- Direction 2: y ∈ (v ∪ ∅) → y ∈ v
                (dir2, _) <- runProofByAsmM (y `In` unionObj) do
                    -- Get the defining property of the union.
                    (def_prop_union, _, _) <- binaryUnionInstantiateM v EmptySet
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
            (ext_axiom, _) <- ZFC.extensionalityAxiomM
            (ext_inst, _) <- multiUIM ext_axiom [v, unionObj]
            (adj1,_) <- adjM isSet_unionObj_proven forall_bicond
            (full_antecedent,_) <- adjM (isSet v) adj1

            mpM ext_inst

    return ()


-- | The schema that houses the proof for 'unionWithEmptySetTheorem'.
-- | It declares its dependencies on other theorems.
unionWithEmptySetSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
     TheoremSchemaMT () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
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

-- | Constructs the PropDeBr term for the theorem stating that for any set S and predicate P,
-- | an element x is in S if and only if it's in the part of S satisfying P or the part not satisfying P.
-- |
-- | Theorem: ∀(params...)∀x ( x∈S(params) ↔ ( (x∈S(params) ∧ P(x,params)) ∨ (x∈S(params) ∧ ¬P(x,params)) ) )
partitionEquivTheorem :: [Int] -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
partitionEquivTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- The left-hand side of the biconditional: x ∈ S
        lhs = X spec_var_idx `In` source_set_template

        -- The right-hand side of the biconditional: (x∈S ∧ P(x)) ∨ (x∈S ∧ ¬P(x))
        -- Note that p_template already contains X spec_var_idx for the variable x.
        x_in_S_and_P = p_template :&&: (X spec_var_idx `In` source_set_template) 
        x_in_S_and_NotP = (neg p_template) :&&: (X spec_var_idx `In` source_set_template) 
        rhs = x_in_S_and_P :||: x_in_S_and_NotP

        -- The core biconditional for a specific x and specific params
        biconditional = lhs :<->: rhs

        -- Quantify over the main variable x
        forall_x_bicond = aX spec_var_idx biconditional

    in
        -- Universally quantify over all parameters to create the final closed theorem.
        multiAx outerTemplateIdxs forall_x_bicond




-- | This function composes the following sentence:
-- | ∀𝑥₂(∀𝑥₁(∀𝑥₀(𝑥₁ = 𝑥₀ → 𝑥₂ ∈ 𝑥₁ → 𝑥₂ ∈ 𝑥₀)))
eqSubstTheorem :: PropDeBr
eqSubstTheorem = 
    let
       eq_subst_thm_tmplt = (X 0 :==: X 1) :->: ((X 2 `In` X 0) :->: (X 2 `In` X 1))
       eq_subst_thm = multiAx [2,0,1] eq_subst_thm_tmplt
    in
       eq_subst_thm


-- | Constructs the PropDeBr term for the theorem stating that a specification
-- | over a set S with predicate P is redundant (i.e., results in S) if and only if
-- | all elements of S already satisfy P.
-- |
-- | Theorem: ∀(params...) (isSet(S(params)) → ({x ∈ S(params) | P(x,params)} = S(params) ↔ ∀x(x ∈ S(params) → P(x,params))))
specRedundancyTheorem :: [Int] -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
specRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- Part 1: The LHS of the biconditional: {x ∈ S | P(x)} = S
        builderSet = builderX spec_var_idx source_set_template p_template
        lhs_equality = builderSet :==: source_set_template

        -- Part 2: The RHS of the biconditional: ∀x(x ∈ S → P(x))
        -- Note that p_template already uses X spec_var_idx for the variable x.
        x_in_S = X spec_var_idx `In` source_set_template
        implication_body = x_in_S :->: p_template
        rhs_forall = aX spec_var_idx implication_body

        -- Combine the two sides into the core biconditional
        biconditional = lhs_equality :<->: rhs_forall

        -- Construct the antecedent for the main implication: isSet(S)
        antecedent = isSet source_set_template

        -- Form the main implication for the body of the theorem
        implication = antecedent :->: biconditional

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
proveSpecRedundancyMFree :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    ObjDeBr ->  -- sourceSet: The instantiated source set S
    PropDeBr -> -- p_tmplt: The instantiated predicate P(x)
    -- PropDeBr -> -- def_prop_B: The proven defining property of the builder set
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr,[Int])
proveSpecRedundancyMFree spec_var_idx sourceSet p_tmplt 
         -- def_prop_B 
         = do
    let (def_prop_B, builderSet) = builderPropsFree spec_var_idx sourceSet p_tmplt
    let builderSubsetTmInst = builderSubsetTheorem [] spec_var_idx sourceSet p_tmplt
    (resultProp,idx,_) <- runProofBySubArgM $ do
        repM (isSet sourceSet) -- We assert this here to emphasize that it should already be proven in the context.
        repM def_prop_B -- We assert this here to emphasize that {x ∈ S | P(x)} has already been instantiated with builderInstantiateM.
        repM eqSubstTheorem -- We assert this here to emphasize that eqSubstTheorem has already been asserted as a lemma.
        repM builderSubsetTmInst -- We assert this here to emphasize that the instantiated builder subset theorem should
                                 -- already be proven in the context.

        -- The proof is a biconditional, so we prove each direction separately.

        -- == Direction 1: ({x ∈ S | P(x)} = S) → (∀x(x ∈ S → P(x))) ==
        (dir1_implication, _) <- runProofByAsmM (builderSet :==: sourceSet) do
            -- Assume B = S. Goal: ∀x(x ∈ S → P(x))
            runProofByUGM () do
                v <- getTopFreeVar
                -- Goal: v ∈ S → P(v)
                runProofByAsmM (v `In` sourceSet) do
                    -- The property of equality substitution states: S=B → (v∈S → v∈B)
                
                    -- Instantiate with v, S, and B in the correct order.
                    (inst_thm, _) <- multiUIM eqSubstTheorem [v, sourceSet, builderSet]

                    -- We need to prove S=B from B=S. This requires symmetry of equality.
                    (s_eq_b, _) <- eqSymM (builderSet .==. sourceSet)
                    --(symm_inst, _) <- multiUIM symm_thm [builderSet, sourceSet]
                    -- (s_eq_b, _) <- mpM symm_inst

                    -- Now apply MP twice to get v ∈ B
                    (imp_from_eq, _) <- mpM inst_thm
                    (v_in_B, _) <- mpM imp_from_eq

                    -- Now that we have `v ∈ B`, we can use the defining property of B to get P(v).
                    (forall_bicond_B, _) <- simpRM def_prop_B
                    (inst_bicond_B, _) <- uiM v forall_bicond_B
                    (imp_B_to_P, _) <- bicondElimLM inst_bicond_B
                    (p_and_v_in_s, _) <- mpM imp_B_to_P
                    (p_of_v, _) <- simpLM p_and_v_in_s
                    return ()

        -- == Direction 2: (∀x(x ∈ S → P(x))) → ({x ∈ S | P(x)} = S) ==
        (dir2_implication, _) <- runProofByAsmM (aX spec_var_idx ((X spec_var_idx `In` sourceSet) :->: p_tmplt)) do
            -- Assume ∀x(x ∈ S → P(x)). Goal: B = S.
            (isSet_B, _) <- simpLM builderSubsetTmInst

            (forall_bicond_sets, _) <- runProofByUGM () do
                v <- getTopFreeVar
                (forall_subset_imp, _) <- simpRM builderSubsetTmInst

                (imp_B_to_S, _) <- uiM v forall_subset_imp
                (imp_S_to_B, _) <- runProofByAsmM (v `In` sourceSet) do
                    let forall_S_implies_P = aX spec_var_idx ((X spec_var_idx `In` sourceSet) :->: p_tmplt)
                    (instantiated_imp, _) <- uiM v forall_S_implies_P
                    (p_of_v, _) <- mpM instantiated_imp
                    (v_in_S_and_P, _) <- adjM (v `In` sourceSet) p_of_v
                    (forall_bicond_B, _) <- simpRM def_prop_B
                    (inst_bicond_B, _) <- uiM v forall_bicond_B
                    (imp_to_B, _) <- bicondElimRM inst_bicond_B
                    adjM p_of_v (v `In` sourceSet)
                    mpM imp_to_B
                    return ()
                bicondIntroM imp_B_to_S imp_S_to_B
            (ext_axiom, _) <- ZFC.extensionalityAxiomM
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
proveSpecRedundancyTheoremM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveSpecRedundancyTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters specified in outerTemplateIdxs.
    multiUGM (replicate (length outerTemplateIdxs) ()) do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.
        freeVarCount <- getFreeVarCount
        let instantiationTerms = Prelude.map V [0 .. freeVarCount - 1]

        -- Establish the properties of the builderSet here
        -- and acquire the instantiated templates with the free variables for this specific proof context.
        (_,_,(_,sourceSet,p_tmplt)) <- builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template p_template
        builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template (neg p_template)
        let lemma2 = builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template p_template
        multiUIM lemma2 instantiationTerms
        

        -- Step 2: Prove the main implication by assuming its antecedent, `isSet sourceSet`.
        runProofByAsmM (isSet sourceSet) do
            



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
specRedundancySchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    TheoremSchemaMT () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
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
        typed_consts = zip (Data.Set.toList all_consts) (repeat ())
    in
        TheoremSchemaMT {
            lemmasM = [eqSubstTheorem, 
                       builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template p_template],
            proofM = proof_program,
            constDictM = typed_consts
        }



disjointSubsetIsEmptyTheorem :: PropDeBr
disjointSubsetIsEmptyTheorem = aX 0 (aX 1 (isSet (X 0) :&&: (X 0 ./\. X 1) :==: EmptySet :&&: (X 1 `subset` X 0) :->: X 1 :==: EmptySet))


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
proveDisjointSubsetIsEmptyM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveDisjointSubsetIsEmptyM = do
    -- Prove: ∀a ∀b (isSet(a) ∧ a ∩ b = ∅ ∧ b ⊆ a → b=∅)
    multiUGM [(), ()] do
        -- Inside UG, free variables for a and b are introduced (v_a, v_b).
        v_b <- getTopFreeVar
        context <- ask
        let v_a_idx = (length . freeVarTypeStack) context - 2
        let v_a = V v_a_idx

        -- Prove the main implication by assuming the antecedent.
        let antecedent = isSet v_a :&&: ((v_a ./\. v_b) :==: EmptySet) :&&: (v_b `subset` v_a)
        runProofByAsmM antecedent do
            -- Step 1: Deconstruct the antecedent assumption.
            (isSet_a_proven, _) <- simpLM antecedent
            (rest1,_) <- simpRM antecedent
            (intersection_is_empty, subset_b_a) <- simpLM rest1
            (subset_b_a,_) <- simpRM rest1 

            -- Step 2: Prove ∀x(¬(x ∈ v_b)) by contradiction.
            (forall_not_in_b, _) <- runProofByUGM () do
                x <- getTopFreeVar
                (x_in_b_implies_false, _) <- runProofByAsmM (x `In` v_b) do
                    -- From b ⊆ a and x ∈ b, we get x ∈ a.
                    (isSet_b, _) <- simpLM subset_b_a
                    (forall_imp, _) <- simpRM subset_b_a
                    (x_in_b_implies_x_in_a, _) <- uiM x forall_imp
                    (x_in_a, _) <- mpM x_in_b_implies_x_in_a

                    -- From x ∈ a and x ∈ b, we get x ∈ (a ∩ b).
                    (def_prop_inter, _, _) <- binaryIntersectionInstantiateM v_a v_b
                    (forall_inter_bicond, _) <- simpRM def_prop_inter
                    (inst_inter_bicond, _) <- uiM x forall_inter_bicond
                    (imp_to_inter, _) <- bicondElimRM inst_inter_bicond
                    (x_in_a_and_b, _) <- adjM x_in_a (x `In` v_b)
                    (x_in_intersection, _) <- mpM imp_to_inter

                    -- From a ∩ b = ∅ and x ∈ (a ∩ b), we get x ∈ ∅.
                    let eqSubstTmplt = x `In` X 0
                    --(x_in_empty, _) <- eqSubstM 1 (X 0 :==: X 1 :->: ((x `In` X 0) :->: (x `In` X 1)))
                    --                         [v_a ./\. v_b, EmptySet]
                    (x_in_empty, _) <- eqSubstM 0 eqSubstTmplt intersection_is_empty


                    -- But we know from the empty set axiom that ¬(x ∈ ∅).
                    (forall_not_in_empty, _) <- ZFC.emptySetAxiomM
                    (not_x_in_empty, _) <- uiM x forall_not_in_empty

                    -- This is a contradiction.
                    contraFM x_in_empty
                
                -- From (x ∈ b → False), we derive ¬(x ∈ b).
                absurdM x_in_b_implies_false

            -- Step 3: Use the result from Step 2 to prove ∀x(x ∈ b ↔ x ∈ ∅).
            (forall_bicond, _) <- runProofByUGM () do
                x <- getTopFreeVar
                (not_in_b, _) <- uiM x forall_not_in_b
                (forall_not_in_empty, _) <- ZFC.emptySetAxiomM
                (not_in_empty, _) <- uiM x forall_not_in_empty
                
                (dir1, _) <- runProofByAsmM (neg (x `In` v_b)) 
                                            (repM not_in_empty)

                (dir2, _) <- runProofByAsmM (neg (x `In` EmptySet)) 
                                   (repM not_in_b)
                (bicond_of_negs,_) <- bicondIntroM dir1 dir2

                -- Use our tautology helper to get the positive biconditional.
                negBicondToPosBicondM bicond_of_negs

            -- Step 4: Apply the Axiom of Extensionality to prove b = ∅.
            (isSet_b, _) <- simpLM subset_b_a
            (isSet_empty, _) <- ZFC.emptySetNotIntM
            (ext_axiom, _) <- ZFC.extensionalityAxiomM
            (ext_inst, _) <- multiUIM ext_axiom [v_b, EmptySet]
            
            (adj1, _) <- adjM isSet_empty forall_bicond
            (full_antecedent, _) <- adjM isSet_b adj1
            
            mpM ext_inst
            return ()

    return ()

-- | The schema that houses the proof for 'disjointSubsetIsEmptyTheorem'.
-- | It declares its dependencies on other theorems.
disjointSubsetIsEmptySchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
     TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
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



-- | Constructs the PropDeBr term for the theorem stating that a specification
-- | over a set S with predicate ¬P is identical with the empty set if and only if
-- | all elements of S already satisfy P.
-- |
-- | Theorem: ∀(params...) (isSet(S(params)) → ({x ∈ S(params) | ¬P(x,params)} = ∅ ↔ ∀x(x ∈ S(params) → P(x,params))))
specAntiRedundancyTheorem :: [Int] -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
specAntiRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- Part 1: The LHS of the biconditional: {x ∈ S | ¬P(x)} = ∅
        builderSet = builderX spec_var_idx source_set_template (neg p_template)
        lhs_equality = builderSet :==: EmptySet

        -- Part 2: The RHS of the biconditional: ∀x(x ∈ S → P(x))
        -- Note that p_template already uses X spec_var_idx for the variable x.
        x_in_S = X spec_var_idx `In` source_set_template
        implication_body = x_in_S :->: p_template
        rhs_forall = aX spec_var_idx implication_body

        -- Combine the two sides into the core biconditional
        biconditional = lhs_equality :<->: rhs_forall

        -- Construct the antecedent for the main implication: isSet(S)
        antecedent = isSet source_set_template

        -- Form the main implication for the body of the theorem
        implication = antecedent :->: biconditional

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
proveSpecAntiRedundancyMFree :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    ObjDeBr ->  -- sourceSet: The instantiated source set S
    PropDeBr -> -- p_tmplt: The instantiated predicate P(x)
    -- PropDeBr -> -- def_prop_B: The proven defining property of the builder set
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr,[Int])
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
        let cond_ls = negBuilderSet :==: EmptySet
        (dir1_implication, _) <- runProofByAsmM cond_ls do
            -- Assume {x ∈ S | ¬P(x)} = ∅. Goal: ∀x(x ∈ S → P(x)).
            simpLM builderSrcPartitionTmInstMain
            -- We have now proven: S = ({𝑥₀ ∈ S | P(𝑥₀)} ∪ {𝑥₀ ∈ S | ¬P(𝑥₀)})
            let substTmplt = sourceSet :==: (builderSet .\/. X 0)
            eqSubstM 0 substTmplt cond_ls
            -- We have now proven: S = ({𝑥₀ ∈ S | P(𝑥₀)} ∪ ∅)
            (unionWithEmptySetTmInstance,_) <- uiM builderSet unionWithEmptySetTheorem
            -- We have now proven:  IsSet ({𝑥₀ ∈ S | P(𝑥₀)}) → ({𝑥₀ ∈ S | P(𝑥₀)} ∪ ∅) = {𝑥₀ ∈ S | P(𝑥₀)} 
            (negBuilderSet_isSet,_) <- simpLM spec_prop
            -- We have now proven: IsSet  ({𝑥₀ ∈ S | P(𝑥₀)}) 
            (actual_union_w_emptyset,_) <- mpM unionWithEmptySetTmInstance
            -- We have now proven: ({𝑥₀ ∈ S | P(𝑥₀)} ∪ ∅) = {𝑥₀ ∈ S | P(𝑥₀)}
            let substTmplt = sourceSet .==. X 0
            (specRedCond,_) <- eqSubstM 0 substTmplt actual_union_w_emptyset
            -- We have proven: S = {𝑥₀ ∈ S | 𝑥₀ = 𝑥₀}
            eqSymM specRedCond
            -- We have now proven: {𝑥₀ ∈ S | P(𝑥₀)} = S
            (final_imp,_) <- bicondElimLM specRedundancyTmInstMain
            -- We have now proven: {𝑥₀ ∈ S | P(𝑥₀)} = S → ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀))
            mpM final_imp
            -- We have now proven: ∀𝑥₀(𝑥₀ ∈ S → P(𝑥₀))

        -- == Direction 2: (∀x(x ∈ S → P(x))) → ({x ∈ S | ¬P(x)} = ∅) ==
        let cond_rs = aX spec_var_idx ((X spec_var_idx `In` sourceSet) :->: p_tmplt)
        (dir2_implication,_) <- runProofByAsmM cond_rs do
            -- Assume ∀x(x ∈ S → P(x)). Goal: {x ∈ S | ¬P(x)} = ∅.
            (specRedImpBwd,_) <- bicondElimRM specRedundancyTmInstMain
            (builderSetEqSrcSet,_) <- mpM specRedImpBwd
            -- We have now proven: {x ∈ S | P(x)} = S

            
            (partDisjoint,_) <- simpRM builderSrcPartitionTmInstMain
            -- We have now proven: ({𝑥₀ ∈ S | P(𝑥₀)} ∩ {𝑥₀ ∈ S | ~P(𝑥₀)}) = ∅
            let eqSubstTemplate = (X 0 ./\. negBuilderSet) :==: EmptySet
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
proveSpecAntiRedundancyTheoremM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveSpecAntiRedundancyTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters specified in outerTemplateIdxs.
    multiUGM (replicate (length outerTemplateIdxs) ()) do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.
        freeVarCount <- getFreeVarCount
        let instantiationTerms = Prelude.map V [0 .. freeVarCount - 1]

        -- Establish the properties of the builderSet here
        -- and acquire the instantiated templates with the free variables for this specific proof context.
        (_,_,(_,sourceSet,p_tmplt)) <- builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template p_template
        builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_idx source_set_template (neg p_template)

        multiUIM (builderSrcPartitionTheorem outerTemplateIdxs spec_var_idx source_set_template p_template) instantiationTerms
        multiUIM (specRedundancyTheorem outerTemplateIdxs spec_var_idx source_set_template p_template) instantiationTerms
        multiUIM (builderSubsetTheorem outerTemplateIdxs spec_var_idx source_set_template (neg p_template)) instantiationTerms



        -- Step 2: Prove the main implication by assuming its antecedent, `isSet sourceSet`.
        runProofByAsmM (isSet sourceSet) do
            



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
specAntiRedundancySchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    TheoremSchemaMT () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
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


-- | Gives us properties of a builder set, as well as the builder set object,
-- | after builderInstantiateM has been called
-- | Reproduces some of the work of builderInstantiateM but allows
-- | us to pass less information to functions as a consequence.
builderPropsFree :: 
    Int ->      -- idx: The 'x' in {x ∈ S | P(x)}
    ObjDeBr ->  -- t: The instantiated set, with all of the original outer context
                --    variables instantiated
    PropDeBr -> -- p_template: the original p_template with all outer context variables
                -- instantiated with free variables
    (PropDeBr, ObjDeBr) -- the properties of the builderset and the builder set object
builderPropsFree idx t p_template =
        let
            new_idx_base = idx + 1
            internalBIdx = new_idx_base -- Placeholder index for the specified set 'B' (which will be XInternal internalBIdx)
            
            -- The core relationship: x ∈ B ↔ (P(x) ∧ x ∈ t)
            -- X idx represents 'x' (the element variable)
            -- XInternal internalBIdx represents 'B' (the set being specified)
            -- XInternal internalTIdx represents 't' (the source set)
            -- p_template represents P(x)
            -- Observe that t won't have any template variables in it so there is
            -- no risk of capture at this time.
            core_prop_template :: PropDeBr
            core_prop_template = (X idx `In` X internalBIdx)
                             :<->:
                             (p_template :&&: (X idx `In` t))

            -- Universally quantify over x: ∀x (x ∈ B ↔ (P(x) ∧ x ∈ t))
            quantified_over_x :: PropDeBr
            quantified_over_x = aX idx core_prop_template

            -- Condition that B must be a set: isSet(B)
            -- isSet is defined in Shorthands as Neg (B `In` IntSet)
            condition_B_isSet :: PropDeBr
            condition_B_isSet = isSet (X internalBIdx) -- Using the isSet shorthand

            -- Combine the conditions for B: isSet(B) ∧ ∀x(...)
            full_condition_for_B :: PropDeBr
            full_condition_for_B = 
                      (condition_B_isSet :&&: quantified_over_x)


            -- hilbertObj
            hilbert_obj :: ObjDeBr
            hilbert_obj = hX internalBIdx full_condition_for_B

            -- substitute the hilbert obj into the template

            free_props = propDeBrSubX internalBIdx hilbert_obj
                    full_condition_for_B
            

        in
            (free_props, hilbert_obj)



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
proveBuilderSrcPartitionUnionMFree :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    ObjDeBr ->  -- sourceSet: The set S
    PropDeBr -> -- p_tmplt: The predicate P(x), which uses X spec_var_idx for x.
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr,[Int],())
proveBuilderSrcPartitionUnionMFree spec_var_idx sourceSet p_tmplt =
              -- partition_equiv_theorem_free =
    runProofBySubArgM do
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
        (forall_bicond, _) <- runProofByUGM () do
            v <- getTopFreeVar
            
            -- Construct the specific instance of the partition equivalence lemma that we need.
            let p_of_v = propDeBrSubX spec_var_idx v p_tmplt
            -- let equiv_for_v = (v `In` sourceSet) :<->: (((v `In` sourceSet) :&&: p_of_v) :||: ((v `In` sourceSet) :&&: (neg p_of_v)))
            
            -- This proof assumes the above equivalence is already proven in the context.
            -- We use repM to formally bring it into this subproof's context.
            (tm_statement, _) <- repM partition_equiv_theorem_free
            (proven_equiv_thm,_) <- uiM v tm_statement

            (def_prop_Union, _, _) <- binaryUnionInstantiateM builderSet_P builderSet_NotP

            -- Goal: Prove v ∈ sourceSet ↔ v ∈ union_of_builders
            -- Direction 1: (v ∈ sourceSet) → (v ∈ union_of_builders)
            (dir1, _) <- runProofByAsmM (v `In` sourceSet) do
                (equiv_imp, _) <- bicondElimLM proven_equiv_thm
                (partition_disj, _) <- mpM equiv_imp
                
                (case1_imp, _) <- runProofByAsmM (p_of_v :&&: (v `In` sourceSet)) do
                    (forall_p, _) <- simpRM def_prop_P
                    (def_p_inst, _) <- uiM v forall_p
                    (def_p_imp, _) <- bicondElimRM def_p_inst

                    (v_in_sp, _) <- mpM def_p_imp
                    (v_in_sp_or_snotp, _) <- disjIntroLM v_in_sp (v `In` builderSet_NotP)
                    (forall_union, _) <- simpRM def_prop_Union
                    (def_union_inst, _) <- uiM v forall_union
                    (def_union_imp, _) <- bicondElimRM def_union_inst
                    mpM def_union_imp
                
                (case2_imp, _) <- runProofByAsmM ((neg p_of_v) :&&: (v `In` sourceSet)) do
                    (forall_notp, _) <- simpRM def_prop_NotP
                    (def_notp_inst, _) <- uiM v forall_notp
                    (def_notp_imp, _) <- bicondElimRM def_notp_inst
                    (v_in_s_notp, _) <- mpM def_notp_imp
                    (v_in_sp_or_snotp, _) <- disjIntroRM (v `In` builderSet_P) v_in_s_notp
                    (forall_union, _) <- simpRM def_prop_Union
                    (def_union_inst, _) <- uiM v forall_union
                    (def_union_imp, _) <- bicondElimRM def_union_inst
                    mpM def_union_imp
                disjElimM partition_disj case1_imp case2_imp

            -- Direction 2: (v ∈ union_of_builders) → (v ∈ sourceSet)
            (dir2, _) <- runProofByAsmM (v `In` union_of_builders) do
                (forall_union, _) <- simpRM def_prop_Union
                (def_union_inst, _) <- uiM v forall_union
                (def_union_imp, _) <- bicondElimLM def_union_inst
                (v_in_sp_or_snotp, _) <- mpM def_union_imp
                
                (forall_subset_p, _) <- simpRM subset_P_proven
                (subset_P_imp, _) <- uiM v forall_subset_p
                
                (forall_subset_notp, _) <- simpRM subset_NotP_proven
                (subset_NotP_imp, _) <- uiM v forall_subset_notp
                
                (case1_imp_dir2, _) <- runProofByAsmM (v `In` builderSet_P) $ mpM subset_P_imp
                (case2_imp_dir2, _) <- runProofByAsmM (v `In` builderSet_NotP) $ mpM subset_NotP_imp
                disjElimM v_in_sp_or_snotp case1_imp_dir2 case2_imp_dir2
            
            -- Combine the two directions into the final biconditional.
            bicondIntroM dir1 dir2

        -- Step 4: Apply the Axiom of Extensionality to get the final equality.
        (ext_axiom, _) <- ZFC.extensionalityAxiomM
        (ext_inst, _) <- multiUIM ext_axiom [sourceSet, union_of_builders]

        (isSet_Union_and_forall_bicond,_) <- adjM isSet_union forall_bicond
        (full_adj,_) <- adjM (isSet sourceSet) isSet_Union_and_forall_bicond

        (imp1, _) <- mpM ext_inst

        return ()
    
    --return () 

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
proveBuilderSrcPartitionIntersectionEmptyMFree :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}
    ObjDeBr ->  -- sourceSet: The set S
    PropDeBr -> -- p_tmplt: The predicate P(x), which uses X spec_var_idx for x.
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr,[Int],())
proveBuilderSrcPartitionIntersectionEmptyMFree spec_var_idx sourceSet p_tmplt -- def_prop_P def_prop_NotP 
           =
    runProofBySubArgM do
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
        x <- showPropM isSet_intersection
        remarkM x
        -- error "isSet_intersection"

        -- Step 3: Prove ∀y (¬(y ∈ intersection_of_builders))
        -- This is equivalent to proving the intersection is empty.
        (forall_not_in_intersection, _) <- runProofByUGM () do
            v <- getTopFreeVar
            -- We prove ¬(v ∈ intersection) by assuming (v ∈ intersection) and deriving a contradiction.
            (absurd_imp,_) <- runProofByAsmM (v `In` intersection_of_builders) do
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
                a <- showPropM notp_imp
                remarkM a
                (notp_and_v_in_s, _) <- mpM notp_imp
                (notp_of_v, _) <- simpLM notp_and_v_in_s

                -- We have now proven P(v) and ¬P(v), which is a contradiction.
                contraFM p_of_v
            absurdM absurd_imp
        -- `runProofByAsmM` proves `(v ∈ intersection) → False`. `absurdM` turns this into `¬(v ∈ intersection)`.
        -- `runProofByUGM` then generalizes it.

        -- Step 4: Prove the final equality using the Axiom of Extensionality.

        (isSet_Empty_prop, _) <- ZFC.emptySetAxiomM -- Extracts ∀x. ¬(x ∈ ∅)
        -- We need to prove ∀y (y ∈ intersection ↔ y ∈ ∅).
        -- Since both sides are always false, the biconditional is always true.
        (forall_bicond, _) <- runProofByUGM () do
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
        (ext_axiom, _) <- ZFC.extensionalityAxiomM
        (ext_inst, _) <- multiUIM ext_axiom [intersection_of_builders, EmptySet]
        (isSetEmptySet,_) <- ZFC.emptySetNotIntM
        (adj1, _) <- adjM isSetEmptySet forall_bicond
        (full_antecedent_for_ext, _) <- adjM isSet_intersection adj1
        
        mpM ext_inst


        return ()


-- | Constructs the PropDeBr term for the theorem that a set S is partitioned
-- | by a predicate P and its negation.
-- |
-- | Theorem: ∀(params...) ( isSet(S) → ( (S = {x∈S|P(x)} ∪ {x∈S|¬P(x)}) ∧ ({x∈S|P(x)} ∩ {x∈S|¬P(x)} = ∅) ) )
builderSrcPartitionTheorem :: [Int] -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
builderSrcPartitionTheorem outerTemplateIdxs spec_var_idx source_set_template p_template =
    let
        -- Construct the two builder sets from the templates
        builderSet_P = builderX spec_var_idx source_set_template p_template
        builderSet_NotP = builderX spec_var_idx source_set_template (neg p_template)

        -- Part 1: The union equality: S = {x|P(x)} ∪ {x|¬P(x)}
        union_of_builders = builderSet_P .\/. builderSet_NotP
        union_equality = source_set_template :==: union_of_builders

        -- Part 2: The intersection equality: {x|P(x)} ∩ {x|¬P(x)} = ∅
        intersection_of_builders = builderSet_P ./\. builderSet_NotP
        intersection_equality = intersection_of_builders :==: EmptySet

        -- Combine the two equalities into a single conjunction
        partition_conjunction = union_equality :&&: intersection_equality

        -- Construct the antecedent for the main implication: isSet(S)
        antecedent = isSet source_set_template

        -- Form the main implication
        implication = antecedent :->: partition_conjunction

    in
        -- Universally quantify over all parameters to create the final closed theorem.
        multiAx outerTemplateIdxs implication


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
proveBuilderSrcPartitionTheoremM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs: Parameters for the source set and predicate.
    Int ->      -- spec_var_idx: The 'x' in {x ∈ S | P(x)}.
    ObjDeBr ->  -- source_set_template: The source set S, which may contain X_k parameters.
    PropDeBr -> -- p_template: The predicate P(x), which may contain X_k parameters.
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveBuilderSrcPartitionTheoremM outerTemplateIdxs spec_var_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters.
    multiUGM (replicate (length outerTemplateIdxs) ()) do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.
        freeVarCount <- getFreeVarCount
        let instantiationTerms = Prelude.map V [0 .. freeVarCount - 1]

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
        runProofByAsmM (isSet sourceSet) do
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
builderSrcPartitionSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    TheoremSchemaMT () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
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



-- isRelWellFoundedOn Dom Rel
-- Assumes Rel is a set of pairs, and Dom is the set it's well-founded on.
-- Forall S ((S subset Dom /\ S /= EmptySet) ->
--            Exists x (x In S /\ Forall y (y In S -> not (y Rel x))) )
-- Example usage:
-- let myDomain = Constant "MySet"
-- let myRelation = Constant "MyRelation" -- Assume this is a set of pairs
-- let wellFoundedStatement = isRelWellFoundedOn myDomain myRelation
isRelWellFoundedOn :: ObjDeBr -> ObjDeBr -> PropDeBr
isRelWellFoundedOn dom rel =
    let
        -- Template Variables for the quantifiers in the well-foundedness definition
        idx_S = 0 -- Represents the subset S of 'dom'
        idx_x = 1 -- Represents the minimal element x in S
        idx_y = 2 -- Represents any element y in S for comparison

        dom_idx = 3
        rel_idx = 4

        -- Antecedent for the main implication: S is a non-empty subset of 'dom'
        s_is_subset_dom = subset (X idx_S) (X dom_idx)  -- S subset dom
        s_is_not_empty  = Neg ( X idx_S :==: EmptySet ) -- S /= EmptySet
        antecedent_S    = s_is_subset_dom :&&: s_is_not_empty

        -- Consequent: Exists an R-minimal element x in S
        -- x In S
        x_is_in_S       = X idx_x `In` X idx_S
        -- y Rel x  (pair <y,x> In rel)
        y_rel_x         = buildPair (X idx_y) (X idx_x) `In` X rel_idx
        -- Forall y (y In S -> not (y Rel x))
        x_is_minimal_in_S = aX idx_y ( (X idx_y `In` X idx_S) :->: Neg y_rel_x )
        -- Exists x (x In S /\ x_is_minimal_in_S)
        consequent_exists_x = eX idx_x ( x_is_in_S :&&: x_is_minimal_in_S )
    in
        propDeBrSubXs [(dom_idx,dom),(rel_idx,rel)] $ aX idx_S ( antecedent_S :->: consequent_exists_x )

-- strongInductionPremiseOnRel P_template idx Dom Rel
-- Forall n (n In Dom -> ( (Forall k (k In Dom /\ k Rel n -> P(k))) -> P(n) ) )
-- Example usage:
-- let myProperty = X idx :==: X idx -- P(x) is x=x
-- let myDomain = natSetObj
-- let lessThanRel = builderX 0 -- This needs to be defined, e.g. {<x,y> | x < y & x,y in natSetObj}
--                  (crossProd natSetObj natSetObj) -- Source set for pairs
--                  ( (project 2 0 (X 0)) .<. (project 2 1 (X 0)) ) -- Property X 0 is a pair <a,b> and a < b
-- let premise = strongInductionPremiseOnRel myProperty myDomain lessThanRel

strongInductionPremiseOnRel :: PropDeBr -> Int -> ObjDeBr -> ObjDeBr -> PropDeBr
strongInductionPremiseOnRel p_template idx dom rel =
    let
        -- Template variable indices for the quantifiers in this premise
        n_idx = 0 -- The main induction variable 'n'
        k_idx = 1 -- The universally quantified variable 'k' such that k Rel n

        dom_idx = 2
        rel_idx = 3

        -- P(n) - using X n_idx for n.
        -- Since P_template uses X idx, we substitute X idx in P_template with X n_idx.
        p_n = propDeBrSubX idx (X n_idx) p_template

        -- P(k) - using X k_idx for k.
        -- Substitute X idx in P_template with X k_idx.
        p_k = propDeBrSubX idx (X k_idx) p_template

        -- Inner hypothesis: k Rel n -> P(k)
        -- Here, n is X n_idx and k is X k_idx
        k_rel_n     = buildPair (X k_idx) (X n_idx) `In` X rel_idx -- k Rel n
        hyp_antecedent = k_rel_n
        hyp_body    = hyp_antecedent :->: p_k

        -- Forall k (hyp_body)
        -- This is the "for all predecessors k of n, P(k) holds" part.
        forall_k_predecessors_hold_P = aX k_idx hyp_body

        -- Inductive Step (IS) for a specific n: (Forall k predecessors...) -> P(n)
        -- Here, n is X n_idx
        inductive_step_for_n = forall_k_predecessors_hold_P :->: p_n

        -- Body of the main Forall n: (IS_for_n)
        n_in_dom = X n_idx `In` X dom_idx
        main_forall_body = inductive_step_for_n
    in
        propDeBrSubXs [(dom_idx, dom), (rel_idx, rel)] $ aX n_idx main_forall_body



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
builderInstantiateM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [ObjDeBr] ->    -- instantiationTerms
    [Int] ->        -- outerTemplateIdxs
    Int ->          -- spec_var_X_idx
    ObjDeBr ->      -- source_set_template
    PropDeBr ->     -- p_template
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], (ObjDeBr, ObjDeBr, PropDeBr))
builderInstantiateM instantiationTerms outerTemplateIdxs spec_var_X_idx source_set_template p_template =
    runProofBySubArgM do
        -- Step 1: Get the closed, universally quantified Axiom of Specification.
        -- 'specificationM' quantifies over the parameters specified in 'outerTemplateIdxs'.
        (closedSpecAxiom, _) <- ZFC.specificationM outerTemplateIdxs spec_var_X_idx source_set_template p_template

        -- Step 2: Use multiUIM to instantiate the axiom with the provided terms.
        -- This proves the specific existential statement for the given parameters.
        (instantiated_existential_prop, _) <- multiUIM closedSpecAxiom instantiationTerms

        -- Step 3: Apply Existential Instantiation to get the Hilbert object and its property.
        -- This is the final result of the construction.
        (defining_prop, prop_idx, built_obj) <- eiHilbertM instantiated_existential_prop

        let instantiated_source_set = objDeBrSubXs (zip outerTemplateIdxs instantiationTerms) source_set_template
        let instantiated_p_template = propDeBrSubXs (zip outerTemplateIdxs instantiationTerms) p_template
         
        -- The runProofBySubArgM wrapper requires the 'do' block to return the 'extraData'
        -- that the caller of builderInstantiateM will receive.
        return (built_obj, instantiated_source_set, instantiated_p_template)









-- | Given the instantiated source set, 'dom', and 
-- | instantiated predicate 'p_template' returned from from `builderInstantiateM`, this function proves that
-- | { x ∈ dom | p_template(x)} is a subset of dom
-- | said set is a subset of its original domain (`domainSet`).
-- | It encapsulates the entire proof within a single sub-argument.
-- | When we say that p_template is instantiated, we mean that all of the template variables,
-- | *other than the its specification variable*, are assumed to have already been instantiated.
proveBuilderIsSubsetOfDomMFree :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>    
    Int -> -- spec_var_idx 
    ObjDeBr ->   -- sourceSet: The ObjDeBr for the set B, i.e., {x ∈ dom | P(x)}
    PropDeBr -> -- p_tmplt
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr,[Int],())
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
            runProofByAsmM (v `In` builderSet) $ do
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
builderSubsetTheorem :: [Int] -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
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
proveBuilderSubsetTheoremM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveBuilderSubsetTheoremM outerTemplateIdxs spec_var_X_idx source_set_template p_template = do
    -- Step 1: Universally generalize over all parameters.
    -- The number of quantifiers is determined by the length of 'outerTemplateIdxs'.
    multiUGM (replicate (length outerTemplateIdxs) ()) do
        
        -- Step 1: Get the list of free variables. All will be active since
        -- the source_set_template and the p_template would be deemed insane
        -- in the context of testing a theorem, if they had any free variables
        -- of their own.
        freeVarCount::Int <- getFreeVarCount
        let freeVars = Prelude.map V [0..freeVarCount - 1]
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


builderSubsetTheoremSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
    [Int] ->    -- outerTemplateIdxs
    Int ->      -- spec_var_X_idx
    ObjDeBr ->  -- source_set_template
    PropDeBr -> -- p_template
    TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
builderSubsetTheoremSchema outerTemplateIdxs spec_var_X_idx source_set_template p_template =
    let
      source_set_tmplt_consts = extractConstsTerm source_set_template
      p_tmplt_consts = extractConstsSent p_template
      all_consts = source_set_tmplt_consts `Set.union` p_tmplt_consts
      typed_consts = zip (Data.Set.toList all_consts) (repeat ()) 
    in   
      TheoremSchemaMT typed_consts [] (proveBuilderSubsetTheoremM outerTemplateIdxs spec_var_X_idx source_set_template p_template)



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
powerSetInstantiateM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr -> -- ^ The object 'x' for which to prove its power set is a set.
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], ObjDeBr)
powerSetInstantiateM x = do
    runProofBySubArgM do
        -- Step 1: Get the Axiom of Power Set from the ZFC rule set.
        (powerSetAxiom_proven, _) <- ZFC.powerSetAxiomM

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



-- | Given an object 'x', proves that its power set, PowerSet(x), is also a set.
-- |
-- | Note: This helper requires that 'isSet x' has already been proven
-- | in the current proof context.
-- |
-- | This helper relies on the `powerSetInstantiateM` helper to get the properties of the
-- | powerSet object.
provePowerSetIsSetM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr -> -- ^ The object 'x' for which to prove its power set is a set.
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int])
provePowerSetIsSetM x = do
    (result_prop,idx,_)<-runProofBySubArgM do
        (prop_of_powSet, _, powSet_obj) <- powerSetInstantiateM x
        PL.simpLM prop_of_powSet
        return ()
    return (result_prop,idx)


-- | Constructs the PropDeBr term for the closed theorem of binary intersection existence.
-- | The theorem is: ∀A ∀B ((isSet A ∧ isSet B) → ∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∧ x ∈ B))))
binaryIntersectionExistsTheorem :: PropDeBr
binaryIntersectionExistsTheorem =
    let
        -- Define integer indices for the template variables (X k).
        a_idx = 0 -- Represents set A
        b_idx = 1 -- Represents set B
        s_idx = 2 -- Represents the intersection set S
        x_idx = 3 -- Represents an element x

        -- Construct the inner part of the formula: x ∈ S ↔ (x ∈ A ∧ x ∈ B)
        x_in_S = X x_idx `In` X s_idx
        x_in_A = X x_idx `In` X a_idx
        x_in_B = X x_idx `In` X b_idx
        x_in_A_and_B = x_in_A :&&: x_in_B
        biconditional = x_in_S :<->: x_in_A_and_B

        -- Quantify over x: ∀x(x ∈ S ↔ (x ∈ A ∧ x ∈ B))
        forall_x_bicond = aX x_idx biconditional

        -- Construct the property of the set S: isSet(S) ∧ ∀x(...)
        isSet_S = isSet (X s_idx)
        property_of_S = isSet_S :&&: forall_x_bicond

        -- Quantify over S: ∃S (isSet(S) ∧ ∀x(...))
        exists_S = eX s_idx property_of_S

        -- Construct the antecedent of the main implication: isSet(A) ∧ isSet(B)
        isSet_A = isSet (X a_idx)
        isSet_B = isSet (X b_idx)
        antecedent = isSet_A :&&: isSet_B

        -- Construct the main implication
        implication = antecedent :->: exists_S

    in
        -- Universally quantify over A and B to create the final closed theorem.
        multiAx [a_idx, b_idx] implication


-- | Proves the theorem defined in 'binaryIntersectionExistsTheorem'.
-- |
-- | The proof strategy is to use the Axiom of Specification. For any two sets A and B,
-- | we can specify a new set S from the source set A using the predicate "is an element of B".
-- | The resulting set S = {x ∈ A | x ∈ B} is precisely the intersection A ∩ B.
-- | The `builderInstantiateM` helper encapsulates this application of the axiom.
proveBinaryIntersectionExistsM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveBinaryIntersectionExistsM = do
    -- The theorem is universally quantified over two sets, A and B.
    multiUGM [(), ()] do
        -- Inside the UG, free variables v_A and v_B are introduced.
        v_B <- getTopFreeVar
        context <- ask
        let v_A_idx = (length . freeVarTypeStack) context - 2
        let v_A = V v_A_idx
        let setA = v_A
        let setB = v_B

        -- Prove the main implication by assuming the antecedent: isSet(A) ∧ isSet(B).
        runProofByAsmM (isSet setA :&&: isSet setB) do
            -- Within this subproof, isSet(A) and isSet(B) are proven assumptions.

            -- Step 1: Define the templates for the Axiom of Specification.
            -- The source set T will be A. The predicate P(x) will be (x ∈ B).
            -- The parameters to our templates are A and B.
            let a_param_idx = 0
            let b_param_idx = 1
            let spec_var_idx = 2 -- The 'x' in {x ∈ T | P(x)}

            let source_set_template = X a_param_idx
            let p_template = X spec_var_idx `In` X b_param_idx

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
            let target_existential = propDeBrSubXs [(0, setA), (1, setB)] binaryIntersectionExistsTheorem

            -- Step 4: Apply Existential Generalization.
            -- This works because 'defining_prop' is the instantiated version of the
            -- property inside the target existential statement.
            egM intersectionObj target_existential

    return ()

-- | The schema that houses 'proveBinaryIntersectionExistsM'.
-- | This theorem has no other high-level theorems as lemmas; it is proven
-- | directly from the Axiom of Specification (via the builderInstantiateM helper).
binaryIntersectionExistsSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
     TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
binaryIntersectionExistsSchema =
    TheoremSchemaMT [] [] proveBinaryIntersectionExistsM

-- | Helper to instantiate the binary intersection theorem and return the intersection set object.
-- | For this helper to work, the theorem defined by 'binaryIntersectionExistsTheorem' must be proven
-- | beforehand (e.g., in the global context by running its schema).
binaryIntersectionInstantiateM ::  (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr -> ObjDeBr -> ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], ObjDeBr)
binaryIntersectionInstantiateM setA setB = do
    runProofBySubArgM do
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



-- | This is the lemma
-- | ∀A ∀B ( (isSet A ∧ isSet B) → ( (∃U (isSet U ∧ ∀x(x ∈ U ↔ ∃Y(Y ∈ {A,B} ∧ x ∈ Y)))) 
-- |    ↔ (∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∨ x ∈ B)))) ) )
union_equiv_theorem :: PropDeBr
union_equiv_theorem =
    let
        tmpl_A_idx = 0; tmpl_B_idx = 1; tmpl_S_idx = 2; tmpl_U_idx = 2; tmpl_Y_idx = 3; tmpl_x_idx = 4
                      
        -- Construct the two existential statements using these Int indices.
        prop_from_union_axiom = eX tmpl_U_idx (isSet (X tmpl_U_idx) :&&:
                                          aX tmpl_x_idx ((X tmpl_x_idx `In` X tmpl_U_idx) :<->:
                                              eX tmpl_Y_idx ((X tmpl_Y_idx `In` roster [X tmpl_A_idx, X tmpl_B_idx]) :&&: (X tmpl_x_idx `In` X tmpl_Y_idx))))
        canonical_body = (X tmpl_x_idx `In` X tmpl_A_idx) :||: (X tmpl_x_idx `In` X tmpl_B_idx)
        canonical_prop = eX tmpl_S_idx (isSet (X tmpl_S_idx) :&&:
                                          aX tmpl_x_idx ((X tmpl_x_idx `In` X tmpl_S_idx) :<->: canonical_body))
            
        thm_antecedent = isSet (X tmpl_A_idx) :&&: isSet (X tmpl_B_idx)
    in    
        multiAx [tmpl_A_idx, tmpl_B_idx] (thm_antecedent :->: (prop_from_union_axiom :<->: canonical_prop))
            
      
-- | Constructs the PropDeBr term for the closed theorem of binary union existence.
-- | The theorem is: ∀A ∀B ((isSet A ∧ isSet B) → ∃S (isSet S ∧ ∀x(x ∈ S ↔ (x ∈ A ∨ x ∈ B))))
binaryUnionExistsTheorem :: PropDeBr
binaryUnionExistsTheorem =
    let
        -- Define the integer indices for the template variables (X k).
        -- These will be bound by the quantifiers.
        a_idx = 0 -- Represents set A
        b_idx = 1 -- Represents set B
        s_idx = 2 -- Represents the union set S
        x_idx = 3 -- Represents an element x

        -- Construct the inner part of the formula: x ∈ S ↔ (x ∈ A ∨ x ∈ B)
        x_in_S = X x_idx `In` X s_idx
        x_in_A = X x_idx `In` X a_idx
        x_in_B = X x_idx `In` X b_idx
        x_in_A_or_B = x_in_A :||: x_in_B
        biconditional = x_in_S :<->: x_in_A_or_B

        -- Quantify over x: ∀x(x ∈ S ↔ (x ∈ A ∨ x ∈ B))
        forall_x_bicond = aX x_idx biconditional

        -- Construct the property of the union set S: isSet(S) ∧ ∀x(...)
        isSet_S = isSet (X s_idx)
        property_of_S = isSet_S :&&: forall_x_bicond

        -- Quantify over S: ∃S (isSet(S) ∧ ∀x(...))
        exists_S = eX s_idx property_of_S

        -- Construct the antecedent of the main implication: isSet(A) ∧ isSet(B)
        isSet_A = isSet (X a_idx)
        isSet_B = isSet (X b_idx)
        antecedent = isSet_A :&&: isSet_B

        -- Construct the main implication
        implication = antecedent :->: exists_S

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

proveBinaryUnionExistsM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveBinaryUnionExistsM = do
    -- Universally generalize over A and B.
    multiUGM [(), ()] do
        -- Inside the UG, free variables v_A and v_B are introduced.
        v_B <- getTopFreeVar
        context <- ask
        let v_A_idx = (length . freeVarTypeStack) context - 2
        let v_A = V v_A_idx
        let setA = v_A
        let setB = v_B

        -- Prove the implication by assuming the antecedent.
        runProofByAsmM (isSet setA :&&: isSet setB) do
            -- Now, isSet(A) and isSet(B) are proven assumptions in this context.

            -- Step 1: Use the Axiom of Pairing to prove ∃P. isSet(P) ∧ P = {A,B}.
            (pairAxiom,_) <- ZFC.pairingAxiomM
            (pairAxiom_inst1, _) <- uiM setA pairAxiom
            (pairAxiom_inst2, _) <- uiM setB pairAxiom_inst1

            -- Step 2: Instantiate this pair set with a Hilbert term `pairSetAB`.
            -- `pair_prop` is isSet({A,B}) ∧ ∀z(z∈{A,B} ↔ z=A ∨ z=B).
            (pair_prop, _, pairSetAB) <- eiHilbertM pairAxiom_inst2
            (isSet_pair_proven, _) <- simpLM pair_prop

            -- Step 3: Use the Axiom of Union on the proven set `pairSetAB`.
            (unionAxiom,_) <- ZFC.unionAxiomM
            (unionAxiom_inst, _) <- uiM pairSetAB unionAxiom

            -- Step 4: Use Modus Ponens with `isSet(pairSetAB)` to derive the existence of the union.
            -- `exists_U` is ∃U(isSet U ∧ ∀x(x∈U ↔ ∃Y(Y∈{A,B} ∧ x∈Y))).
            (exists_U, _) <- mpM unionAxiom_inst
            -- Step 5: Assert a general, CLOSED theorem about the equivalence of the two forms of union.
            -- Thm: ∀A,B. (isSet A ∧ isSet B) → ( (∃U. from Axiom of Union on {A,B}) ↔ (∃S. with canonical binary union prop) )
            -- We build the two existential statements as templates first.

            let tmpl_A_idx = 0; tmpl_B_idx = 1; tmpl_S_idx = 2; tmpl_U_idx = 2; tmpl_Y_idx = 3; tmpl_x_idx = 4
                      

            -- Step 6: Instantiate the theorem with our specific sets A and B.
            (instantiated_thm, _) <- multiUIM union_equiv_theorem [setA, setB]

            -- Step 7: Use Modus Ponens with our assumption `isSet A ∧ isSet B`.
            (proven_biconditional, _) <- mpM instantiated_thm

            -- Step 8: From the equivalence and the proven `exists_U`, derive the target existential.
            (forward_imp, _) <- bicondElimLM proven_biconditional

            forward_imp_txt <- showPropM forward_imp
            remarkM $ "Forward Implication: " <> forward_imp_txt
            PL.mpM forward_imp -- This proves the target_existential

    return ()



-- | The schema that houses 'proveBinaryUnionExistsM'.
-- | The schema stipulates that:
-- | "union_equiv_theorem" is a required lemma.
binaryUnionExistsSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
     TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
binaryUnionExistsSchema = 

      
    TheoremSchemaMT [] [union_equiv_theorem] proveBinaryUnionExistsM 




-- | Helper to instantiate the binary union theorem and return the union set.
-- | For this helper to work, the theorem defined by 'binaryUnionExistsTheorem' must be proven
-- | beforehand, which is likely done in the global context.
binaryUnionInstantiateM ::  (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr -> ObjDeBr -> ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], ObjDeBr)
binaryUnionInstantiateM setA setB = do
    runProofBySubArgM do
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
proveUnionIsSetM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr -> ObjDeBr -> ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int])
proveUnionIsSetM setA setB = do
    (resultProp,idx,_) <- runProofBySubArgM do
        (prop_of_union, _, unionObj) <- binaryUnionInstantiateM setA setB
        (isSet_union_proven, _) <- simpLM prop_of_union
        return ()
    return (resultProp,idx)

-- | This function composes the "pair substitution theorem":
-- |  
-- |  ∀𝑥₅(∀𝑥₄(∀𝑥₃(∀𝑥₂(∀𝑥₁(∀𝑥₀((𝑥₃,𝑥₂) = 
-- |      (𝑥₁,𝑥₀) ∧ 𝑥₁ ∈ 𝑥₅ ∧ 𝑥₀ ∈ 𝑥₄ → 𝑥₃ ∈ 𝑥₅ ∧ 𝑥₂ ∈ 𝑥₄))))))
-- |  
pairSubstTheorem :: PropDeBr
pairSubstTheorem = 
    let
        thm_A=0; thm_B=1; thm_x=2; thm_y=3; thm_a=4; thm_b=5
        thm_antecedent = (buildPair (X thm_x) (X thm_y) :==: buildPair (X thm_a) (X thm_b))
                            :&&: (X thm_a `In` X thm_A) :&&: (X thm_b `In` X thm_B)
        thm_consequent = (X thm_x `In` X thm_A) :&&: (X thm_y `In` X thm_B)
        pair_subst_theorem_closed = multiAx [thm_A, thm_B, thm_x, thm_y, thm_a, thm_b] (thm_antecedent :->: thm_consequent)
    in
        pair_subst_theorem_closed

-- | This function composes the "pair in universe theorem":
-- |
-- |  ∀𝑥₃(∀𝑥₂(∀𝑥₁(∀𝑥₀(isSet(𝑥₃) ∉ ℤ ∧ isSet(𝑥₂) ∧ 𝑥₁ ∈ 𝑥₃ ∧ 𝑥₀ ∈ 𝑥₂ 
-- |         → (𝑥₁,𝑥₀) ∈ 𝒫(𝒫(𝑥₃ ∪ 𝑥₂))))))
-- |
pairInUniverseTheorem :: PropDeBr
pairInUniverseTheorem =
    let thm_A=0; thm_B=1; thm_x=2; thm_y=3
        thm_univ = buildPowerSet (buildPowerSet (X thm_A .\/. X thm_B))
        thm_pair_univ_antecedent = isSet (X thm_A) :&&: isSet (X thm_B) :&&: (X thm_x `In` X thm_A) :&&: (X thm_y `In` X thm_B)
        thm_pair_univ_consequent = buildPair (X thm_x) (X thm_y) `In` thm_univ
        pair_in_universe_theorem_closed = multiAx [thm_A, thm_B, thm_x, thm_y] (thm_pair_univ_antecedent :->: thm_pair_univ_consequent)
    in
        pair_in_universe_theorem_closed

-- | Constructs the PropDeBr term for the closed theorem stating that the property
-- | of a cross product derived via the Axiom of Specification implies the
-- | canonical property of a cross product.
-- |
-- | 'binaryUnionExistsTheorem' is a required lemma for this theorem.
-- | Theorem: ∀A∀B((isSet A ∧ isSet B) → (SpecProp(A,B) → CanonicalProp(A,B)))
crossProductDefEquivTheorem :: PropDeBr
crossProductDefEquivTheorem =
    let
        -- Define integer indices for the template variables (X k).
        -- These will be bound by the outermost quantifiers for A and B.
        a_idx = 0 -- Represents set A
        b_idx = 1 -- Represents set B

        setA = X a_idx
        setB = X b_idx

        -- Define the inner predicate P(z) used in the specification.
        -- P(z) := ∃x∃y (z = <x,y> ∧ x ∈ A ∧ y ∈ B)
        spec_z_idx = 2; spec_x_idx = 3; spec_y_idx = 4
        predicate_P = eX spec_x_idx (eX spec_y_idx (
                          (X spec_z_idx :==: buildPair (X spec_x_idx) (X spec_y_idx))
                          :&&: (X spec_x_idx `In` setA)
                          :&&: (X spec_y_idx `In` setB)
                      ))

        -- Define the universe set U = P(P(A U B))
        universeSet = buildPowerSet (buildPowerSet (setA .\/. setB))

        -- Define the cross product object B via the builder shorthand, which
        -- is equivalent to the Hilbert term from specification.
        -- B := {z ∈ U | P(z)}
        crossProdObj = builderX spec_z_idx universeSet predicate_P

        -- Now, construct the two main properties that form the implication.

        -- 1. SpecProp(A,B): The defining property of B as derived from specification.
        --    isSet(B) ∧ ∀z(z∈B ↔ (P(z) ∧ z∈U))
        spec_prop_z_idx = 2 -- A new z for this quantifier

        spec_prop_body = (X spec_prop_z_idx `In` crossProdObj) :<->:
                         ((propDeBrSubX spec_z_idx (X spec_prop_z_idx) predicate_P) :&&: (X spec_prop_z_idx `In` universeSet))
        spec_prop = isSet crossProdObj :&&: aX spec_prop_z_idx spec_prop_body

        -- 2. CanonicalProp(A,B): The standard definition of the property of A × B.
        --    isSet(B) ∧ ∀x∀y(<x,y>∈B ↔ (x∈A ∧ y∈B))
        canon_x_idx = 2; canon_y_idx = 3
        canon_element_prop = (X canon_x_idx `In` setA) :&&: (X canon_y_idx `In` setB)
        canon_pair_in_b = buildPair (X canon_x_idx) (X canon_y_idx) `In` crossProdObj
        canon_quantified_bicond = aX canon_x_idx (aX canon_y_idx (canon_element_prop :<->: canon_pair_in_b))
        canonical_prop = isSet crossProdObj :&&: canon_quantified_bicond

        -- Construct the main implication of the theorem: SpecProp(A,B) → CanonicalProp(A,B)
        spec_implies_canonical = spec_prop :->: canonical_prop

        -- Construct the antecedent for the entire theorem: isSet(A) ∧ isSet(B)
        isSet_A = isSet setA
        isSet_B = isSet setB
        theorem_antecedent = isSet_A :&&: isSet_B

        -- Form the implication for the body of the theorem
        theorem_body = theorem_antecedent :->: spec_implies_canonical

    in
        -- Universally quantify over A and B to create the final closed theorem.
        multiAx [a_idx, b_idx] theorem_body
    


-- | Proves "crossProductDefEquivTheorem".
proveCrossProductDefEquivM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveCrossProductDefEquivM = do
    -- Universally generalize over A and B
    multiUGM [(), ()] do
        -- Inside UG, free variables v_A and v_B are introduced
        v_B <- getTopFreeVar
        context <- ask
        let v_A_idx = (length . freeVarTypeStack) context - 2
        let v_A = V v_A_idx
        let setA = v_A
        let setB = v_B

        -- Prove the main implication by assuming the antecedent
        runProofByAsmM (isSet setA :&&: isSet setB) do
            -- Within this subproof, isSet A and isSet B are proven assumptions.
            -- Construct all necessary terms and properties internally.
            let universeSet = buildPowerSet (buildPowerSet (setA .\/. setB))
            let z_idx = 0; x_idx = 1; y_idx = 2; setA_idx = 3; setB_idx = 4
            let universeSet_tmplt = buildPowerSet (buildPowerSet (X setA_idx .\/. X setB_idx))
            let predicate_P = eX x_idx (eX y_idx (
                                  (X z_idx :==: buildPair (X x_idx) (X y_idx))
                                  :&&: (X x_idx `In` setA)
                                  :&&: (X y_idx `In` setB)
                              ))
            let predicate_P_tmplt = eX x_idx (eX y_idx (
                                  (X z_idx :==: buildPair (X x_idx) (X y_idx))
                                  :&&: (X x_idx `In` X setA_idx)
                                  :&&: (X y_idx `In` X setB_idx)
                              ))
            -- The object for the cross product, B = A×B
            let crossProdObj = builderX z_idx universeSet predicate_P
            crossProdObj_txt <- showObjM crossProdObj
            remarkM $ "Cross Product Object: " <> crossProdObj_txt
            -- Get the defining property of B from the Axiom of Specification
            --(specAxiom, _) <- specificationM [] z_idx universeSet predicate_P -- No outer free vars in this sub-context
            --(definingProp_of_B, _, _) <- eiHilbertM specAxiom
 
            -- Correctly use specificationFreeMBuilder, which is designed to handle
            -- the free variables v_A and v_B present in 'setA', 'setB', and thus in 'predicate_P'.
            (definingProp_of_B, _, (crossProdObj,_,_)) <- 
                 builderInstantiateM [V 0, V 1] [setA_idx, setB_idx] z_idx universeSet_tmplt predicate_P_tmplt

            crossProdObj_txt <- showObjM crossProdObj
            remarkM $ "Cross Product Object from Builder: " <> crossProdObj_txt
            --error "stop this shit"

            -- Construct the canonical target property for the cross product B
            let s_idx_final = 0; x_idx_final = 1; y_idx_final = 2
            let element_prop_final = (X x_idx_final `In` setA) :&&: (X y_idx_final `In` setB)
            let pair_in_s_final = buildPair (X x_idx_final) (X y_idx_final) `In` (X s_idx_final)
            let quantified_bicond_final = aX x_idx_final (aX y_idx_final (pair_in_s_final :<->: element_prop_final))
            let canonical_prop_of_B = isSet crossProdObj :&&: quantified_bicond_final

            -- Now, prove the implication: definingProp_of_B → canonical_prop_of_B
            runProofByAsmM definingProp_of_B do
                -- This inner proof derives the canonical property from the specification property.
                (isSet_B_proven, _) <- simpLM definingProp_of_B
                (spec_forall_bicond, _) <- simpRM definingProp_of_B
                (quantified_bicond_derived, _) <- multiUGM [(), ()] do
                    v_y_inner <- getTopFreeVar
                    context_inner <- ask
                    let v_x_inner_idx = (length . freeVarTypeStack) context_inner - 2
                    let v_x_inner = V v_x_inner_idx
                    (dir1,_) <- runProofByAsmM (buildPair v_x_inner v_y_inner `In` crossProdObj) do
                        (spec_inst,_) <- uiM (buildPair v_x_inner v_y_inner) spec_forall_bicond
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
                                               
                        -- Instantiate the pair substitution theorem with our specific free variables and Hilbert terms.
                        let instantiation_terms_for_thm = [setA, setB, v_x_inner, v_y_inner, v_a_h, v_b_h]
                        (instantiated_theorem, _) <- multiUIM pairSubstTheorem instantiation_terms_for_thm

                        -- Use Modus Ponens with the fully instantiated body 'p_inst_final' to get the consequent.
                        mpM instantiated_theorem
                    (dir2,_) <- runProofByAsmM ((v_x_inner `In` setA) :&&: (v_y_inner `In` setB)) do
                        -- Goal: Prove <x,y> ∈ B. This means proving P(<x,y>) ∧ <x,y>∈U.

                        -- Part 1: Prove P(<x,y>), which is ∃a∃b(<x,y>=<a,b> ∧ a∈A ∧ b∈B).
                        -- We prove this by witnessing with a=v_x and b=v_y.
                        (vx_in_A_p, _) <- simpLM ((v_x_inner `In` setA) :&&: (v_y_inner `In` setB))
                        (vy_in_B_p, _) <- simpRM ((v_x_inner `In` setA) :&&: (v_y_inner `In` setB))
                        (refl_pair, _) <- eqReflM (buildPair v_x_inner v_y_inner)

                        (in_A_and_in_B, _) <- adjM vx_in_A_p vy_in_B_p
                        (p_vx_vy_instantiated_body, _) <- adjM refl_pair in_A_and_in_B


                        let p_ab_template = (buildPair v_x_inner v_y_inner :==: buildPair (X 0) (X 1)) :&&: ((X 0 `In` setA) :&&: (X 1 `In` setB))
                        let p_vx_y_template = propDeBrSubX 0 v_x_inner p_ab_template
                        let eg_target_y = eX 1 p_vx_y_template
                        (exists_y_prop, _) <- egM v_y_inner eg_target_y

                        let p_x_b_template = eX 1 (propDeBrSubX 0 (X 0) p_ab_template)
                        let eg_target_x = eX 0 p_x_b_template
                        (p_of_pair_proven, _) <- egM v_x_inner eg_target_x

                        -- Instantiate the pair in universe theorem and use it.
                        (instantiated_thm, _) <- multiUIM pairInUniverseTheorem [setA, setB, v_x_inner, v_y_inner]


                        (conj3_4, _) <- adjM vx_in_A_p vy_in_B_p
                        (isSetB_p, _) <- simpRM (isSet setA :&&: isSet setB)
                        (conj2_3_4, _) <- adjM isSetB_p conj3_4
                        (isSetA_p, _) <- simpLM (isSet setA :&&: isSet setB)
                        (full_antecedent, _) <- adjM isSetA_p conj2_3_4
                        (pair_in_U_proven, _) <- mpM instantiated_thm
                        -- Part 3: Combine proofs for P(<x,y>) and <x,y>∈U to match the spec property.
                        (in_U_and_P, _) <- adjM p_of_pair_proven pair_in_U_proven
                        
                        -- Part 4: Use the spec property to conclude <x,y> ∈ B
                        (spec_bicond_inst, _) <- uiM (buildPair v_x_inner v_y_inner) spec_forall_bicond
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
crossProductDefEquivSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
     TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
crossProductDefEquivSchema = 
    TheoremSchemaMT [] 
                    [binaryUnionExistsTheorem
                    , pairSubstTheorem
                    , pairInUniverseTheorem] 
                    proveCrossProductDefEquivM



-- | Constructs the PropDeBr term for the closed theorem of Cartesian product existence.
-- | The theorem is: ∀A ∀B ((isSet A ∧ isSet B) → ∃S (isSet S ∧ ∀x∀y(<x,y>∈S ↔ (x∈A ∧ y∈B))))
crossProductExistsTheorem :: PropDeBr
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
        pair_xy = buildPair (X x_idx) (X y_idx)
        pair_in_S = pair_xy `In` (X s_idx)
        
        x_in_A = X x_idx `In` (X a_idx)
        y_in_B = X y_idx `In` (X b_idx)
        x_in_A_and_y_in_B = x_in_A :&&: y_in_B

        biconditional = x_in_A_and_y_in_B :<->: pair_in_S

        -- Quantify over x and y: ∀x∀y(<x,y> ∈ S ↔ (x ∈ A ∧ y ∈ B))
        quantified_xy_bicond = aX x_idx (aX y_idx biconditional)

        -- Construct the property of the set S: isSet(S) ∧ ∀x∀y(...)
        isSet_S = isSet (X s_idx)
        property_of_S = isSet_S :&&: quantified_xy_bicond

        -- Quantify over S: ∃S (isSet(S) ∧ ∀x∀y(...))
        exists_S = eX s_idx property_of_S

        -- Construct the antecedent of the main implication: isSet(A) ∧ isSet(B)
        isSet_A = isSet (X a_idx)
        isSet_B = isSet (X b_idx)
        antecedent = isSet_A :&&: isSet_B

        -- Construct the main implication
        implication = antecedent :->: exists_S

    in
        -- Universally quantify over A and B to create the final closed theorem.
        -- multiAx [0, 1] is equivalent to aX 0 (aX 1 (...))
        multiAx [a_idx, b_idx] implication



-- | Proves the theorem: 'crossProductExistsTheorem'.
-- | 'crossProductDefEquivTheorem' is a required lemma for this proof.
proveCrossProductExistsM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m ()
proveCrossProductExistsM = do
    -- The theorem is universally quantified over two sets, A and B.
    -- We use multiUGM to handle the two ∀ quantifiers.
    multiUGM [(), ()] do
        -- Inside the UG, free variables v_B (most recent) and v_A are introduced.
        v_B <- getTopFreeVar
        context <- ask
        let v_A_idx = (length . freeVarTypeStack) context - 2
        let v_A = V v_A_idx
        let setA = v_A
        let setB = v_B

        -- Prove the main implication by assuming the antecedent.
        runProofByAsmM (isSet setA :&&: isSet setB) do
            -- Now, inside this assumption, we have proven `isSet setA` and `isSet setB`.
            (isSet_A_proven, _) <- PL.simpLM (isSet setA :&&: isSet setB)
            (isSet_B_proven, _) <- PL.simpRM (isSet setA :&&: isSet setB)
            
            -- Step 1: Prove that the universe U = P(P(A U B)) is a set.
            let universeSet = buildPowerSet (buildPowerSet (setA .\/. setB))
            (_, _, _) <- runProofBySubArgM do
                -- Step 1a: Get the theorem: ∀A'∀B'((isSet A' ∧ isSet B') → isSet(A'∪B'))
                (isSet_union_proven, _) <- proveUnionIsSetM setA setB

                (isSet_power_union, _) <- provePowerSetIsSetM (setA .\/. setB)

                -- Step 1d: Use the theorem again to prove isSet(P(P(A U B))).
                --(imp2, _) <- uiM (buildPowerSet (setA .\/. setB)) thm_powerset_is_set
                --(isSet_power_power_union, _) <- mpM imp2 -- Uses isSet_power_union
                (isSet_power_power_union,_) <- provePowerSetIsSetM (buildPowerSet (setA .\/. setB))

                return ()

            -- Step 2: Define the predicate P(z) for specification.
            let z_idx = 0; x_idx = 1; y_idx = 2; 
                setA_idx = 3; setB_idx = 4
            let universeSet_tmplt = buildPowerSet (buildPowerSet (X setA_idx .\/. X setB_idx))
            -- Define the predicate P(z) as ∃x
            let predicate_P = eX x_idx (eX y_idx (
                                  (X z_idx :==: buildPair (X x_idx) (X y_idx))
                                  :&&: (X x_idx `In` setA)
                                  :&&: (X y_idx `In` setB)
                              ))
            let predicate_P_tmplt = eX x_idx (eX y_idx (
                                  (X z_idx :==: buildPair (X x_idx) (X y_idx))
                                  :&&: (X x_idx `In` X setA_idx)
                                  :&&: (X y_idx `In` X setB_idx)
                              ))
            predicate_P_txt <- showPropM predicate_P_tmplt
            remarkM $ "Predicate P(z): " <> predicate_P_txt
            (definingProp_of_B, _, (crossProdObj,_,_)) <- builderInstantiateM [V 0, V 1]
                         [setA_idx, setB_idx] z_idx universeSet_tmplt predicate_P_tmplt

            -- Step 3: Use the theorem about definition equivalence to get the canonical property.

            (thm_equiv_inst1, _) <- uiM setA crossProductDefEquivTheorem
            (thm_equiv_inst2, _) <- uiM setB thm_equiv_inst1
            
            (imp_equiv, _) <- mpM thm_equiv_inst2
            (proven_property_of_B, _) <- mpM imp_equiv

            -- Step 4: Construct the target existential statement using the explicit template method.
            let s_idx_final = 0; x_idx_final = 1; y_idx_final = 2
            let element_prop_final = (X x_idx_final `In` setA) :&&: (X y_idx_final `In` setB)
            let pair_in_s_final = buildPair (X x_idx_final) (X y_idx_final) `In` (X s_idx_final)
            let quantified_bicond_final = aX x_idx_final (aX y_idx_final (element_prop_final :<->: pair_in_s_final))
            let target_property_for_S = isSet (X s_idx_final) :&&: quantified_bicond_final
            let target_existential = eX s_idx_final target_property_for_S

            -- Step 5: Apply Existential Generalization.
            crossProdObjTxt <- showObjM crossProdObj
            remarkM $ "CROSSPRODOBJ IS" <> crossProdObjTxt
            egM crossProdObj target_existential
    return ()



-- | The schema that houses 'proveCrossProductExistsM'.
-- | The schema stipulates that:
-- | "crossProductDefEquivTheorem" is a required lemma.
crossProductExistsSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
     TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
crossProductExistsSchema = 
    TheoremSchemaMT [] [binaryUnionExistsTheorem,crossProductDefEquivTheorem] proveCrossProductExistsM

-- | Helper to instantiate the cross product existence theorem and return the
-- | resulting cartesian product set.
-- | For this helper to work, the theorem defined by 'crossProductExistsTheorem' must be proven
-- | beforehand, which will likely be done in the global context.
crossProductInstantiateM ::  (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr -> ObjDeBr -> ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], ObjDeBr)
crossProductInstantiateM setA setB = do
    runProofBySubArgM do
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



-- | Applies Universal Instantiation (UI) multiple times to a given proposition.
-- | Returns the final instantiated proposition and its proof index.
-- | - Case 0: No instantiation terms -> re-proves the initial proposition.
-- | - Case 1: One instantiation term -> applies PREDL.uiM directly.
-- | - Case >1: Multiple terms -> creates a sub-argument for the sequen
multiUIM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    PropDeBr ->      -- initialProposition: The proposition to start with.
    [ObjDeBr] ->    -- instantiationTerms: List of terms to instantiate with, in order.
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr,[Int])
multiUIM initialProposition instantiationTerms =
    case instantiationTerms of
        [] ->
            -- Case 0: No terms to instantiate with.
            -- Re-prove the initial proposition to ensure it's the active "last proven statement"
            -- and to get its index in the current context.
            repM initialProposition

        [singleTerm] ->
            -- Case 1: Exactly one term to instantiate with.
            -- Apply PREDL.uiM directly. No need for a sub-argument wrapper.
            uiM singleTerm initialProposition

        _ -> -- More than one term (list has at least two elements here)
            -- Case 2: Multiple instantiation terms.
            -- Create a sub-argument whose internal proof is the sequence of UI steps.
            do
                (result_prop, idx, extra_data) <- runProofBySubArgM (
                    -- Use foldM to iteratively apply PREDL.uiM.
                    -- The accumulator for foldM is (current_proposition_term, its_index).
                    foldM
                        (\(currentProp_term, _currentProp_idx) term_to_instantiate ->
                            -- PREDL.uiM applies UI, proves the new proposition, adds it to proof steps,
                            -- updates the Last s writer state, and returns (new_proposition_term, new_index).
                            -- This (new_prop, new_idx) becomes the new accumulator.
                            uiM term_to_instantiate currentProp_term
                        )
                        (initialProposition, []) -- Start fold with initialProposition and a dummy index.
                        instantiationTerms
                    -- The result of this foldM is a monadic action of type m (PropDeBr, [Int]).
                    -- This is the 'prog' for runProofBySubArgM.
                    -- Its 'Last s' writer state (set by the last PREDL.uiM) will be used
                    -- by runProofBySubArgM as the 'consequent' of the sub-argument.
                    )
                return (result_prop, idx)



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
applyWellFoundednessM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr ->  -- subsetS
    ObjDeBr ->  -- domainD
    ObjDeBr ->  -- relationR
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], ())
applyWellFoundednessM subsetS domainD relationR =
    runProofBySubArgM do
        -- Step 1: Formally acknowledge the required premises from the outer context.
        -- The proof will fail if these are not already proven.
        let wellFoundedProp = isRelWellFoundedOn domainD relationR
        (isRelWellFounded_proven, _) <- repM wellFoundedProp

        let subset_and_nonempty_prop = (subsetS `subset` domainD) :&&: (subsetS ./=. EmptySet)
        (subset_and_nonempty_proven, _) <- repM subset_and_nonempty_prop

        -- Step 2: The proposition `isRelWellFounded_proven` is definitionally
        -- equivalent to ∀s((s⊆D ∧ s≠∅) → hasMinimalElement s R).
        -- We instantiate this with our specific subset `subsetS`.
        (instantiated_imp, _) <- uiM subsetS isRelWellFounded_proven
        -- `instantiated_imp` is now the proven proposition:
        -- (subsetS ⊆ domainD ∧ subsetS ≠ ∅) → hasMinimalElement subsetS relationR

        -- Step 3: Apply Modus Ponens. The antecedent for this implication is
        -- `subset_and_nonempty_proven`, which we acknowledged in Step 1.
        (has_minimal_proven, _) <- mpM instantiated_imp
        
        -- The last proven statement is now `hasMinimalElement subsetS relationR`, which is our goal.
        -- The () is the 'extraData' returned by the sub-argument.
        return ()







-- | A monadic helper that is employed by strongInductionTheoremProgFree.
-- |
-- |
deriveInductiveContradictionM :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) =>
    ObjDeBr ->  -- absurd_candidate
    ObjDeBr ->  -- dom
    ObjDeBr ->  -- rel_obj
    PropDeBr -> -- induction_premise
    PropDeBr -> -- spec_prop
    ProofGenTStd () [ZFC.LogicRule PropDeBr DeBrSe ObjDeBr] PropDeBr Text m (PropDeBr, [Int], ())
deriveInductiveContradictionM absurd_candidate dom rel_obj induction_premise spec_prop 
           =
    runProofBySubArgM do
        remarkM "DERIVING INDUCTIVE CONTRADICTION"
        let builderSubsetTmFree = absurd_candidate `subset` dom
        let absurd_asm = absurd_candidate./=. EmptySet
        let rel_is_relation = rel_obj `subset` (dom `crossProd` dom)
        (proves_false,_) <- runProofByAsmM absurd_asm do
            adjM builderSubsetTmFree absurd_asm
            (min_assertion,_,_) <- applyWellFoundednessM absurd_candidate dom rel_obj 
            (witnessed_min_assertion,_,min_element) <- eiHilbertM min_assertion
            ((min_element_in_absurd_set,idx_witnessed_min_assert) ,
             (absurd_set_elements_not_below_min,idxB)) <- deconstructAdjM witnessed_min_assertion            
            (induction_premise_on_min,idxA) <- uiM min_element induction_premise
            (some_statement,_) <- simpRM spec_prop
            (another_statement,_) <- uiM min_element some_statement
            (forward,_) <- bicondElimLM another_statement
            (after_forward,_) <- mpM forward
            simpLM after_forward
            (x,_) <- modusTollensM induction_premise_on_min
            (exists_statement, idx) <- aNegIntroM x
            (absurd_element_assert,_, absurd_element) <- eiHilbertM exists_statement     
            (more_absurd,_) <- negImpToConjViaEquivM absurd_element_assert
            (l_more_absurd,_) <- simpLM more_absurd


            repM l_more_absurd
            (r_more_absurd,_) <- simpRM more_absurd
            let absurd_element_in_n = absurd_element `In` natSetObj
            (something,_) <- simpRM rel_is_relation
            let xobj = buildPair absurd_element min_element
            (something_else,_) <- uiM xobj something
            mpM something_else


            (domXdomProps,_,domXdom)<- crossProductInstantiateM dom dom
            (ok, _) <- simpRM domXdomProps
            (idontknow,_) <- multiUIM ok [absurd_element,min_element]
            (noidea,_) <- bicondElimRM idontknow
            something_txt <- showObjM $ domXdom
            (whatever,_) <- simpRM rel_is_relation
            (imp_whatever,_) <- uiM xobj whatever
            (forward_imp,_) <- mpM imp_whatever
            (noclue, _) <- mpM noidea
            (whatever,_) <- simpLM noclue
            adjM r_more_absurd whatever
            let newProp = absurd_element `In` absurd_candidate
            (please_stop,_) <- simpRM spec_prop
            (almost,_) <- uiM absurd_element please_stop                
            (really_almost,_) <- bicondElimRM almost
            final_ante <- mpM really_almost
            (final_imp,_) <- uiM absurd_element absurd_set_elements_not_below_min
            (next,_) <- mpM final_imp

            contraFM l_more_absurd
        return ()

strongInductionTheoremProgFree::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
               Int -> ObjDeBr -> PropDeBr -> ProofGenTStd () [ZFCRuleDeBr] PropDeBr Text m (PropDeBr,[Int])
strongInductionTheoremProgFree idx dom p_pred = do
            let rel_idx = idx + 1
            let asmMain = eX rel_idx (
                           X rel_idx `subset` (dom `crossProd` dom)
                               :&&: isRelWellFoundedOn dom (X rel_idx)
                                :&&: strongInductionPremiseOnRel p_pred idx dom (X rel_idx))
            let (anti_spec_prop,anti_absurd_candidate) = builderPropsFree idx dom p_pred
            let (spec_prop, absurd_candidate) = builderPropsFree idx dom (neg p_pred)
            let builderSubsetTmFree = builderSubsetTheorem [] idx dom (neg p_pred)
            let specAntiRedundancyTmFreeConditional = specAntiRedundancyTheorem [] idx dom p_pred
            (specAntiRedundancyTmFree,_) <- mpM specAntiRedundancyTmFreeConditional
            runProofByAsmM asmMain do
                (asm_after_ei,_,rel_obj) <- eiHilbertM asmMain
                (rel_is_relation,rel_is_relation_idx) <- simpLM asm_after_ei
                (bAndC,_) <- simpRM asm_after_ei
                (well_founded,well_founded_idx) <- simpLM bAndC
                (induction_premise,induction_premise_idx) <- simpRM bAndC
                remarkM $   (pack . show) rel_is_relation_idx <> " asserts that rel is a relation over N.\n" 
                           <> (pack . show) well_founded_idx <> " asserts that rel is well-founded over N.\n"
                           <> (pack . show) induction_premise_idx <> " asserts that the induction premise holds for N"
                
                (proves_false,_,()) <- deriveInductiveContradictionM absurd_candidate dom rel_obj 
                          induction_premise spec_prop

                (double_neg,_) <- absurdM proves_false
                (final_generalization_set_version,_) <- doubleNegElimM double_neg
                (final_imp,_) <- bicondElimLM specAntiRedundancyTmFree

                
                mpM final_imp






strongInductionTheoremProg::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
               [Int] -> Int -> ObjDeBr -> PropDeBr -> ProofGenTStd () [ZFCRuleDeBr] PropDeBr Text m ()
strongInductionTheoremProg outerTemplateIdxs idx dom_template p_template = do



    let builderSubsetTmInstance = builderSubsetTheorem outerTemplateIdxs idx dom_template (neg p_template)
    let specAntiRedundancyTmInstance = specAntiRedundancyTheorem outerTemplateIdxs idx dom_template p_template
    

    multiUGM (replicate (length outerTemplateIdxs) ()) do
        -- Inside the UG, we have free variables (V_i) corresponding to the X_k parameters.
        freeVarCount <- getFreeVarCount
        let instantiationTerms = Prelude.map V [0 .. freeVarCount - 1]

        (_,_,(_,dom,_)) <- builderInstantiateM instantiationTerms outerTemplateIdxs idx 
                          dom_template (neg p_template)
        (_,_,(_,_,p_pred)) <- 
                          builderInstantiateM instantiationTerms outerTemplateIdxs idx dom_template p_template

                        

        multiUIM builderSubsetTmInstance instantiationTerms
        multiUIM specAntiRedundancyTmInstance instantiationTerms
        let rel_idx = idx + 1

        let isSetDom = isSet dom
        (main_imp, _) <- runProofByAsmM isSetDom do
            strongInductionTheoremProgFree idx dom p_pred
        let asmMain = eX rel_idx (
                           X rel_idx `subset` (dom `crossProd` dom)
                               :&&: isRelWellFoundedOn dom (X rel_idx)
                                :&&: strongInductionPremiseOnRel p_pred idx dom (X rel_idx))
        let full_asm = isSetDom .&&. asmMain
        runProofByAsmM full_asm do
            (isSet_dom,_) <- simpLM full_asm
            (sub_imp,_) <- mpM main_imp
            (inductive_asm,_) <- simpRM full_asm
            mpM sub_imp
    return ()


strongInductionTheoremMSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => 
     [Int] -> Int -> ObjDeBr -> PropDeBr -> TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text m ()
strongInductionTheoremMSchema outerTemplateIdxs spec_var_idx dom p_template= 
    let
      dom_tmplt_consts = extractConstsTerm dom
      p_tmplt_consts = extractConstsSent p_template
      all_consts = dom_tmplt_consts `Set.union` p_tmplt_consts
      typed_consts = zip (Data.Set.toList all_consts) (repeat ()) 
    in
      TheoremSchemaMT typed_consts [crossProductExistsTheorem
                              , builderSubsetTheorem outerTemplateIdxs spec_var_idx dom (neg p_template)
                              , specAntiRedundancyTheorem outerTemplateIdxs spec_var_idx dom p_template
                             ] (strongInductionTheoremProg outerTemplateIdxs spec_var_idx dom p_template)



testEqualityRules :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testEqualityRules = do
    remarkM "--- Testing Equality Rules ---"

    -- Test eqReflM
    remarkM "Testing eqReflM (0 == 0):"
    let term0 = Integ 0
    (reflSent, reflIdx) <- eqReflM term0
    reflShow <- showPropM reflSent
    remarkM $ "Proved: " <> reflShow <> " at index " <> pack (show reflIdx)

    -- Test eqSymM
    remarkM "Testing eqSymM (given fake 1 == 2):"
    let term1 = Integ 1
    let term2 = Integ 2
    let eq12 = term1 :==: term2
    (eq12Sent, eq12Idx) <- fakePropM [] eq12 -- Assume 1==2 is proven for the test
    eq12Show <- showPropM eq12Sent
    remarkM $ "Assuming: " <> eq12Show <> " at index " <> pack (show eq12Idx)
    (symSent, symIdx) <- eqSymM eq12Sent
    symShow <- showPropM symSent
    remarkM $ "Proved: " <> symShow <> " at index " <> pack (show symIdx)

    -- Test eqTransM
    remarkM "Testing eqTransM (given fake 1 == 2 and 2 == 3):"
    let term3 = Integ 3
    let eq23 = term2 :==: term3
    (eq23Sent, eq23Idx) <- fakePropM []eq23 -- Assume 2==3 is proven
    eq23Show <- showPropM eq23Sent
    remarkM $ "Assuming: " <> eq23Show <> " at index " <> pack (show eq23Idx)
    (transSent, transIdx) <- eqTransM eq12Sent eq23Sent -- Use eq12Sent from previous step
    transShow <- showPropM transSent
    remarkM $ "Proved: " <> transShow <> " at index " <> pack (show transIdx)

    -- Test eqSubstM
    remarkM "Testing eqSubstM (template X0 == X0, given fake 5 == 6):"
    let template = X 0 :==: X 0
    let term5 = Integ 5
    let term6 = Integ 6
    let eq56 = term5 :==: term6
    -- Prove the source sentence P(a), which is 5 == 5
    (sourceSent, sourceIdx) <- eqReflM term5 -- Use eqReflM to prove 5==5
    sourceShow <- showPropM sourceSent
    remarkM $ "Proved source: " <> sourceShow <> " at index " <> pack (show sourceIdx)
    -- Assume the equality a == b, which is 5 == 6
    (eqSent, eqIdx) <- fakePropM [] eq56
    eqShow <- showPropM eqSent
    remarkM $ "Assuming equality: " <> eqShow <> " at index " <> pack (show eqIdx)
    -- Perform substitution
    (substSent, substIdx) <- eqSubstM 0 template eqSent -- Use the template, not the source sentence here
    substShow <- showPropM substSent
    remarkM $ "Proved subst: " <> substShow <> " at index " <> pack (show substIdx)

    remarkM "--- Equality Rule Tests Complete ---"
    return ()

testNormalization :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testNormalization = do
    remarkM "--- Testing Normalization ---"
    let term2 = Integ 1
    let s1 = aX 1 (eXBang 0 (X 1 :==: X 0))


    fakeConstM "N" ()
    fakePropM [] s1
    s1Show <- showPropM s1
    remarkM $ "Proved: " <> s1Show   
    return ()
 
testMoreComplexNesting :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testMoreComplexNesting = do
    remarkM "--- Testing More Complex Nesting (A > E > E!) ---"
    
    -- Represents ∀𝑥₂ ( ∃𝑥₁ ( ∃!𝑥₀ ( (𝑥₂ = 𝑥₁) ∧ (𝑥₁ = 𝑥₀) ) ) )
    let s3 = aX 2 ( eX 1 ( eXBang 0 ( (X 2 :==: X 1) :&&: (X 1 :==: X 0) ) ) )

    -- Add as fake prop and print
    fakePropM []s3
    s3Show <- showPropM s3
    remarkM "Input: aX 2 ( eX 1 ( eXBang 0 ( (X 2 :==: X 1) :&&: (X 1 :==: X 0) ) ) )"
    remarkM $ "Printed: " <> s3Show   
    
    remarkM "--- More Complex Nesting Test Complete ---"
    return ()

testNonSequentialIndices :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testNonSequentialIndices = do
    remarkM "--- Testing Non-Sequential Indices (A5 > E!2 > A7) ---"

    -- Represents ∀𝑥₅ ( ∃!𝑥₂ ( ∀𝑥₇ ( (𝑥₅ = 𝑥₂) ∨ (𝑥₂ = 𝑥₇) ) ) )
    let s4 = aX 5 ( eXBang 2 ( aX 7 ( (X 5 :==: X 2) :||: (X 2 :==: X 7) ) ) )

    -- Add as fake prop and print
    fakePropM [] s4
    s4Show <- showPropM s4
    remarkM "Input: aX 5 ( eXBang 2 ( aX 7 ( (X 5 :==: X 2) :||: (X 2 :==: X 7) ) ) )"
    remarkM $ "Printed: " <> s4Show

    remarkM "--- Non-Sequential Indices Test Complete ---"
    return ()






testComplexSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testComplexSubsetNotation = do
    remarkM "--- Testing More Complex Subset Notation (⊆) ---"

    -- 1. Define constants to represent sets
    let setN = Constant "N"
    let setA = Constant "A" -- Placeholder for Test 1 & 2
    let setB = Constant "B"
    let setC = Constant "C"

    -- 2. Add constants to the proof state
    fakeConstM "N" () -- Needed for Test 3
    fakeConstM "A" () -- Assume these are defined/exist for the test
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- 3. Test 1: Basic subset A B
    remarkM "Test 1: Basic subset A B"
    let subPropAB = subset setA setB
    (addedProp1, _) <- fakePropM [] subPropAB
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM "(Should be A ⊆ B)"

    -- 4. Test 2: Subset notation within a conjunction: (A ⊆ B) ∧ (B ⊆ C)
    remarkM "Test 2: Subset notation within conjunction (A ⊆ B) ∧ (B ⊆ C)"
    let subPropBC = subset setB setC
    -- Construct the conjunction using the PropDeBr operator :&&:
    let conjProp = subPropAB :&&: subPropBC
    (addedConjProp, _) <- fakePropM [] conjProp
    printedOutputConj <- showPropM addedConjProp
    remarkM $ "Actual printed output (Test 2): " <> printedOutputConj
    -- Note: Depending on operator precedence for ∧ and ⊆, parentheses might appear
    remarkM "(Should look like (A ⊆ B) ∧ (B ⊆ C) or similar)"

    -- 5. Test 3: Using a set builder expression {x ∈ N | x ≥ 5} ⊆ N
    remarkM "Test 3: Checking print for {x ∈ N | x ≥ 5} ⊆ N"
    -- Ensure N constant is added (done above)
    let five = Integ 5
    -- Define the property P(x) as x <= 5, using X 0 for the bound variable 'x'
    let propertyP = X 0 :<=: five
    -- Construct the set {x ∈ N | x ≥ 5} using builderX with index 0
    let setBuilderA = builderX 0 setN propertyP -- Defined in Langs/BasicUntyped.hs
    -- Create the subset proposition: {x ∈ N | x ≥ 5} ⊆ N
    let subPropBuilder = subset setBuilderA setN
    -- Add, print, and check the output
    (addedPropBuilder, _) <- fakePropM []subPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 3): " <> printedOutputBuilder
    remarkM "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊆ N or similar)"

    remarkM "--- Complex Subset Notation Test Complete ---"
    return ()

testStrictSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testStrictSubsetNotation = do
    remarkM "--- Testing Strict Subset Notation (⊂) ---"

    -- 1. Define constants
    let setA = Constant "A"
    let setB = Constant "B"
    let setN = Constant "N"

    -- 2. Add constants to proof state
    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "N" ()

    -- 3. Test 1: Basic strict subset A ⊂ B
    remarkM "Test 1: Basic strict subset A ⊂ B"
    -- This assumes strictSubset a b = subset a b :&&: Neg (a :==: b)
    let strictSubProp1 = strictSubset setA setB
    (addedProp1, _) <- fakePropM [] strictSubProp1
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM "(Should be A ⊂ B)"

    -- 4. Test 2: Strict subset with set builder {x ∈ N | x ≥ 5} ⊂ N
    remarkM "Test 2: Strict subset involving a Set Builder expression"
    let five = Integ 5
    let propertyP = X 0 :<=: five
    let setBuilderA = builderX 0 setN propertyP -- {x ∈ N | x ≥ 5}
    -- Create the strict subset proposition: {x ∈ N | x ≥ 5} ⊂ N
    let strictSubPropBuilder = strictSubset setBuilderA setN
    (addedPropBuilder, _) <- fakePropM [] strictSubPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 2): " <> printedOutputBuilder
    remarkM "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊂ N or similar)"

    -- 5. Test 3: A structure that should NOT use the ⊂ notation
    remarkM "Test 3: Structure that should NOT print as ⊂ (using A=A instead of Not(A=B))"
    -- Example: (A ⊆ B) ∧ (A = A) -- Does not match Neg(A==B)
    (eqAA, _) <- eqReflM setA -- Prove A = A using EqRefl rule
    let subPropAB = subset setA setB -- A ⊆ B part
    let nonStrictSubProp = subPropAB :&&: eqAA -- Combine with A=A
    (addedProp3, _) <- fakePropM [] nonStrictSubProp
    printedOutput3 <- showPropM addedProp3
    remarkM $ "Actual printed output (Test 3): " <> printedOutput3
    remarkM "(Should be (A ⊆ B) ∧ (A = A) or similar, *NOT* A ⊂ B)"

    remarkM "--- Strict Subset Notation Test Complete ---"
    return ()


testNotSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testNotSubsetNotation = do
    remarkM "--- Testing Not Subset Notation (⊈) ---"

    -- 1. Define constants
    let setA = Constant "A"
    let setB = Constant "B"
    let setN = Constant "N"

    -- 2. Add constants to proof state
    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "N" ()

    -- 3. Test 1: Basic not subset A ⊈ B
    remarkM "Test 1: Basic not subset A ⊈ B"
    -- Assumes notSubset a b = Neg (subset a b)
    let notSubProp1 = notSubset setA setB
    (addedProp1, _) <- fakePropM [] notSubProp1
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM "(Should be A ⊈ B)"

    -- 4. Test 2: Not subset with set builder {x ∈ N | x ≥ 5} ⊈ N
    remarkM "Test 2: Not subset involving a Set Builder expression"
    let five = Integ 5
    let propertyP = X 0 :<=: five
    let setBuilderA = builderX 0 setN propertyP -- {x ∈ N | x ≥ 5}
    -- Create the not subset proposition: {x ∈ N | x ≥ 5} ⊈ N
    let notSubPropBuilder = notSubset setBuilderA setN
    (addedPropBuilder, _) <- fakePropM [] notSubPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 2): " <> printedOutputBuilder
    remarkM "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊈ N or similar)"

    -- 5. Test 3: A structure that should NOT use the ⊈ notation
    remarkM "Test 3: Structure that should NOT print as ⊈"
    -- Example: Neg (A ⊂ B) -- Should print as ¬(A ⊂ B), not A ⊈ B
    let strictSubProp = strictSubset setA setB -- Assuming this helper exists and works
    let negStrictSubProp = Neg strictSubProp
    (addedProp3, _) <- fakePropM []negStrictSubProp
    printedOutput3 <- showPropM addedProp3
    remarkM $ "Actual printed output (Test 3): " <> printedOutput3
    remarkM "(Should be ¬(A ⊂ B) or similar, *NOT* related to ⊈)"

    remarkM "--- Not Subset Notation Test Complete ---"
    return ()



testHelperPreconditionViolation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testHelperPreconditionViolation = do
    remarkM "--- Testing Helper Precondition Violation ---"
    let setN = Constant "N"
    let constC = Constant "C"
    let setB = Constant "B"

    fakeConstM "N" ()
    fakeConstM "C" ()
    fakeConstM "B" ()

    -- Construct A = {x ∈ N | x = C} using builderX
    -- This term 'setA' contains Bound 1 internally. Its depth is 1.
    let setA = builderX 0 setN (X 0 :==: constC)
    setAShow <- showObjM setA -- See the structure (likely involves Bound 1)
    remarkM $ "Constructed setA = " <> setAShow

    -- Construct subset A B
    -- This calculates idx = max(depth A, depth B) = max(1, 0) = 1.
    -- Precondition requires A not contain Bound 1, but it does.
    let violatingSubsetProp = subset setA setB
    remarkM "Constructed 'subset setA setB'. Precondition (A must not contain Bound 1) is VIOLATED."

    -- Add it to the proof state. It might pass checkSanity if the check isn't perfect,
    -- but it represents a violation of the helper's intended use conditions.
    (addedProp, _) <- fakePropM [] violatingSubsetProp
    printedProp <- showPropM addedProp
    remarkM $ "Resulting PropDeBr structure (printed form): " <> printedProp
    remarkM "(Check if it printed using ⊆ or fallback ∀ notation)"
    remarkM "--- Precondition Violation Test Complete ---"
    return ()


testBuilderXSuite :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testBuilderXSuite = do
    remarkM "--- Starting New builderX Test Suite ---"

    -- Prerequisite Constants
    fakeConstM "N" () -- Natural numbers (example source set)
    fakeConstM "M" () -- Another example set
    fakeConstM "C" () -- A specific constant element
    let setN = Constant "N"
    let setM = Constant "M"
    let constC = Constant "C"
    let int5 = Integ 5

    -- Test 1: Simple Predicate (x <= 5)
    remarkM "Test 1: Simple Predicate { x ∈ N | x ≥ 5 }"
    let prop1 = X 0 :<=: int5
    let builtSet1 = builderX 0 setN prop1
    builtSet1Show <- showObjM builtSet1
    remarkM $ "Constructed (idx=0): " <> builtSet1Show
    remarkM "(Expected: {𝑥₀ ∈ N | 𝑥₀ ≥ 5})"

    -- Test 2: Predicate with Equality (x == C)
    remarkM "Test 2: Predicate with Equality { x ∈ N | x == C }"
    let prop2 = X 0 :==: constC
    let builtSet2 = builderX 0 setN prop2
    builtSet2Show <- showObjM builtSet2
    remarkM $ "Constructed (idx=0): " <> builtSet2Show
    remarkM "(Expected: {𝑥₀ ∈ N | 𝑥₀ = C})"

    -- Test 3: Using a different index (idx=1)
    remarkM "Test 3: Using Different Index { x ∈ N | x ≥ 5 }"
    let prop3 = X 1 :<=: int5 -- Using X 1 now
    let builtSet3 = builderX 1 setN prop3 -- Using index 1
    builtSet3Show <- showObjM builtSet3
    remarkM $ "Constructed (idx=1): " <> builtSet3Show
    remarkM "(Expected: {𝑥₁ ∈ N | 𝑥₁ ≥ 5})"

    -- Test 4: Predicate with nested quantifiers (∀y (y ∈ M -> x = y))
    remarkM "Test 4: Nested Quantifier in Predicate { x ∈ N | ∀y (y ∈ M → x = y) }"
    -- Predicate: aX 1 ( (X 1 `In` setM) :->: (X 0 :==: X 1) )
    -- Here, x is X 0 (bound by builderX), y is X 1 (bound by aX)
    let prop4 = aX 1 ( (X 1 `In` setM) :->: (X 0 :==: X 1) )
    let builtSet4 = builderX 0 setN prop4 -- Using index 0 for x
    builtSet4Show <- showObjM builtSet4
    remarkM $ "Constructed (idx=0): " <> builtSet4Show
    remarkM "(Expected: {𝑥₀ ∈ N | ∀𝑥₁((𝑥₁ ∈ M) → (𝑥₀ = 𝑥₁))})"

    -- Test 5: Complex Predicate with Existential Quantifier
    remarkM "Test 5: Complex Predicate { x ∈ N | ∃y (y ∈ M ∧ x = <y, C>) }"
    -- Predicate: eX 1 ( (X 1 `In` setM) :&&: (X 0 :==: Pair (X 1) constC) )
    -- Here, x is X 0 (bound by builderX), y is X 1 (bound by eX)
    let prop5 = eX 1 ( (X 1 `In` setM) :&&: (X 0 :==: buildPair (X 1) constC) )
    let builtSet5 = builderX 0 setN prop5 -- Using index 0 for x
    builtSet5Show <- showObjM builtSet5
    remarkM $ "Constructed (idx=0): " <> builtSet5Show
    remarkM "(Expected: {𝑥₀ ∈ N | ∃𝑥₁((𝑥₁ ∈ M) ∧ (𝑥₀ = <𝑥₁, C>))})"

    -- Test 6: Using a different source set M
    remarkM "Test 6: Different Source Set { x ∈ M | x == C }"
    let prop6 = X 0 :==: constC
    let builtSet6 = builderX 0 setM prop6 -- Source set is M
    builtSet6Show <- showObjM builtSet6
    remarkM $ "Constructed (idx=0): " <> builtSet6Show
    remarkM "(Expected: {𝑥₀ ∈ M | 𝑥₀ = C})"

    -- Test 7: Predicate always true (using x == x)
    remarkM "Test 7: Predicate Always True { x ∈ N | x == x }"
    let prop7 = X 0 :==: X 0
    let builtSet7 = builderX 0 setN prop7
    builtSet7Show <- showObjM builtSet7
    remarkM $ "Constructed (idx=0): " <> builtSet7Show
    remarkM "(Expected: {𝑥₀ ∈ N | 𝑥₀ = 𝑥₀})"

    -- Test 8: Predicate involving other template variables (if needed later)
    -- remarkM "Test 8: Predicate with other X vars - Placeholder"
    -- let prop8 = (X 0 :==: X 99) -- Example, assuming X 99 is defined elsewhere
    -- let builtSet8 = builderX 0 setN prop8
    -- builtSet8Show <- showObjM builtSet8
    -- remarkM $ "Constructed (idx=0): " <> builtSet8Show
    -- remarkM "(Shows interaction with other template vars if applicable)"

    remarkM "--- builderX Test Suite Complete ---"
    return ()


testCompositionImplementation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testCompositionImplementation = do
    remarkM "--- Testing Composition Implementation (with Tupl [dom, cod, graph] assumption) ---"

    -- Define simple functions and argument
    -- NOTE: We assume f and g are now represented as triples Tupl[dom,cod,graph]
    -- For this test, we still use Constants, assuming they represent such triples.
    let f = Constant "F"
    let g = Constant "G"
    let x = Constant "A"
    fakeConstM "F" () -- Represents function F as Tupl[DomF, CodF, GraphF]
    fakeConstM "G" () -- Represents function G as Tupl[DomG, CodG, GraphG]
    fakeConstM "A" () -- Represents argument A
    remarkM "Using f = F, g = G, x = A"

    -- 1. Calculate h = f .:. g using the definition based on compositionTemplate
    remarkM "Calculating h = f .:. g"
    let h = f .:. g -- Assumes .:. uses compositionTemplate which uses the new .@.
    hShow <- showObjM h
    remarkM $ "Constructed h: " <> hShow
    remarkM "(Note: This will be a complex Hilbert term based on compositionTemplate and the new .@.)"

    -- 2. Calculate h .@. x using the new .@. definition
    remarkM "Calculating h .@. x"
    -- This now uses: objDeBrSubXs [(0,h),(1,x)] (hX 2 ( Tupl [X 1, X 2] `In` tripletLast (X 0) ))
    let applied_h = h .@. x
    applied_h_Show <- showObjM applied_h
    remarkM $ "Result (h .@. x): " <> applied_h_Show
    remarkM "(Note: This involves substituting h and x into the .@. template containing tripletLast)"

    -- 3. Calculate f .@. (g .@. x) separately using the new .@.
    remarkM "Calculating f .@. (g .@. x) separately"
    -- Inner application: g .@. x
    let applied_g = g .@. x
    applied_g_Show <- showObjM applied_g
    remarkM $ "  Inner (g .@. x): " <> applied_g_Show
    -- Outer application: f .@. applied_g
    let expected_result = f .@. applied_g
    expected_result_Show <- showObjM expected_result
    remarkM $ "  Outer f .@. (g .@. x): " <> expected_result_Show

    -- 4. Compare (visually via remarks)
    remarkM "--- Comparison ---"
    remarkM $ "h .@. x             => " <> applied_h_Show
    remarkM $ "f .@. (g .@. x)     => " <> expected_result_Show
    remarkM "Check if the final term structures match visually."
    remarkM "WARNING: Visual comparison of these complex Hilbert terms might be difficult."
    remarkM "Consider adding a formal proof step to check equality if possible."
    remarkM "If they differ structurally, there might be an issue in how .:. or .@. interacts with the substitutions."

    remarkM "--- Composition Implementation Test Complete ---"
    return ()

testShorthandRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testShorthandRendering = do
    remarkM "--- Testing Shorthand Rendering (Post Function Triple Change) ---"

    -- Setup Constants
    let a = Constant "A"
    let b = Constant "B"
    let n = Constant "N"
    -- Assume f, g represent function triples Tupl[_, _, _]
    let f = Constant "f"
    let g = Constant "g"
    let x_arg = Constant "x_arg" -- Argument for functions

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "N" ()
    fakeConstM "f" () -- Represents function f
    fakeConstM "g" () -- Represents function g
    fakeConstM "x_arg" () -- Represents an argument

    let five = Integ 5
    let zero = Integ 0

    -- Test 1: Function Application (.@.) -> f(x_arg)
    remarkM "Test 1: f .@. x_arg"
    -- Uses the new .@. definition internally
    let app_f_x = f .@. x_arg
    app_f_x_show <- showObjM app_f_x
    remarkM "  Input Term (structure depends on new .@.): f .@. x_arg"
    remarkM $ "  Actual Rendered:   " <> app_f_x_show
    remarkM "  Expected Rendered: f(x_arg)"
    remarkM "  (Success depends on parseFuncApplication recognizing the new structure)"

    -- Test 2: Nested Function Application -> f(g(x_arg))
    remarkM "Test 2: f .@. (g .@. x_arg)"
    let app_g_x = g .@. x_arg
    let app_f_gx = f .@. app_g_x
    app_f_gx_show <- showObjM app_f_gx
    remarkM "  Input Term: f .@. (g .@. x_arg)"
    remarkM $ "  Actual Rendered:   " <> app_f_gx_show
    remarkM "  Expected Rendered: f(g(x_arg))"
    remarkM "  (Success depends on parseFuncApplication recognizing nested new structures)"

    -- Test 3: Function Composition (.:.) -> f ∘ g
    remarkM "Test 3: f .:. g"
    -- Assumes .:. uses compositionTemplate which uses the new .@.
    let comp_f_g = f .:. g
    comp_f_g_show <- showObjM comp_f_g
    remarkM "  Input Term (structure depends on new .@. via template): f .:. g"
    remarkM $ "  Actual Rendered:   " <> comp_f_g_show
    remarkM "  Expected Rendered: f ∘ g"
    remarkM "  (Success depends on parseComposition recognizing the template structure)"

    -- Test 3b: Apply composed function -> (f ∘ g)(x_arg)
    remarkM "Test 3b: (f .:. g) .@. x_arg"
    let app_comp_x = comp_f_g .@. x_arg
    app_comp_x_show <- showObjM app_comp_x
    remarkM "  Input Term: (f .:. g) .@. x_arg"
    remarkM $ "  Actual Rendered:   " <> app_comp_x_show
    remarkM "  Expected Rendered: (f ∘ g)(x_arg)"
    remarkM "  (Success depends on parseFuncApplication recognizing the composed structure)"

    -- == Other tests remain largely the same, as they don't depend on the function representation ==

    -- Test 4: Set Builder -> { x ∈ N | x ≥ 5 }
    remarkM "Test 4: builderX 0 N (X 0 :<=: 5)"
    let builder_n_ge_5 = builderX 0 n (X 0 :<=: five)
    builder_n_ge_5_show <- showObjM builder_n_ge_5
    remarkM "  Input: builderX 0 N (X 0 :<=: 5)"
    remarkM $ "  Actual:   " <> builder_n_ge_5_show
    remarkM "  Expected: {𝑥₀ ∈ N | 𝑥₀ ≥ 5}"

    -- Test 5: Hilbert Epsilon Shorthand -> ε[index]
    remarkM "Test 5: Hilbert ε shorthand (requires proven Exists)"
    let hilbert_prop = X 0 :==: a -- Example property P(x) = (x == A)
    let hilbert_term = hX 0 hilbert_prop -- εx.(x == A)
    let exists_prop = eX 0 hilbert_prop -- ∃x.(x == A)
    (fake_exists, fake_idx) <- fakePropM [] exists_prop
    exists_show <- showPropM fake_exists -- Show the prop being faked
    remarkM $ "  Faking proof of: " <> exists_show  <> " at index " <> pack (show fake_idx)
    hilbert_term_short_show <- showObjM hilbert_term
    remarkM "  Input: hX 0 (X 0 :==: A)  (after proving Exists)"
    remarkM $ "  Actual:   " <> hilbert_term_short_show
    remarkM $ "  Expected: ε" <> pack (show fake_idx) -- Adjust format if needed

    -- Test 6: Default Hilbert -> εx.(...)
    remarkM "Test 6: Default Hilbert ε binding"
    let hilbert_term_default = hX 1 (X 1 :<=: zero) -- εx.(x <= 0)
    hilbert_term_default_show <- showObjM hilbert_term_default
    remarkM "  Input: hX 1 (X 1 :<=: 0)"
    remarkM $ "  Actual:   " <> hilbert_term_default_show
    remarkM "  Expected: ε𝑥₁(𝑥₁ ≥ 0)"

    -- Test 7: Subset (⊆)
    remarkM "Test 7: subset A B"
    let subset_a_b = subset a b
    subset_a_b_show <- showPropM subset_a_b
    remarkM "  Input: subset A B"
    remarkM $ "  Actual:   " <> subset_a_b_show
    remarkM "  Expected: A ⊆ B"

    -- Test 8: Strict Subset (⊂)
    remarkM "Test 8: strictSubset A B"
    let strictsubset_a_b = strictSubset a b
    strictsubset_a_b_show <- showPropM strictsubset_a_b
    remarkM "  Input: strictSubset A B"
    remarkM $ "  Actual:   " <> strictsubset_a_b_show
    remarkM "  Expected: A ⊂ B"

    -- Test 9: Not Subset (⊈)
    remarkM "Test 9: notSubset A B"
    let notsubset_a_b = notSubset a b
    notsubset_a_b_show <- showPropM notsubset_a_b
    remarkM "  Input: notSubset A B"
    remarkM $ "  Actual:   " <> notsubset_a_b_show
    remarkM "  Expected: A ⊈ B"

    -- Test 10: Exists Unique (∃!)
    remarkM "Test 10: eXBang 0 (X 0 :==: A)"
    let existsunique_a = eXBang 0 (X 0 :==: a)
    existsunique_a_show <- showPropM existsunique_a
    remarkM "  Input: eXBang 0 (X 0 :==: A)"
    remarkM $ "  Actual:   " <> existsunique_a_show
    remarkM "  Expected: ∃!𝑥₀(𝑥₀ = A)"

    -- Test 11: Not Equal (≠)
    remarkM "Test 11: A ./=. B"
    let notequal_a_b = a ./=. b -- Or Neg (a :==: b)
    notequal_a_b_show <- showPropM notequal_a_b
    remarkM "  Input: A ./=. B"
    remarkM $ "  Actual:   " <> notequal_a_b_show
    remarkM "  Expected: A ≠ B"

    -- Test 12: Not In (∉)
    remarkM "Test 12: A `nIn` B"
    let notin_a_b = a `nIn` b -- Or Neg (a `In` b)
    notin_a_b_show <- showPropM notin_a_b
    remarkM "  Input: A `nIn` B"
    remarkM $ "  Actual:   " <> notin_a_b_show
    remarkM "  Expected: A ∉ B"

    remarkM "--- Shorthand Rendering Tests Complete ---"
    return ()





testProjectShorthandParsing :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testProjectShorthandParsing = do
    remarkM "--- Testing Project Shorthand Parsing (via Rendering) ---"

    -- Setup Constants and Variables
    let tupleA = Constant "MyTupleA"
    let tupleB = Constant "MyTupleB"
    let constA = Constant "A"
    let constB = Constant "B"
    let constC = Constant "C"

    fakeConstM "MyTupleA" ()
    fakeConstM "MyTupleB" ()
    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- == Positive Cases ==

    -- Test 1: Simple 2-tuple, project index 0
    remarkM "Test 1: Project 2 0 MyTupleA"
    let proj_2_0_A = project 2 0 tupleA -- Generate term using helper
    proj_2_0_A_show <- showObjM proj_2_0_A
    remarkM "  Input:    project 2 0 MyTupleA"
    remarkM $ "  Actual:   " <> proj_2_0_A_show
    remarkM "  Expected: π₀(MyTupleA)"

    -- Test 2: Simple 2-tuple, project index 1
    remarkM "Test 2: Project 2 1 MyTupleA"
    let proj_2_1_A = project 2 1 tupleA
    proj_2_1_A_show <- showObjM proj_2_1_A
    remarkM "  Input:    project 2 1 MyTupleA"
    remarkM $ "  Actual:   " <> proj_2_1_A_show
    remarkM "  Expected: π₁(MyTupleA)"

    -- Test 3: 3-tuple, project index 1
    remarkM "Test 3: Project 3 1 MyTupleB"
    let proj_3_1_B = project 3 1 tupleB
    proj_3_1_B_show <- showObjM proj_3_1_B
    remarkM "  Input:    project 3 1 MyTupleB"
    remarkM $ "  Actual:   " <> proj_3_1_B_show
    remarkM "  Expected: π₁(MyTupleB)"

    -- Test 4: Nested projection (term `t` is itself a projection)
    remarkM "Test 4: Project 2 0 (project 2 1 MyTupleA)"
    let inner_proj = project 2 1 tupleA
    let outer_proj = project 2 0 inner_proj
    outer_proj_show <- showObjM outer_proj
    remarkM "  Input:    project 2 0 (project 2 1 MyTupleA)"
    remarkM $ "  Actual:   " <> outer_proj_show
    remarkM "  Expected: π₀(π₁(MyTupleA))"

    -- Test 5: A standard Hilbert term that doesn't match the project structure
    remarkM "Test 5: Standard Hilbert term hX 0 (X 0 :==: Constant A)"
    let simpleHilbert = hX 0 (X 0 :==: constA)
    simpleHilbert_show <- showObjM simpleHilbert
    remarkM "  Input:    hX 0 (X 0 :==: Constant A)"
    remarkM $ "  Actual:   " <> simpleHilbert_show
    remarkM "  Expected: ε𝑥₀(𝑥₀ = A)  (or similar default Hilbert rendering, NOT π)"

    -- == Negative Cases (Should Fail Parsing) ==

    -- Test 6 (Negative Case - RHS Not a Tuple)
    remarkM "Test 6: Hilbert term where RHS of equality is not a Tuple"
    let nonTupleRHS = hX 1 ( eX 0 ( Constant "A" :==: Constant "B" ) )
    nonTupleRHS_show <- showObjM nonTupleRHS
    remarkM "  Input:    hX 1 ( eX 0 ( Constant \"A\" :==: Constant \"B\" ) )"
    remarkM $ "  Actual:   " <> nonTupleRHS_show
    remarkM "  Expected: ε𝑥₁(∃𝑥₀(A = B)) (Default Hilbert rendering, NOT π)"





    -- Test 7 (Negative Case - Body Not Equality)
    remarkM "Test 7: Hilbert term where body inside Exists is not an Equality"
    let nonEqBody = hX 1 ( eX 0 ( Neg ( Constant "A" :==: buildPair (X 1) (X 0) ) ) )
    nonEqBody_show <- showObjM nonEqBody
    remarkM "  Input:    hX 1 ( eX 0 ( Neg ( Constant \"A\" :==: Tupl [X 1, X 0] ) ) )"
    remarkM $ "  Actual:   " <> nonEqBody_show
    remarkM "  Expected: ε𝑥₁(∃𝑥₀(¬(A = (𝑥₁,𝑥₀)))) (Default Hilbert rendering, NOT π)"


    remarkM "--- Project Shorthand Parsing Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of Cartesian Product (A × B)
testCrossProductRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testCrossProductRendering = do
    remarkM "--- Testing Cross Product Shorthand Rendering (A × B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"
    let setC = Constant "C" -- For comparison

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- == Positive Case: Render term created by crossProd helper ==
    remarkM "Test 1: Rendering term generated by crossProd A B"
    let prodAB = crossProd setA setB -- Use the helper function
    actualOutput <- showObjM prodAB     -- Use showObjM to trigger rendering
    let expectedOutput = "A × B"      -- Define the expected string output

    remarkM "  Input Term: crossProd A B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show prodAB) -- Uncomment to see raw structure if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do 
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseCrossProduct logic within toSubexpParseTree to be correct)"
    else
        do 
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseCrossProduct logic within toSubexpParseTree and showSubexpParseTree formatting)"

    -- == Negative Case (Optional): Ensure unrelated terms don't render as cross product ==
    remarkM "Test 2: Rendering a simple Tuple (A, B)"
    let tupleTerm = buildPair setA setB
    tupleOutput <- showObjM tupleTerm
    let expectedTupleOutput = "(A,B)" -- Or similar based on your tuple rendering
    remarkM "  Input Term: Tupl [A, B]"
    remarkM $ "  Actual Rendered Output: " <> tupleOutput
    remarkM $ "  Expected Rendered Output (e.g.): " <> expectedTupleOutput
    if tupleOutput /= expectedOutput && tupleOutput == expectedTupleOutput then
         remarkM "  Check: Rendering is not 'A × B' and matches tuple format. PASSED."
    else
         remarkM "  Check: Rendering is incorrect. FAILED."


    remarkM "--- Cross Product Rendering Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of FUNCS(A,B)
testFuncsSetRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testFuncsSetRendering = do
    remarkM "--- Testing FUNCS(A,B) Shorthand Rendering ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by funcsSet helper ==
    remarkM "Test 1: Rendering term generated by funcsSet A B"
    let funcsAB = funcsSet setA setB -- Use the helper function

    actualOutput <- showObjM funcsAB     -- Use showObjM to trigger rendering
    -- Note: Expecting 𝗙𝗨𝗡𝗖𝗦(A,B) based on default FuncApp/Tuple rendering
    let expectedOutput = "𝗙𝗨𝗡𝗖𝗦(A,B)"

 

    remarkM "  Input Term: funcsSet A B"
    --remarkM $ "  Internal Structure (for info): " <> (pack $ show funcsAB) -- Uncomment if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    --remarkM exp3


    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
          remarkM "  Check: Rendering matches expected output. PASSED."
          remarkM "  (Requires parseFuncsSet logic within toSubexpParseTree to be correct)"
    else
        do
          remarkM "  Check: Rendering does NOT match expected output. FAILED."
          remarkM "  (Check parseFuncsSet logic and showSubexpParseTree formatting for FuncApp/Tuple)"

    remarkM "--- FUNCS(A,B) Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Binary Union (A ∪ B)
testBinaryUnionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testBinaryUnionRendering = do
    remarkM "--- Testing Binary Union Shorthand Rendering (A ∪ B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by binaryUnion helper ==
    remarkM "Test 1: Rendering term generated by binaryUnion A B"
    let unionAB = setA .\/. setB -- Use the new helper function
    actualOutput <- showObjM unionAB     -- Use showObjM to trigger rendering
    let expectedOutput = "A ∪ B"      -- Define the expected string output

    remarkM "  Input Term: A .\\/. B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show unionAB) -- Uncomment to see raw structure if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseBinaryUnion logic within toSubexpParseTree to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseBinaryUnion logic within toSubexpParseTree and showSubexpParseTree formatting)"

    remarkM "--- Binary Union Rendering Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of Binary Intersection (A ∩ B)
testIntersectionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testIntersectionRendering = do
    remarkM "--- Testing Binary Intersection Shorthand Rendering (A ∩ B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by (./\.) helper ==
    remarkM "Test 1: Rendering term generated by A ./\\. B"
    let intersectionAB = setA ./\. setB -- Use the new operator
    actualOutput <- showObjM intersectionAB   -- Use showObjM to trigger rendering
    let expectedOutput = "A ∩ B"         -- Define the expected string output

    remarkM "  Input Term: A ./\\. B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show intersectionAB) -- Uncomment if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseIntersectionOp logic within toSubexpParseTree to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseIntersectionOp logic within toSubexpParseTree and showSubexpParseTree formatting)"

    remarkM "--- Binary Intersection Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Big Union (∪S)
testBigUnionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testBigUnionRendering = do
    remarkM "--- Testing Big Union Shorthand Rendering (∪S) ---"
    let setS = Constant "S"
    fakeConstM "S" ()

    remarkM "Test 1: Rendering term generated by bigUnion S"
    let unionS = bigUnion setS -- Use the helper function
    actualOutput <- showObjM unionS     -- Use showObjM to trigger rendering
    let expectedOutput = "∪S"      -- Define the expected string output

    remarkM "  Input Term: bigUnion S"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    if actualOutput == expectedOutput then
        remarkM "  Check: Rendering matches expected output. PASSED."
    else
        remarkM "  Check: Rendering does NOT match expected output. FAILED."

    remarkM "--- Big Union Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Big Intersection (∩S)
testBigIntersectionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testBigIntersectionRendering = do
    remarkM "--- Testing Big Intersection Shorthand Rendering (∩S) ---"
    let setS = Constant "S"
    fakeConstM "S" () -- Assume S exists and is non-empty for the test definition

    remarkM "Test 1: Rendering term generated by bigIntersection S"
    let intersectionS = bigIntersection setS -- Use the helper function
    actualOutput <- showObjM intersectionS     -- Use showObjM to trigger rendering
    let expectedOutput = "∩S"         -- Define the expected string output

    remarkM "  Input Term: bigIntersection S"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    if actualOutput == expectedOutput then
        remarkM "  Check: Rendering matches expected output. PASSED."
    else
        remarkM "  Check: Rendering does NOT match expected output. FAILED."

    remarkM "--- Big Intersection Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Roster Notation {a, b, ...}
testRosterRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testRosterRendering = do
    remarkM "--- Testing Roster Notation Shorthand Rendering {..} ---"

    -- Setup Constants
    let elemA = Constant "A"
    let elemB = Constant "B"
    let elemC = Constant "C"
    let int1 = Integ 1

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- Test 1: Empty set
    --remarkM "Test 1: Rendering roster []"
    --let rosterEmpty = roster []
    --actualOutput1 <- showObjM rosterEmpty
    --let expectedOutput1 = "{}"
    --remarkM "  Input Term: roster []"
    --remarkM $ "  Actual Rendered Output:   " <> actualOutput1
    --remarkM $ "  Expected Rendered Output: " <> expectedOutput1
    --if actualOutput1 == expectedOutput1 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 2: Singleton set {A}
    remarkM "Test 2: Rendering roster [A]"
    let rosterA = roster [elemA]
    actualOutput2 <- showObjM rosterA
    let expectedOutput2 = "{A}"
    remarkM "  Input Term: roster [A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput2
    remarkM $ "  Expected Rendered Output: " <> expectedOutput2
    if actualOutput2 == expectedOutput2 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 3: Two element set {A, 1}
    remarkM "Test 3: Rendering roster [A, 1]"
    let rosterA1 = roster [elemA, int1]
    actualOutput3 <- showObjM rosterA1
    -- Note: Expected output depends on the derived Ord instance for ObjDeBr
    -- Integ constructor usually comes before Constant constructor
    let expectedOutput3 = "{1,A}"
    remarkM "  Input Term: roster [A, 1]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput3
    remarkM $ "  Expected Rendered Output: " <> expectedOutput3
    if actualOutput3 == expectedOutput3 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 4: Three element set {C, B, A} - testing sorting
    remarkM "Test 4: Rendering roster [C, B, A] (tests sorting)"
    let rosterCBA = roster [elemC, elemB, elemA]
    actualOutput4 <- showObjM rosterCBA
    let expectedOutput4 = "{A,B,C}" -- Assumes alphabetical sort for Constants
    remarkM "  Input Term: roster [C, B, A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput4
    remarkM $ "  Expected Rendered Output: " <> expectedOutput4
    if actualOutput4 == expectedOutput4 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 5: Set with duplicates {B, A, A} - testing deduplication
    remarkM "Test 5: Rendering roster [B, A, A] (tests deduplication)"
    let rosterBAA = roster [elemB, elemA, elemA]
    actualOutput5 <- showObjM rosterBAA
    let expectedOutput5 = "{A,B}" -- Sorted and deduplicated
    remarkM "  Input Term: roster [B, A, A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput5
    remarkM $ "  Expected Rendered Output: " <> expectedOutput5
    if actualOutput5 == expectedOutput5 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."


    remarkM "--- Roster Notation Rendering Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of Set Difference (A \\ B)
testSetDifferenceRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testSetDifferenceRendering = do
    remarkM "--- Testing Set Difference Shorthand Rendering (A \\\\ B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by (.\.) helper ==
    remarkM "Test 1: Rendering term generated by A .\\. B"
    let differenceAB = setA .\. setB -- Use the new operator
    actualOutput <- showObjM differenceAB   -- Use showObjM to trigger rendering
    let expectedOutput = "A ∖ B"         -- Define the expected string output (double backslash for Haskell String)

    remarkM "  Input Term: A .\\. B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show differenceAB) -- Uncomment if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseSetDifference logic and rendering logic in Rendering.hs to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseSetDifference, Rendering.hs formatting, and binaryOpInData)"

    remarkM "--- Set Difference Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Power Set P(A)
testPowerSetRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testPowerSetRendering = do
    remarkM "--- Testing Power Set Shorthand Rendering (P(A)) ---"

    -- Setup Constant for set
    let setA = Constant "A"
    fakeConstM "A" ()

    -- == Positive Case: Render term created by buildPowerSet helper ==
    remarkM "Test 1: Rendering term generated by buildPowerSet A"
    let pSetA = buildPowerSet setA -- Use the helper function
    actualOutput <- showObjM pSetA     -- Use showObjM to trigger rendering
    -- User specified Unicode Script P (U+1D4AB)
    let expectedOutput = "𝒫(A)"
    remarkM "  Input Term: buildPowerSet A"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parsePowerSet logic and rendering logic in Rendering.hs to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parsePowerSet, Rendering.hs formatting and ParseTreeConst)"

    remarkM "--- Power Set Rendering Tests Complete ---"
    return ()


testPairAndTupleRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testPairAndTupleRendering = do
    remarkM "--- Testing Pair and Tuple Rendering (Kuratowski) ---"

    -- Setup Constants for elements
    let constA = Constant "A"
    let constB = Constant "B"
    let constC = Constant "C"
    let constD = Constant "D"
    let int1 = Integ 1
    let int2 = Integ 2

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()
    fakeConstM "D" ()

    -- Test 1: Simple Pair (A, B)
    remarkM "Test 1: Rendering buildPair A B"
    let pairAB = buildPair constA constB
    actualOutput1 <- showObjM pairAB
    let expectedOutput1 = "(A,B)"
    remarkM "  Input Term: buildPair A B"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput1
    remarkM $ "  Expected Rendered Output: " <> expectedOutput1
    if actualOutput1 == expectedOutput1 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (Verify parsePair and Tuple rendering in Rendering.hs)"

    -- Test 2: Pair with an integer (1, C)
    remarkM "Test 2: Rendering buildPair (Integ 1) C"
    let pair1C = buildPair int1 constC
    actualOutput2 <- showObjM pair1C
    let expectedOutput2 = "(1,C)"
    remarkM "  Input Term: buildPair (Integ 1) C"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput2
    remarkM $ "  Expected Rendered Output: " <> expectedOutput2
    if actualOutput2 == expectedOutput2 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 3: Simple Tuple (A, B, C) - built as Pair A (Pair B C)
    remarkM "Test 3: Rendering buildTuple [A, B, C]"
    let tupleABC = buildTuple [constA, constB, constC]
    actualOutput3 <- showObjM tupleABC
    let expectedOutput3 = "(A,B,C)"
    remarkM "  Input Term: buildTuple [A, B, C]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput3
    remarkM $ "  Expected Rendered Output: " <> expectedOutput3
    if actualOutput3 == expectedOutput3 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (Verify parseTupleMax/parseTupleFixed and Tuple rendering)"

    -- Test 4: Tuple with mixed types (A, 1, B, 2)
    remarkM "Test 4: Rendering buildTuple [A, (Integ 1), B, (Integ 2)]"
    let tupleA1B2 = buildTuple [constA, int1, constB, int2]
    actualOutput4 <- showObjM tupleA1B2
    let expectedOutput4 = "(A,1,B,2)"
    remarkM "  Input Term: buildTuple [A, (Integ 1), B, (Integ 2)]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput4
    remarkM $ "  Expected Rendered Output: " <> expectedOutput4
    if actualOutput4 == expectedOutput4 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 5: Single element tuple (A) - buildTuple [A] should just be A
    remarkM "Test 5: Rendering buildTuple [A]"
    let tupleA_single = buildTuple [constA]
    actualOutput5 <- showObjM tupleA_single
    let expectedOutput5 = "A" -- As per buildTuple [x] -> x
    remarkM "  Input Term: buildTuple [A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput5
    remarkM $ "  Expected Rendered Output: " <> expectedOutput5
    if actualOutput5 == expectedOutput5 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 6: Empty tuple - buildTuple [] should be EmptySet, rendered as ∅
    remarkM "Test 6: Rendering buildTuple []"
    let tupleEmpty = buildTuple []
    actualOutput6 <- showObjM tupleEmpty
    let expectedOutput6 = "∅" -- Assuming EmptySet renders as ∅
    remarkM "  Input Term: buildTuple [] (which is EmptySet)"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput6
    remarkM $ "  Expected Rendered Output: " <> expectedOutput6
    if actualOutput6 == expectedOutput6 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (Verify EmptySet rendering or buildTuple [] behavior)"

    -- Test 7: Nested Pairs/Tuples - Pair (Pair A B) C -> ((A,B),C)
    remarkM "Test 7: Rendering buildPair (buildPair A B) C"
    let nestedPair = buildPair (buildPair constA constB) constC
    actualOutput7 <- showObjM nestedPair
    let expectedOutput7 = "((A,B),C)"
    remarkM "  Input Term: buildPair (buildPair A B) C"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput7
    remarkM $ "  Expected Rendered Output: " <> expectedOutput7
    if actualOutput7 == expectedOutput7 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 8: A Kuratowski pair that is NOT created by buildPair, but by roster directly
    -- This tests if parsePair can still recognize it for tuple rendering.
    remarkM "Test 8: Rendering a direct Kuratowski pair roster [roster[A], roster[A,B]]"
    let directKuratowski = roster [roster[constA], roster[constA, constB]]
    actualOutput8 <- showObjM directKuratowski
    let expectedOutput8 = "(A,B)" -- Expecting it to be parsed as a pair
    remarkM "  Input Term: roster [roster[A], roster[A,B]]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput8
    remarkM $ "  Expected Rendered Output: " <> expectedOutput8
    if actualOutput8 == expectedOutput8 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (parsePair might not be robust enough, or roster rendering interferes)"

    remarkM "--- Pair and Tuple Rendering Tests Complete ---"
    return ()


testAxiomOfChoice :: ProofGenTStd () [ZFCRuleDeBr] PropDeBr Text IO ()
testAxiomOfChoice = do
    -- Test for Axiom of Choice
    (acAx, acAxIdx) <- axiomOfChoiceM

    showAcAx <- showPropM acAx
    remarkM $ "Axiom of Choice: " <> showAcAx <> " at index " <> pack (show acAxIdx)
    -- Due to its complexity, you might want to add a remark with its raw structure too for debugging:
    -- remarkM $ "Raw AC: " <> pack (show acAx)
    return ()






main :: IO ()
main = do



    let y0 = (Integ 0 :==: Integ 0) :->: (Integ 99 :==: Integ 99)
    let y1 = Integ 0 :==: Integ 0
    let y2 = (Integ 99 :==: Integ 99) :->: (Integ 1001 :==: Integ 1001)
    let x0 = eX 0 (aX 0 ((Integ 0 :==: V 102) :&&: (X 0 `In` X 1)) :&&: (X 1 `In` X 1))
    let x1 = aX 3 (aX 2 (aX 1 ((X 3 :==: X 2) :&&: aX 0 (X 0 :==: X 1))))
    --(print . show) (checkSanity [] [(),()] mempty x0)
    print "X1" 

    (putStrLn . show) x1
    let xv = aX 10 (aX 21 (aX 1 (X 10 :==: X 21 :&&: aX 0 (X 0 :==: X 1))))
    -- ∀𝑥₃(∀𝑥₂(∀𝑥₁(𝑥₃ = 𝑥₂ ∨ ∀𝑥₀(𝑥₀ = 𝑥₁))))
    let cxv = xv
    (putStrLn . show) cxv
    let f = parseForall x1
    case f of
        Just (f,()) -> do
            let term1 = hX 0 (Integ 0 `In` Integ 0)
            let fNew = f term1
            (print.show) fNew
        Nothing -> print "parse failed!"
       --let z = applyUG xn () 102
--    -- (print . show) z
    let proof = (   fakeProp [] y0
                <> fakeProp [] y1 
                <> fakeProp [] y2
                <> mp y0
                <> mp y2
                <> proofByAsm y1 (Integ 99 :==: Integ 99) (mp $ y1 .->. (Integ 99 :==: Integ 99))
                )
                  ::[PropRuleDeBr]
    let zb = runProof proof

    -- either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb
    print "OI leave me alone"
    let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :<=: Integ 0))
    let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ 0))
    let generalized = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :==: Integ 0))
    let asm = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
    let mid = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 0)

    let proof2 =    fakeConst "N" ()
                 <> fakeProp [] z1
                 <> fakeProp [] z2
                 <> proofByUG generalized
                                        (
                                            proofByAsm asm z1 (
                                                    ui (V 0) z1
                                                <> mp ( asm .->. (V 0 :<=: Integ 0))
                                                <> simpL ((V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10))
                                                <> adj (V 0 `In` Constant "N") (V 0 :<=: Integ 0)
                                                <> ui (V 0) z2
                                                <> mp ( mid .->. (V 0 :==: Integ 0)  )
                                            )  
                                        )
                                    ::[PredRuleDeBr]

    let proof3 = proofByUG generalized
                                     (
                                        proofByAsm asm z1 (
                                                ui (V 0) z1
                                             <> mp ( asm .->. (V 0 :<=: Integ 0))
                                      
                                            )
                                     )
                                  ::[PredRuleDeBr]
                 
    let zb2 = runProof proof2 

    let zb3 = runProof ((fakeConst "N" () <> fakeProp [] z1 <> fakeProp [] z2 <> ui (V 0) z1)::[PredRuleDeBr])
    --either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd)  zb2
    --either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb3
    (a,b,c,d) <- runProofGeneratorT testprog
    print "hi wattup 2"
    let stepTxt= showPropDeBrStepsBase c
    (putStrLn . unpack) stepTxt
    print "YOYOYOYOYOYOYOYOYOYO CHECK THEOREM"
    print "YOYOYOYOYOYOYOYOYOYO CHECK THEOREM"
    print "YOYOYOYOYOYOYOYOYOYO CHECK THEOREM3"
    (a,b,c,d) <- checkTheoremM testTheoremMSchema
--   print "yo"
    let stepTxt= showPropDeBrStepsBase d
    (putStrLn . unpack) stepTxt

    print "TEST ROSTER RENDERING BEGIN-------------------------------------"
    (aRos, bRos, cRos, dRos) <- runProofGeneratorT testRosterRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cRos -- Print results


    print "TEST PROG 2 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog2
    (putStrLn . unpack . showPropDeBrStepsBase) c

    return ()

    print "TEST PROG 3 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog3
    (putStrLn . unpack . showPropDeBrStepsBase) c

    print "TEST PROG 4 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog4
    (putStrLn . unpack . showPropDeBrStepsBase) c
    (putStrLn . show) b

    (putStrLn . show) c


    print "TEST PROG 5 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog5
    (putStrLn . unpack . showPropDeBrStepsBase) c
    (putStrLn . show) b

    print "TEST EQUALITY RULES BEGIN-------------------------------------"
    (aEq, bEq, cEq, dEq) <- runProofGeneratorT testEqualityRules
    (putStrLn . unpack . showPropDeBrStepsBase) cEq
    return ()

    print "TEST NORMALIZATION-------------------------------------"
    (aEq, bEq, cEq, dEq) <- runProofGeneratorT testNormalization
    (putStrLn . unpack . showPropDeBrStepsBase) cEq
    return ()

    print "TEST MORE COMPLEX NESTING BEGIN-------------------------------------"
    (aMC, bMC, cMC, dMC) <- runProofGeneratorT testMoreComplexNesting
    (putStrLn . unpack . showPropDeBrStepsBase) cMC

    print "TEST NON-SEQUENTIAL INDICES BEGIN-------------------------------------"
    (aNS, bNS, cNS, dNS) <- runProofGeneratorT testNonSequentialIndices
    (putStrLn . unpack . showPropDeBrStepsBase) cNS


    print "TEST COMPLEX SUBSET NOTATION BEGIN-------------------------------------"
    (aCSub, bCSub, cCSub, dCSub) <- runProofGeneratorT testComplexSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cCSub -- Print results

    print "TEST STRICT SUBSET NOTATION BEGIN-------------------------------------"
    (aStrict, bStrict, cStrict, dStrict) <- runProofGeneratorT testStrictSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cStrict -- Print results


    print "TEST NOT SUBSET NOTATION BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testNotSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results

    print "TEST builderX BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testBuilderXSuite
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results


    print "TEST AICLAIMX BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testCompositionImplementation
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results

    print "TEST SH BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testShorthandRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results

    print "TEST PROJECT SHORTHAND PARSING BEGIN-------------------------------------"
    (aPrj, bPrj, cPrj, dPrj) <- runProofGeneratorT testProjectShorthandParsing
    (putStrLn . unpack . showPropDeBrStepsBase) cPrj -- Print results


    print "TEST CROSS PRODUCT PARSING BEGIN-------------------------------------"
    (aXP, bXP, cXP, dXP) <- runProofGeneratorT testCrossProductRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cXP -- Print results


    print "TEST BINARY UNION RENDERING BEGIN-------------------------------------"
    (aBU, bBU, cBU, dBU) <- runProofGeneratorT testBinaryUnionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBU -- Print results



    print "TEST BINARY INTERSECTION RENDERING BEGIN-------------------------------------"
    (aBI, bBI, cBI, dBI) <- runProofGeneratorT testIntersectionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBI -- Print results

    print "TEST BIG UNION RENDERING BEGIN-------------------------------------"
    (aBU, bBU, cBU, dBU) <- runProofGeneratorT testBigUnionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBU -- Print results

    print "TEST BIG INTERSECTION RENDERING BEGIN-------------------------------------"
    (aBI, bBI, cBI, dBI) <- runProofGeneratorT testBigIntersectionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBI -- Print results

   

    print "TEST SET DIFFERENCE RENDERING BEGIN-------------------------------------"
    (aDiff, bDiff, cDiff, dDiff) <- runProofGeneratorT testSetDifferenceRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cDiff -- Print results

    print "TEST POWER SET RENDERING BEGIN-------------------------------------"
    (aPow, bPow, cPow, dPow) <- runProofGeneratorT testPowerSetRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cPow -- Print results

    -- print "TEST EMPTY SET RENDERING BEGIN-------------------------------------"
    -- (aEmp, bEmp, cEmp, dEmp) <- runProofGeneratorT testEmptySetRendering
    -- (putStrLn . unpack . showPropDeBrStepsBase) cEmp -- Print results
    print "TEST PAIR AND TUPLE RENDERING (KURATOWSKI) BEGIN-------------------------------------"
    (aPT, bPT, cPT, dPT) <- runProofGeneratorT testPairAndTupleRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cPT -- Print results

    print "TEST AXIOM OF CHOICE BEGIN-------------------------------------"
    (aAC, bAC, cAC, dAC) <- runProofGeneratorT testAxiomOfChoice
    (putStrLn . unpack . showPropDeBrStepsBase) cAC -- Print results

    print "TEST FUNCS(A,B) RENDERING BEGIN-------------------------------------"
    (aFSR, bFSR, cFSR, dFSR) <- runProofGeneratorT testFuncsSetRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cFSR -- Print results

    -- print "TEST BINARY UNION EXISTS SCHEMA-------------------------------------"
    -- (a,b,c,d) <- checkTheoremM $ binaryUnionExistsSchema
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    -- print "TEST BINARY CROSSPRODDEFEQUIV SCHEMA-------------------------------------"
    -- (a,b,c,d) <- checkTheoremM $ crossProductDefEquivSchema
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    -- print "TEST CROSSPROD EXISTS SCHEMA ---------------------------"
    -- (a,b,c,d) <- checkTheoremM $ crossProductExistsSchema
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    -- print "TEST BUILDER SUBSET THEOREM-------------------------------------"
    -- let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
    -- let source_set_template = X 1 .\/. X 2
    -- (a,b,c,d) <- checkTheoremM $ builderSubsetTheoremSchema [1,2] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    -- print "TEST BUILDER SOURCE PARTITION THEOREM--------------------"
    -- let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
    -- let source_set_template = X 1 .\/. X 2
    -- (a,b,c,d) <- checkTheoremM $ builderSrcPartitionSchema [1,2] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results




    -- print "TEST STRONG INDUCTION THEOREM-------------------------------------"
    -- let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
    -- let source_set_template = X 1 .\/. X 2
    -- (a,b,c,d) <- checkTheoremM $ strongInductionTheoremMSchema [1,2] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    print "TEST STRONG INDUCTION THEOREM 2-------------------------------------"
    let p_template = Constant "C" :==: X 0
    let source_set_template = Constant "S"
    (a,b,c,d) <- checkTheoremM $ strongInductionTheoremMSchema [] 0 source_set_template p_template
    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    -- print "TEST UNION WITH EMPTY SET THEOREM-------------------------------------"
    -- (a,b,c,d) <- checkTheoremM unionWithEmptySetSchema
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

    -- print "DISJOINT SUBSET IS EMPTY THEOREM-------------------------------------"
    -- (a,b,c,d) <- checkTheoremM disjointSubsetIsEmptySchema
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


    -- print "SPEC REDUNDANCY THEOREM-------------------------------------"
    -- let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
    -- let source_set_template = X 1 .\/. X 2
    -- (a,b,c,d) <- checkTheoremM $ specRedundancySchema [1,2] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


    -- print "SPEC REDUNDANCY THEOREM TEST 2-------------------------------------"
    -- let p_template = X 0 .==. X 0
    -- let source_set_template = Constant "SourceSet"
    -- (a,b,c,d) <- checkTheoremM $ specRedundancySchema [] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results



    -- print "SPEC ANTI-REDUNDANCY THEOREM-------------------------------------"
    -- let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
    -- let source_set_template = X 1 .\/. X 2
    -- (a,b,c,d) <- checkTheoremM $ specRedundancySchema [1,2] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results



    -- print "SPEC ANTI-REDUNDANCY THEOREM TEST 2-------------------------------------"
    -- let p_template = X 0 .==. X 0
    -- let source_set_template = Constant "SourceSet"
    -- (a,b,c,d) <- checkTheoremM $ specAntiRedundancySchema [] 0 source_set_template p_template
    -- (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


    return ()



testprog::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog = do
      let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :<=: Integ 0))
      showZ1 <- showPropM z1
      remarkM $ showZ1 <> " Z1Z1Z1Z1" 
      let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ 0))
      let asm = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
      let asm2 = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
      fakeConstM "N" ()
      fakePropM [] z1
      fakePropM [] z2
      
      fux<- runProofByUGM () do
          runProofByAsmM  asm2 do
              (s5,_,_)<- runProofBySubArgM  do
                 newFreeVar <- getTopFreeVar
                 (s1,_) <- uiM newFreeVar z1
                 (s2,idx) <- mpM s1
                 (natAsm,_) <- simpLM asm
                 (s3,_) <- adjM natAsm s2
                 (s4,_) <- uiM newFreeVar z2
                 mpM s4
              return ()
          return ()
      runTheoremM  testTheoremMSchema
      runTmSilentM  testTheoremMSchema
      (absurdImp,_) <- runProofByAsmM z2 do
        (notZ1,_) <- fakePropM [](Neg z1)
        (falseness,_) <- contraFM z1
        showF <- showPropM falseness
        remarkM $ showF <> " is the falseness"
      showAbsurdImp <- showPropM absurdImp
      remarkM $ showAbsurdImp <> " is the absurdity"
      absurdM absurdImp
      return ()

testprog2::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog2 = do
    let p = eX 0 (X 0 `In` Constant "N")
    let q = eX 0 (X 0 :<=: Integ 10)
    let pImpQ = p :->: q
    fakeConstM "N" ()
    fakePropM [] pImpQ
    fakePropM [] (neg q)
    (s,idx) <- modusTollensM pImpQ
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


testprog3::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog3 = do
    let a = eX 0 (X 0 `nIn` Constant "N")
    fakeConstM "N" ()
    fakePropM [] a
    (s,idx) <- reverseANegIntroM a
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()

testprog4::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog4 = do
    let a = aX 0 (X 0 `nIn` Constant "N")
    fakeConstM "N" ()
    fakePropM [] a
    (s,idx) <- reverseENegIntroM a
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


testprog5::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog5 = do
    let a = eXBang 99 (Neg (X 99 `In` Constant "N"))
    fakeConstM "N" ()
    (s,idx) <- fakePropM [] a


    showS <- showPropM a
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


theoremProg::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => ProofGenTStd () [PredRuleDeBr] PropDeBr Text m ()
theoremProg = do
    let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :<=: Integ 0))
    let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ  0))
    let asm = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
    let asm2 = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
    (generalized, _) <- runProofByUGM () do
          runProofByAsmM asm2 do
              newFreeVar <- getTopFreeVar
              (s1,_) <- uiM newFreeVar z1
              (s2,_) <- mpM s1
              remarkIdx <- remarkM "Yeah baby"
              remarkIdx2<-remarkM "" --empty remark
              --(lift . print) "Coment1"
              --(lift . print . show) s1
              remarkM $ (pack . show) remarkIdx2 <> " was the index of the remark above/"
              (natAsm,_) <- simpLM asm
              --(lift . print) "COmment 2"
              (s3,_) <- adjM natAsm s2
              (s4,line_idx) <- uiM newFreeVar z2
              showS4 <- showPropM s4
              remarkM $ showS4 <> " is the sentence. It was proven in line " <> (pack . show) line_idx
                       <> "\nThis is the next line of this remark."
              -- (lift . print . show) line_idx
              (s5,_) <- mpM s4
              simpLM asm
    return ()
--              return (s5,())

