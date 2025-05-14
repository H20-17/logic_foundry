module Langs.Internal.BasicUntyped.Axiomizations 
()
where

import Langs.Internal.BasicUntyped.Core
import Langs.Internal.BasicUntyped.Shorthands

import Control.Monad ( unless, guard,msum )
import Data.List (intersperse,findIndex, partition,sort,find)
import Data.Text (Text, pack, unpack,concat, lines,intercalate)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
import Data.Set(Set, notMember)
import qualified Data.Set as Set (fromList,insert,member)
import Control.Applicative ( Alternative((<|>)) )

import Control.Monad.Except ( MonadError(throwError) )
import Kernel

import Internal.StdPattern

import Control.Exception (SomeException)
import qualified RuleSets.PropLogic as PL
import qualified RuleSets.PredLogic as PREDL
import qualified RuleSets.ZFC as ZFC
import RuleSets.PropLogic (LogicSent(parseIff))
import RuleSets.ZFC (specification,parseMemberOf,memberOf)





instance PL.LogicSent PropDeBr () where

  (.&&.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.&&.) = (:&&:)

  parseAdj :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseAdj = parseConjunction

  (.->.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.->.) = (:->:)

  parse_implication :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parse_implication = parseImplication


  neg :: PropDeBr -> PropDeBr
  neg = Neg

  parseNeg :: PropDeBr -> Maybe PropDeBr
  parseNeg = parseNegation

  (.||.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.||.) = (:||:)
  parseDisj :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseDisj = parseDisjunction


  false :: PropDeBr
  false = F

  (.<->.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.<->.) = (:<->:)


  parseIff  :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseIff = parseBiconditional


objDeBrSubBoundVarToX0 :: Int -> ObjDeBr -> ObjDeBr
objDeBrSubBoundVarToX0 boundVarIdx obj = case obj of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert (propDeBrSubBoundVarToX0 boundVarIdx p)
    Bound idx -> if idx == boundVarIdx then X 0 else Bound idx
    V idx -> V idx
    (o1 :+: o2) -> objDeBrSubBoundVarToX0 boundVarIdx o1 :+: objDeBrSubBoundVarToX0 boundVarIdx o2
    Intneg o1     -> Intneg (objDeBrSubBoundVarToX0 boundVarIdx o1)
    (o1 :*: o2) -> objDeBrSubBoundVarToX0 boundVarIdx o1 :*: objDeBrSubBoundVarToX0 boundVarIdx o2
    IntSet -> IntSet
    EmptySet -> EmptySet


propDeBrSubBoundVarToX0 :: Int -> PropDeBr -> PropDeBr
propDeBrSubBoundVarToX0 boundVarIdx prop = case prop of
    Neg p -> Neg $ propDeBrSubBoundVarToX0 boundVarIdx p
    (p :&&: q) -> propDeBrSubBoundVarToX0 boundVarIdx p :&&: propDeBrSubBoundVarToX0 boundVarIdx q
    (p :||: q) -> propDeBrSubBoundVarToX0 boundVarIdx p :||: propDeBrSubBoundVarToX0 boundVarIdx q
    (p :->: q) -> propDeBrSubBoundVarToX0 boundVarIdx p :->: propDeBrSubBoundVarToX0 boundVarIdx q
    (p :<->: q) -> propDeBrSubBoundVarToX0 boundVarIdx p :<->: propDeBrSubBoundVarToX0 boundVarIdx q
    (a :==: b) -> objDeBrSubBoundVarToX0 boundVarIdx a :==: objDeBrSubBoundVarToX0 boundVarIdx b
    In a b -> In (objDeBrSubBoundVarToX0 boundVarIdx a) (objDeBrSubBoundVarToX0 boundVarIdx b)
    Forall p -> Forall (propDeBrSubBoundVarToX0 boundVarIdx p)
    Exists p -> Exists (propDeBrSubBoundVarToX0 boundVarIdx p)
    (a :<=: b) -> objDeBrSubBoundVarToX0 boundVarIdx a :<=: objDeBrSubBoundVarToX0 boundVarIdx b
    F -> F



boundExpToFunc :: PropDeBr -> ObjDeBr -> PropDeBr
boundExpToFunc p obj = propDeBrSubX 0 obj template
           where
                 boundDepth = boundDepthPropDeBr p
                 template = propDeBrSubBoundVarToX0 boundDepth p

instance PREDL.LogicSent PropDeBr ObjDeBr ()  where
    parseExists :: PropDeBr -> Maybe (ObjDeBr -> PropDeBr, ())
    parseExists prop =
      case prop of
          Exists p -> Just (boundExpToFunc p,())
          _ -> Nothing


    parseForall :: PropDeBr -> Maybe (ObjDeBr -> PropDeBr, ())
    parseForall prop =
        case prop of
           Forall p -> Just (boundExpToFunc p,())
           _ -> Nothing
    createForall :: PropDeBr -> () -> Int -> PropDeBr
    createForall prop () idx = Forall (propDeBrApplyUG prop idx (boundDepthPropDeBr prop))

    reverseParseQuantToExistsNot :: (ObjDeBr -> PropDeBr) -> () -> PropDeBr
    reverseParseQuantToExistsNot f () = eX 0 (Neg (f (X 0)))

    reverseParseQuantToForallNot :: (ObjDeBr -> PropDeBr) -> () -> PropDeBr
    reverseParseQuantToForallNot f () = aX 0 (Neg (f (X 0)))

    parseExistsNot :: PropDeBr -> Maybe (ObjDeBr -> PropDeBr, ())
    parseExistsNot prop =
        case prop of
            Exists (Neg p) -> Just (boundExpToFunc p,())
            _ -> Nothing
    parseForallNot :: PropDeBr -> Maybe (ObjDeBr -> PropDeBr, ())
    parseForallNot prop =
        case prop of
            Forall (Neg p) -> Just (boundExpToFunc p,())
            _ -> Nothing
    reverseParseQuantToForall :: (ObjDeBr -> PropDeBr) -> () -> PropDeBr
    reverseParseQuantToForall f () = aX 0 (f (X 0))
    reverseParseQuantToExists :: (ObjDeBr -> PropDeBr) -> () -> PropDeBr
    reverseParseQuantToExists f () = eX 0 (f (X 0))
    reverseParseQuantToHilbert :: (ObjDeBr -> PropDeBr) -> () -> ObjDeBr
    reverseParseQuantToHilbert f () = hX 0 (f (X 0))
    parseEq :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
    parseEq  = parseEqual
    (.==.) :: ObjDeBr -> ObjDeBr -> PropDeBr
    (.==.) = (:==:)
    substX :: Int -> PropDeBr -> ObjDeBr -> PropDeBr
    substX idx template obj = propDeBrSubX idx obj template



objDeBrApplyUG :: ObjDeBr -> Int -> Int -> ObjDeBr
objDeBrApplyUG obj freevarIdx boundvarIdx =
    case obj of
        Integ num -> Integ num
        Constant name -> Constant name
        Hilbert p1 -> Hilbert (propDeBrApplyUG p1 freevarIdx boundvarIdx)
        Bound idx -> Bound idx
        V idx -> if idx == freevarIdx then Bound boundvarIdx else V idx
        (o1 :+: o2) -> objDeBrApplyUG o1 freevarIdx boundvarIdx :+: objDeBrApplyUG o2 freevarIdx boundvarIdx
        Intneg o1     -> Intneg (objDeBrApplyUG o1 freevarIdx boundvarIdx)
        (o1 :*: o2) -> objDeBrApplyUG o1 freevarIdx boundvarIdx :*: objDeBrApplyUG o2 freevarIdx boundvarIdx
        IntSet -> IntSet
        EmptySet -> EmptySet



propDeBrApplyUG :: PropDeBr -> Int -> Int -> PropDeBr
propDeBrApplyUG prop freevarIdx boundvarIdx =
    case prop of
        Neg p -> Neg (propDeBrApplyUG p freevarIdx boundvarIdx)
        (p1 :&&: p2) -> propDeBrApplyUG p1 freevarIdx boundvarIdx :&&: propDeBrApplyUG p2 freevarIdx boundvarIdx
        (p1 :||: p2) -> propDeBrApplyUG p1 freevarIdx boundvarIdx :||: propDeBrApplyUG p2 freevarIdx boundvarIdx
        (p1 :->: p2) -> propDeBrApplyUG p1 freevarIdx boundvarIdx :->: propDeBrApplyUG p2 freevarIdx boundvarIdx
        (p1 :<->: p2) -> propDeBrApplyUG p1 freevarIdx boundvarIdx :<->: propDeBrApplyUG p2 freevarIdx boundvarIdx
        (o1 :==: o2) -> objDeBrApplyUG o1 freevarIdx boundvarIdx :==: objDeBrApplyUG o2 freevarIdx boundvarIdx
        In o1 o2 -> In (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        Forall p -> Forall (propDeBrApplyUG p freevarIdx boundvarIdx)
        Exists p -> Exists (propDeBrApplyUG p freevarIdx boundvarIdx)
        (o1 :<=: o2) -> objDeBrApplyUG o1 freevarIdx boundvarIdx :<=: objDeBrApplyUG o2 freevarIdx boundvarIdx
        F -> F



instance ZFC.LogicTerm ObjDeBr where
    --parseTuple :: ObjDeBr -> Maybe [ObjDeBr]
    --parseTuple = parseTupl
    --buildTuple :: [ObjDeBr] -> ObjDeBr
    --buildTuple = Tupl
    (.+.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
    (.+.) = (:+:)
    (.*.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
    (.*.) = (:*:)
    intNeg :: ObjDeBr -> ObjDeBr
    intNeg = Intneg
    intSet :: ObjDeBr
    intSet = IntSet


instance ZFC.LogicSent PropDeBr ObjDeBr where

    specAxiom :: [Int] -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
    specAxiom outerIdxs idx t p_template =
        let
            internalTIdx = 1 -- Placeholder index for the source set 't'
            internalBIdx = 2 -- Placeholder index for the specified set 'B' (which will be XInternal internalBIdx)

            -- The core relationship: x ∈ B ↔ (P(x) ∧ x ∈ t)
            -- X idx represents 'x' (the element variable)
            -- XInternal internalBIdx represents 'B' (the set being specified)
            -- XInternal internalTIdx represents 't' (the source set)
            -- p_template represents P(x)
            core_prop_template :: PropDeBr
            core_prop_template = (X idx `In` XInternal internalBIdx)
                             :<->:
                             (p_template :&&: (X idx `In` XInternal internalTIdx))

            -- Universally quantify over x: ∀x (x ∈ B ↔ (P(x) ∧ x ∈ t))
            quantified_over_x :: PropDeBr
            quantified_over_x = aX idx core_prop_template

            -- Condition that B must be a set: isSet(B)
            -- isSet is defined in Shorthands as Neg (B `In` IntSet)
            condition_B_isSet :: PropDeBr
            condition_B_isSet = isSet (XInternal internalBIdx) -- Using the isSet shorthand

            -- Combine the conditions for B: isSet(B) ∧ ∀x(...)
            full_condition_for_B :: PropDeBr
            full_condition_for_B = condition_B_isSet :&&: quantified_over_x

            -- Existentially quantify over B: ∃B (isSet(B) ∧ ∀x(...))
            -- eXInt binds XInternal internalBIdx
            quantified_over_B :: PropDeBr
            quantified_over_B = eXInt internalBIdx full_condition_for_B

            -- Substitute the actual source set 't' (for XInternal internalTIdx)
            -- This results in: ∃B (isSet(B) ∧ ∀x (x ∈ B ↔ (P(x) ∧ x ∈ t_actual)))
            axiom_body_with_t :: PropDeBr
            axiom_body_with_t = propDeBrSubXInt internalTIdx t quantified_over_B

            -- Close over any outer template variables (parameters in P(x) or t)
            closed_axiom :: PropDeBr
            closed_axiom = multiAx outerIdxs axiom_body_with_t
        in
            closed_axiom

    replaceAxiom :: [Int] -> Int -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
    replaceAxiom outerIdxs x_from_T_idx y_image_idx t p_xy_template =
        -- p_xy_template is the user's predicate P(X x_from_T_idx, X y_image_idx)
        -- t is the source set
        let
            -- Placeholders for substituting 't' (source set) and binding 'B' (replacement set)
            internalTIdx = 0 -- Placeholder for t
            internalBIdx = 1 -- Placeholder for B

            -- Premise: ∀x (x ∈ t → ∃!y P(x,y))
            -- Let x_outer_scope be X x_from_T_idx (this is what the outer aX will bind)
            -- Let y_to_bind be X y_image_idx (this is what eXBang will bind)

            -- To make eXBang safe, we create a template for its argument P(x,y).
            -- We use distinct placeholders for x and y within this template for eXBang.
            -- Let X 5 be the placeholder for x, and X y_image_idx be the placeholder for y.
            x_placeholder_for_P_arg = 5 -- Arbitrary index, distinct from y_image_idx

            -- Step 1: Create the argument for eXBang.
            -- This argument should be P(X x_placeholder_for_P_arg, X y_image_idx)
            -- We get this by taking p_xy_template (which is P(X x_from_T_idx, X y_image_idx))
            -- and substituting X x_from_T_idx with X x_placeholder_for_P_arg.
            -- The X y_image_idx in p_xy_template remains as X y_image_idx, ready for eXBang.
            p_template_for_exbang_input = propDeBrSubX x_from_T_idx (X x_placeholder_for_P_arg) p_xy_template
            
            -- Step 2: Apply eXBang to this template.
            -- eXBang y_image_idx will bind X y_image_idx in p_template_for_exbang_input.
            -- The result is conceptually: ∃!(X y_image_idx) P(X x_placeholder_for_P_arg, X y_image_idx)
            unique_existence_intermediate_template = eXBang y_image_idx p_template_for_exbang_input

            -- Step 3: Now, substitute the actual x (which is X x_from_T_idx, bound by the outer aX)
            -- for X x_placeholder_for_P_arg in the result of eXBang.
            unique_existence_for_specific_x = propDeBrSubX x_placeholder_for_P_arg (X x_from_T_idx) unique_existence_intermediate_template
            
            premise_implication = (X x_from_T_idx `In` XInternal internalTIdx) :->: unique_existence_for_specific_x
            premise = aX x_from_T_idx premise_implication

            -- Conclusion: ∃B (isSet(B) ∧ ∀y' (y' ∈ B ↔ ∃x' (x' ∈ t ∧ P(x',y'))))
            -- Using fresh template indices for y' and x' in the conclusion
            y_prime_idx_conc = 2 
            x_prime_idx_conc = 3

            -- Construct P(X x_prime_idx_conc, X y_prime_idx_conc) from the original p_xy_template
            p_x_prime_y_prime_conc = propDeBrSubXs [ (x_from_T_idx, X x_prime_idx_conc)
                                                   , (y_image_idx,  X y_prime_idx_conc) ]
                                                   p_xy_template

            exists_x_prime_part_conc = eX x_prime_idx_conc (
                                        (X x_prime_idx_conc `In` XInternal internalTIdx) -- x' ∈ t
                                        :&&: p_x_prime_y_prime_conc                     -- P(x',y')
                                      )

            conclusion_membership_equivalence = (X y_prime_idx_conc `In` XInternal internalBIdx) -- y' ∈ B
                                             :<->: exists_x_prime_part_conc

            forall_y_prime_conclusion_core = aX y_prime_idx_conc conclusion_membership_equivalence

            condition_B_isSet = isSet (XInternal internalBIdx)
            full_definition_of_B = condition_B_isSet :&&: forall_y_prime_conclusion_core
            conclusion = eXInt internalBIdx full_definition_of_B

            axiom_template_before_t_substitution = premise :->: conclusion
            axiom_body_with_t = propDeBrSubXInt internalTIdx t axiom_template_before_t_substitution
            closed_axiom = multiAx outerIdxs axiom_body_with_t
        in
            closed_axiom

    memberOf :: ObjDeBr -> ObjDeBr -> PropDeBr
    memberOf a b = a `In` b
    (.<=.) :: ObjDeBr -> ObjDeBr -> PropDeBr
    (.<=.) = (:<=:)


    intsAreUrelementsAxiom :: PropDeBr
    intsAreUrelementsAxiom =
              -- Construct the axiom: ∀i (i ∈ IntSet → (∀x (x ∉ i)))
              -- Using template variables: ∀X₀ (X₀ ∈ IntSet → (∀X₁ (¬(X₁ ∈ X₀))))
              -- Inner part: ∀X₁ (¬(X₁ ∈ X₀))
              -- Template for negation: Neg (X 1 `In` X 0)
              let inner_forall = aX 1 (Neg (X 1 `In` X 0))

              -- Outer part: X₀ ∈ IntSet → inner_forall
              -- Template for implication: (X 0 `In` IntSet) :->: inner_forall
                  implication = (X 0 `In` IntSet) :->: inner_forall

              -- Full axiom: ∀X₀ (implication)
              in aX 0 implication

    emptySetAxiom :: PropDeBr -- MODIFIED implementation
    emptySetAxiom = aX 0 (Neg (X 0 `In` EmptySet))
        -- This asserts ∀x (x ∉ EmptySet).
        -- X 0 is the universally quantified element x.
        -- EmptySet is your ObjDeBr constructor for the empty set.

    extensionalityAxiom :: PropDeBr -- MODIFIED implementation
    extensionalityAxiom =
        -- ∀A ∀B ( (isSet(A) ∧ isSet(B) ∧ (∀x (x ∈ A ↔ x ∈ B))) → A = B )
        -- where isSet(Y) is defined as ¬(Y ∈ IntSet) for this context.
        --
        -- Using template variables:
        -- X 0 for A (bound by the first aX)
        -- X 1 for B (bound by the second aX)
        -- X 2 for x (the element, bound by the third aX)
        let
            a_is_Not_IntUrelement = Neg (X 0 `In` IntSet)
            b_is_Not_IntUrelement = Neg (X 1 `In` IntSet)

            x_in_A = X 2 `In` X 0
            x_in_B = X 2 `In` X 1
            elements_are_equivalent = aX 2 (x_in_A :<->: x_in_B) -- ∀x (x ∈ A ↔ x ∈ B)

            -- The full antecedent of the main implication:
            -- (A is not an IntUrelement) ∧ (B is not an IntUrelement) ∧ (A and B have same elements)
            antecedent = a_is_Not_IntUrelement :&&: b_is_Not_IntUrelement :&&: elements_are_equivalent

            -- The consequent of the main implication:
            consequent = X 0 :==: X 1 -- A = B
        in
            -- ∀A ∀B (antecedent → consequent)
            aX 0 (aX 1 (antecedent :->: consequent))

    emptySetNotIntAxiom :: PropDeBr -- New implementation
    emptySetNotIntAxiom = Neg (EmptySet `In` IntSet)
        -- This asserts EmptySet ∉ IntSet.
        -- EmptySet is your ObjDeBr constructor for the empty set.
        -- IntSet is your ObjDeBr constructor for the set of integers.


-- Axiom of Regularity:
-- Forall A (A /= EmptySet -> Exists x (x In A /\ (x intersect A) == EmptySet))
regularityAxiom :: PropDeBr
regularityAxiom = aX 0 ( 
                         (isSet (X 0)) :&&: Neg (X 0 :==: EmptySet) :->: 
                                eX 1 ( 
                                       (X 1 `In` X 0) :&&: ((X 1 ./\. X 0) :==: EmptySet) 
                                     ) 
                       )
