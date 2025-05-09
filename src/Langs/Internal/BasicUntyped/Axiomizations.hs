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
            internalTIdx = 1
            internalBIdx = 2

            core_prop_template :: PropDeBr
            core_prop_template = (X idx `In` XInternal internalBIdx)
                             :<->:
                             (p_template :&&: (X idx `In` XInternal internalTIdx))

            quantified_over_x :: PropDeBr
            quantified_over_x = aX idx core_prop_template

            quantified_over_B :: PropDeBr
            quantified_over_B = eXInt internalBIdx quantified_over_x

            axiom_body_with_t :: PropDeBr
            axiom_body_with_t = propDeBrSubXInt internalTIdx t quantified_over_B

            closed_axiom :: PropDeBr
            closed_axiom = multiAx outerIdxs axiom_body_with_t

        in
            closed_axiom

    replaceAxiom :: [Int] -> Int -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
    replaceAxiom outerIdxs idx1 idx2 t p_template =

        let
            internalTIdx = 1
            internalBIdx = 2

            exists_unique_b = eXBang idx2 p_template

            implication_in_premise = (X idx1 `In` XInternal internalTIdx) :->: exists_unique_b

            premise_template :: PropDeBr
            premise_template = aX idx1 implication_in_premise

            conjunction_in_conclusion = (X idx2 `In` XInternal internalTIdx) :&&: p_template -- Changed from t to XInternal internalTIdx

            exists_b_in_conclusion = eX idx2 conjunction_in_conclusion

            bicond_in_conclusion = (X idx1 `In` XInternal internalBIdx) :<->: exists_b_in_conclusion

            forall_a_in_conclusion = aX idx1 bicond_in_conclusion

            conclusion_template :: PropDeBr
            conclusion_template = eXInt internalBIdx forall_a_in_conclusion

            axiom_template_pre_subst :: PropDeBr
            axiom_template_pre_subst = premise_template :->: conclusion_template

            axiom_body_with_t :: PropDeBr
            axiom_body_with_t = propDeBrSubXInt internalTIdx t axiom_template_pre_subst

            closed_axiom :: PropDeBr
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