{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DoAndIfThenElse #-}
module Langs.Internal.BasicUntyped.Shorthands (
    (./=.),
    builderX,
    nIn,
    subset,
    strictSubset,
    boundDepthObjDeBr,
    boundDepthPropDeBr,
    notSubset,
    (.@.),
    (.:.),
    project,
    objDeBrSubX,
    crossProd,
    funcsSet,
    parseFuncApplication,
    parseSetBuilder,
    parseHilbertShort,
    parseNotEqual,
    parseNotIn,
    parseNotSubset,
    parseStrictSubset,
    parseSubset,
    parseExistsUnique,
    parseComposition,
    parseProjectHilbert,
    parseCrossProduct,
    parseFuncsSet,
    (.\/.),
    parseBinaryUnion,
    (./\.),
    parseIntersectionOp,
    bigUnion,
    bigIntersection,
    parseBigUnion,
    parseBigIntersection,
    (.\.),
    parseSetDifference,
    powerSet,
    parsePowerSet,
    (.<.),
    parseLessThan,
    parseTupleFixed,
    parseTupleMax,
    pair,
    parsePair,
    tuple,
    parseIsFunc,
    isFunc,
    natSetObj,      -- Exporting the NatSet object
    parseNatSet,     -- Exporting the NatSet parser
    parseForallChain,
    parseImplication,
    isRelationOn


) where
import Langs.Internal.BasicUntyped.Core
import Control.Monad ( unless, guard,msum, zipWithM )
import Data.List (intersperse,findIndex, partition,sort,find)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Data.Set(Set, notMember)
import qualified Data.Set as Set (fromList,insert,member)
import Control.Applicative ( Alternative((<|>)) )

import Control.Monad.Except ( MonadError(throwError) )
import Kernel

import Internal.StdPattern

import Control.Exception (SomeException)
import qualified RuleSets.PropLogic.Core as PL
import qualified RuleSets.PredLogic.Core as PREDL
import qualified RuleSets.ZFC.Core as ZFC
import RuleSets.PropLogic.Core (LogicSent(parseIff))
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS )
import Text.XHtml (sub)
import qualified Internal.StdPattern
import Data.Maybe (isJust)

import Data.Text (Text, pack, unpack,concat, lines,intercalate)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )

import Debug.Trace(traceM)
import Data.Traversable (for)

parsePairFirstExp :: ObjDeBr -> Maybe ObjDeBr
parsePairFirstExp subexp = do
    (i,tupleObj) <- parseProjectHilbert subexp
    guard (i==0)
    return tupleObj





parseTupleMax :: ObjDeBr -> Maybe [ObjDeBr]
parseTupleMax obj = do
        (o1, o2) <- parsePair obj
        return (o1 : parseTupleMaxInternal o2)
    where
        parseTupleMaxInternal obj =
            case parsePair obj of
                Just (o1,o2) -> o1 : parseTupleMaxInternal o2
                Nothing -> [obj]



parseTupleFixed :: ObjDeBr -> Int -> Maybe [ObjDeBr]
parseTupleFixed obj n
      |  n == 0 = case obj of
                    EmptySet -> Just []
                    _ ->  Nothing
      |  n == 1 = Just [obj]
      |  n == 2 = do
            (o1, o2) <- parsePair obj
            return [o1, o2]
      | n > 2 = do
            (o1, o2) <- parsePair obj
            otherElements <- parseTupleFixed o2 (n-1)
            return $ o1 : otherElements 
      | otherwise = Nothing



pair :: ObjDeBr -> ObjDeBr -> ObjDeBr
pair o1 o2 = roster [roster[o1], roster[o1,o2]]

parsePair :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parsePair obj = do
    list <- parseRoster obj
    guard (length list == 2 || length list == 1)
    (o1, o2) <- if 
                  length list == 1 
                then
                  caseA (head list)
                else 
                  caseB (head list) (list!!1)
    return (o1,o2)
  where
    caseA obj = do
        list <- parseRoster obj
        guard (length list == 1)
        let o = head list
        return (o,o)
    caseB objA objB = do
        listA <- parseRoster objA
        listB <- parseRoster objB
        guard (length listA == 2 && length listB == 1 || length listA == 1 && length listB == 2)
        (o1, o2) <- if length listA == 2 && length listB == 1 then
                         caseBInternal (head listB) (head listA) (listA!!1)
                       else
                         caseBInternal (head listA) (head listB) (listB!!1)
        return (o1, o2)
    caseBInternal :: ObjDeBr -> ObjDeBr -> ObjDeBr -> Maybe (ObjDeBr,ObjDeBr)
    caseBInternal el1 el2a el2b = do
        guard (el1 == el2a || el1 == el2b)
        (o1,o2) <- if el1 == el2a then
                     return (el1, el2b)
                   else return (el1, el2a)
        return (o1,o2)






tuple :: [ObjDeBr] -> ObjDeBr
tuple objs =
    case objs of
        [] -> EmptySet
        [x] -> x
        (x:xs) -> pair x (tuple xs)



-- Parses a term to see if it matches the structure created by function application (f .@. x).
-- If it matches, returns Just (the_function_term, the_argument_term). Otherwise, returns Nothing.
--
-- Expected Structure:
-- Hilbert p'
-- where p' has the form: (Tupl [arg_term, Bound bound_idx] `In` graph_term)
-- and graph_term has the structure created by (project 3 2 func_triple_term)
-- and bound_idx is the index associated with the Hilbert binding (obtained via parseHilbert).
--
parseFuncApplication :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseFuncApplication obj = do
    -- 1. Match the Hilbert structure: Hilbert p'
    --    parseHilbert returns the inner proposition 'p'' and 'bound_idx'.
    --    'bound_idx' is the index used for the Bound variable associated with this Hilbert node.
    (inner_prop, bound_idx) <- parseHilbert obj

    -- 2. Match the 'In' structure within the inner proposition: tuple_term `In` graph_term
    (tuple_term, graph_term) <- parseIn inner_prop

    -- 3. Match the tuple structure: Tupl arg_term result_var
    -- arg_term is the potential argument 'x'
    -- result_var is the potential bound variable 'y'
    (arg_term, result_var) <- parsePair tuple_term


    -- 4. Verify the result_var is the Bound variable with the index from the Hilbert binding
    result_idx_parsed <- parseBound result_var
    guard (result_idx_parsed == bound_idx) -- Check if the bound index matches

    -- 5. Verify the graph_term corresponds to a projection of index 2 from a 3-tuple.
    --    Use parseProjectHilbert to recognize the projection structure and extract the original function triple.
    (projection_index, func_triple_term) <- parseProjectHilbert graph_term
    guard (projection_index == 2) -- Check it's the graph projection (index 2)

    -- Optional but recommended: Check that the extracted argument and function terms
    -- do not contain the bound variable from the outer Hilbert term.
    guard (not (objDeBrBoundVarInside arg_term bound_idx))
    guard (not (objDeBrBoundVarInside func_triple_term bound_idx))

    -- 6. If all checks pass, return the extracted function and argument terms
    return (func_triple_term, arg_term)


-- | Constructs the ObjDeBr term representing the union of a set of sets S.
--   ∪S = hX U (isSet(U) ∧ ∀x (x ∈ U ↔ ∃Y (Y ∈ S ∧ x ∈ Y)))
bigUnion :: ObjDeBr -> ObjDeBr
bigUnion setS =
    let
        -- Template variable indices
        setS_idx = 0 -- Placeholder for input setS
        x_idx    = 1 -- Placeholder for element 'x'
        y_idx    = 2 -- Placeholder for set 'Y' within S
        u_idx    = 3 -- Placeholder for the union set 'U' (bound by hX)

        -- Inner existential: ∃Y (Y ∈ S ∧ x ∈ Y)
        -- Using X y_idx for Y, X setS_idx for S, X x_idx for x
        inner_exists = eX y_idx ((X y_idx `In` X setS_idx) :&&: (X x_idx `In` X y_idx))

        -- Core property for elements: x ∈ U ↔ ∃Y (Y ∈ S ∧ x ∈ Y)
        -- Using X u_idx for U
        element_membership_prop = (X x_idx `In` X u_idx) :<->: inner_exists

        -- Universally quantify over x: ∀x (x ∈ U ↔ ...)
        quantified_element_prop = aX x_idx element_membership_prop

        -- Condition that U must be a set: isSet(U)
        -- Using X u_idx for U
        condition_U_isSet = isSet (X u_idx)

        -- Combine the conditions for U: isSet(U) ∧ ∀x(...)
        full_prop_for_U = condition_U_isSet :&&: quantified_element_prop

        -- Hilbert term: hX U (isSet(U) ∧ ∀x (...))
        -- hX binds X u_idx
        hilbertTemplate = hX u_idx full_prop_for_U

    -- Substitute the actual setS (for X setS_idx) into the Hilbert template
    in objDeBrSubX setS_idx setS hilbertTemplate


-- | Parses an ObjDeBr term to see if it matches the structure generated by 'bigUnion'.
-- | Returns Maybe setS on success.
-- | Expected structure: hX U (isSet(U) ∧ ∀x (x ∈ U ↔ ∃Y (Y ∈ S ∧ x ∈ Y)))
parseBigUnion :: ObjDeBr -> Maybe ObjDeBr
parseBigUnion obj = do
    -- 1. Match outer Hilbert: Hilbert p_conj
    --    idx_U is the De Bruijn index for the union set U, bound by hX.
    (p_conj, idx_U) <- parseHilbert obj

    -- 2. Expect p_conj to be a conjunction: isSet_U_prop :&&: forall_prop
    (isSet_U_prop, forall_prop) <- parseConjunction p_conj

    -- 3. Verify isSet_U_prop is isSet(Bound idx_U)
    --    parseIsSet should return the argument of isSet, which is (Bound idx_U)
    u_object_from_isSet <- parseIsSet isSet_U_prop
    u_bound_from_isSet <- parseBound u_object_from_isSet -- Extract the index from Bound
    guard (u_bound_from_isSet == idx_U) -- Check it's the correct Hilbert-bound variable

    -- 4. Match the second part of the conjunction: ∀x (biconditional_prop)
    --    idx_x is the De Bruijn index for x, bound by aX.
    (biconditional_prop, idx_x) <- parseForall2 forall_prop

    -- 5. Match Biconditional: x_in_U_prop :<->: exists_Y_prop
    (x_in_U_prop, exists_Y_prop) <- parseBiconditional biconditional_prop

    -- 6. Check LHS of biconditional: (Bound idx_x) `In` (Bound idx_U)
    (bound_x_lhs, bound_U_lhs) <- parseIn x_in_U_prop
    parsed_idx_x_lhs <- parseBound bound_x_lhs
    parsed_idx_U_lhs <- parseBound bound_U_lhs
    guard (parsed_idx_x_lhs == idx_x) -- x matches aX-bound variable
    guard (parsed_idx_U_lhs == idx_U) -- U matches hX-bound variable

    -- 7. Parse RHS of biconditional: ∃Y (Y_in_S_prop ∧ x_in_Y_prop)
    --    idx_y is the De Bruijn index for Y, bound by eX.
    (conj_Y_S_x_Y_prop, idx_y) <- parseExists exists_Y_prop

    -- 8. Parse inner Conjunction: Y_in_S_prop ∧ x_in_Y_prop
    (y_in_S_prop, x_in_Y_prop) <- parseConjunction conj_Y_S_x_Y_prop

    -- 9. Parse Y_in_S_prop: (Bound idx_y) `In` setS
    (bound_y_from_Y_in_S, setS) <- parseIn y_in_S_prop
    parsed_idx_y_from_Y_in_S <- parseBound bound_y_from_Y_in_S
    guard (parsed_idx_y_from_Y_in_S == idx_y) -- Y matches eX-bound variable

    -- 10. Parse x_in_Y_prop: (Bound idx_x) `In` (Bound idx_y)
    (bound_x_from_x_in_Y, bound_y_from_x_in_Y) <- parseIn x_in_Y_prop
    parsed_idx_x_from_x_in_Y <- parseBound bound_x_from_x_in_Y
    parsed_idx_y_from_x_in_Y <- parseBound bound_y_from_x_in_Y
    guard (parsed_idx_x_from_x_in_Y == idx_x) -- x matches aX-bound variable
    guard (parsed_idx_y_from_x_in_Y == idx_y) -- Y matches eX-bound variable

    -- 11. Sanity checks: setS (the input set to bigUnion) should not contain
    --     the bound variables idx_U (for the union U), idx_x (for elements of U),
    --     or idx_y (for elements Y of setS).
    guard (not (objDeBrBoundVarInside setS idx_U ||
                objDeBrBoundVarInside setS idx_x ||
                objDeBrBoundVarInside setS idx_y))

    -- 12. If all checks pass, return the original setS
    return setS



-- | Constructs the ObjDeBr term representing the intersection of a set of sets S.
--   Requires S to be non-empty for standard definition (handled by ∃Z(Z ∈ S)).
--   ∩S = hX I (isSet(I) ∧ ∀x (x ∈ I ↔ (∃Z(Z ∈ S) ∧ ∀Y (Y ∈ S → x ∈ Y))))
bigIntersection :: ObjDeBr -> ObjDeBr
bigIntersection setS =
    let
        -- Template variable indices
        setS_idx = 0 -- Placeholder for input setS
        x_idx    = 1 -- Placeholder for element 'x'
        y_idx    = 2 -- Placeholder for set 'Y' within S (used in the inner universal quantifier)
        z_idx    = 3 -- Placeholder for set 'Z' within S (used in the non-empty check existential)
        i_idx    = 4 -- Placeholder for the intersection set 'I' (bound by hX)

        -- Non-empty check: ∃Z (Z ∈ S)
        -- Using X z_idx for Z, X setS_idx for S
        non_empty_check = eX z_idx (X z_idx `In` X setS_idx)

        -- Inner universal: ∀Y (Y ∈ S → x ∈ Y)
        -- Using X y_idx for Y, X x_idx for x
        inner_forall = aX y_idx ((X y_idx `In` X setS_idx) :->: (X x_idx `In` X y_idx))

        -- Core property for elements: x ∈ I ↔ (NonEmptyCheck ∧ InnerForall)
        -- Using X i_idx for I
        element_membership_prop = (X x_idx `In` X i_idx) :<->: (non_empty_check :&&: inner_forall)

        -- Universally quantify over x: ∀x (x ∈ I ↔ ...)
        quantified_element_prop = aX x_idx element_membership_prop
        
        -- Condition that I must be a set: isSet(I)
        -- Using X i_idx for I
        condition_I_isSet = isSet (X i_idx)

        -- Combine the conditions for I: isSet(I) ∧ ∀x(...)
        full_prop_for_I = condition_I_isSet :&&: quantified_element_prop

        -- Hilbert term: hX I (isSet(I) ∧ ∀x (...))
        -- hX binds X i_idx
        hilbertTemplate = hX i_idx full_prop_for_I

    -- Substitute the actual setS (for X setS_idx) into the Hilbert template
    in objDeBrSubX setS_idx setS hilbertTemplate


-- | Parses an ObjDeBr term to see if it matches the structure generated by 'bigIntersection'.
-- | Returns Maybe setS on success.
-- | Expected structure: hX I (isSet(I) ∧ ∀x (x ∈ I ↔ (∃Z(Z ∈ S) ∧ ∀Y (Y ∈ S → x ∈ Y))))
parseBigIntersection :: ObjDeBr -> Maybe ObjDeBr
parseBigIntersection obj = do
    -- 1. Match outer Hilbert: Hilbert p_conj
    --    idx_I is the De Bruijn index for the intersection set I, bound by hX.
    (p_conj, idx_I) <- parseHilbert obj

    -- 2. Expect p_conj to be a conjunction: isSet_I_prop :&&: forall_elements_prop
    (isSet_I_prop, forall_elements_prop) <- parseConjunction p_conj

    -- 3. Verify isSet_I_prop is isSet(Bound idx_I)
    i_object_from_isSet <- parseIsSet isSet_I_prop
    i_bound_from_isSet <- parseBound i_object_from_isSet
    guard (i_bound_from_isSet == idx_I) -- Check it's the correct Hilbert-bound variable

    -- 4. Match the second part of the conjunction: ∀x (biconditional_prop)
    --    idx_x is the De Bruijn index for x, bound by aX.
    (biconditional_prop, idx_x) <- parseForall2 forall_elements_prop

    -- 5. Match Biconditional: x_in_I_prop :<->: definition_prop
    (x_in_I_prop, definition_prop) <- parseBiconditional biconditional_prop

    -- 6. Check LHS of biconditional: (Bound idx_x) `In` (Bound idx_I)
    (bound_x_lhs, bound_I_lhs) <- parseIn x_in_I_prop
    parsed_idx_x_lhs <- parseBound bound_x_lhs
    parsed_idx_I_lhs <- parseBound bound_I_lhs
    guard (parsed_idx_x_lhs == idx_x) -- x matches aX-bound variable
    guard (parsed_idx_I_lhs == idx_I) -- I matches hX-bound variable

    -- 7. Parse RHS of biconditional (definition_prop): non_empty_check_prop :&&: inner_forall_prop
    (non_empty_check_prop, inner_forall_prop) <- parseConjunction definition_prop

    -- 8. Parse non_empty_check_prop: ∃Z (Z_in_S_prop)
    --    idx_z is the De Bruijn index for Z, bound by eX.
    (z_in_S_prop, idx_z) <- parseExists non_empty_check_prop
    (bound_z_from_Z_in_S, setS_from_exists) <- parseIn z_in_S_prop
    parsed_idx_z_from_Z_in_S <- parseBound bound_z_from_Z_in_S
    guard (parsed_idx_z_from_Z_in_S == idx_z) -- Z matches eX-bound variable

    -- 9. Parse inner_forall_prop: ∀Y (Y_in_S_implies_x_in_Y_prop)
    --    idx_y is the De Bruijn index for Y, bound by aX.
    (y_in_S_implies_x_in_Y_prop, idx_y) <- parseForall2 inner_forall_prop

    -- 10. Parse Implication: y_in_S_prop_inner :->: x_in_Y_prop_inner
    (y_in_S_prop_inner, x_in_Y_prop_inner) <- parseImplication y_in_S_implies_x_in_Y_prop

    -- 11. Parse y_in_S_prop_inner: (Bound idx_y) `In` setS_from_forall
    (bound_y_from_Y_in_S, setS_from_forall) <- parseIn y_in_S_prop_inner
    parsed_idx_y_from_Y_in_S <- parseBound bound_y_from_Y_in_S
    guard (parsed_idx_y_from_Y_in_S == idx_y) -- Y matches aX-bound variable from inner_forall_prop

    -- 12. Parse x_in_Y_prop_inner: (Bound idx_x) `In` (Bound idx_y)
    (bound_x_from_x_in_Y, bound_y_from_x_in_Y) <- parseIn x_in_Y_prop_inner
    parsed_idx_x_from_x_in_Y <- parseBound bound_x_from_x_in_Y
    parsed_idx_y_from_x_in_Y <- parseBound bound_y_from_x_in_Y
    guard (parsed_idx_x_from_x_in_Y == idx_x) -- x matches outer aX-bound variable
    guard (parsed_idx_y_from_x_in_Y == idx_y) -- Y matches inner aX-bound variable

    -- 13. Check that setS from the non-empty check and setS from the inner universal quantifier match
    guard (setS_from_exists == setS_from_forall)
    let setS = setS_from_exists -- Use one of them as the definitive setS

    -- 14. Sanity checks: setS (the input set to bigIntersection) should not contain
    --     the bound variables idx_I (for intersection I), idx_x (element of I),
    --     idx_z (dummy Z for non-empty check), or idx_y (element Y of setS).
    guard (not (objDeBrBoundVarInside setS idx_I ||
                objDeBrBoundVarInside setS idx_x ||
                objDeBrBoundVarInside setS idx_z ||
                objDeBrBoundVarInside setS idx_y))

    -- 15. If all checks pass, return the original setS
    return setS





parseHilbertShort :: ObjDeBr -> Map PropDeBr [Int] -> Maybe [Int]
parseHilbertShort subexp dict = 
    case subexp of
        Hilbert p ->
            Just =<< Data.Map.lookup (Exists p) dict 
        _ -> Nothing

--parsePair :: ObjDeBr -> Maybe (ObjDeBr,ObjDeBr)
--parsePair subexp = do
--    list <- parseTupl subexp
--    guard (length list == 2)
--    return (head list,list!!1)

parseComposition :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseComposition obj = do
    -- 1. Expect hX h_idx (...)
    (body, hIdx) <- parseHilbert obj

    -- 2. Expect body to be prop1 :&&: prop2
    (prop1_parsed, prop2_parsed) <- parseConjunction body

    -- 3. Minimally check prop1 structure: (X hIdx) `In` some_set
    --    We don't need to fully deconstruct/verify the set expression here,
    --    just ensure the left side of 'In' is the correctly bound 'h'.
    (h_check, _funcs_set_check) <- parseIn prop1_parsed
    hIdx_check <- parseBound h_check
    guard (hIdx_check == hIdx) -- Make sure 'h' in prop1 is the one bound by hX

    -- 4. Deconstruct prop2: aX x_idx ( L :==: R )
    (equalityExpr, xIdx) <- parseForall2 prop2_parsed
    (ls, rs) <- parseEqual equalityExpr

    -- 5. Deconstruct LHS of equality: h .@. x
    (h_term_ls, x_term_ls) <- parseFuncApplication ls
    hIdx_ls <- parseBound h_term_ls
    guard (hIdx_ls == hIdx) -- Check h index matches hX binder
    xIdx_ls <- parseBound x_term_ls
    guard (xIdx_ls == xIdx) -- Check x index matches aX binder

    -- 6. Deconstruct RHS of equality: f .@. (g .@. x)
    --    Extract f first
    (f, gAtX) <- parseFuncApplication rs
    --    Check f doesn't contain free h (hIdx) or x (xIdx) variables
    guard (not (objDeBrBoundVarInside f hIdx))
    guard (not (objDeBrBoundVarInside f xIdx))

    --    Extract g from g .@. x
    (g, x_term_rs) <- parseFuncApplication gAtX
    --    Check g doesn't contain free h (hIdx) or x (xIdx) variables
    guard (not (objDeBrBoundVarInside g hIdx))
    guard (not (objDeBrBoundVarInside g xIdx))
    --    Check the argument x matches the bound x
    xIdx_rs <- parseBound x_term_rs
    guard (xIdx_rs == xIdx) -- Check x index matches aX binder

    -- 7. If all checks passed, return the extracted f and g
    return (f, g)



-- Helper to recursively parse a chain of Forall quantifiers
-- Returns the inner most term,
-- the count of exists quantifiers and the binding depth of
-- the innermost term.
-- Note: The depths returned are NOT relative to the context *outside* the chain.
parseForallChain :: PropDeBr -> Maybe (PropDeBr, Int, Int)
parseForallChain prop = fmap g (go prop 0)
  where
    go p quantifierCount =
      case p of
        Forall inner ->
          go inner (quantifierCount + 1) -- Increment quantifier count
        _ -> Just (p, quantifierCount)
    g (p, quantifierCount) = (p, quantifierCount, boundDepthPropDeBr p)



-- Helper to recursively parse a chain of Exists quantifiers
-- Returns the inner most term,
-- the count of exists quantifiers and the binding depth of
-- the innermost term.
-- Note: The depths returned are NOT relative to the context *outside* the chain.
parseExistsChain :: PropDeBr -> Maybe (PropDeBr, Int, Int)
parseExistsChain prop = fmap g (go prop 0)
  where
    go p quantifierCount =
      case p of
        Exists inner ->
          go inner (quantifierCount + 1) -- Increment quantifier count
        _ -> Just (p, quantifierCount)
    g (p, quantifierCount) = (p, quantifierCount, boundDepthPropDeBr p)


-- | Attempts to parse an ObjDeBr term to see if it matches the Hilbert
-- | expression structure generated by the `project n m t` helper function.
-- | Returns Maybe (projection_index, original_tuple_term) on success.
-- | Includes checks to ensure the recovered term 't' does not contain
-- | Bound variables referring back to the internal binders of the projection structure.
-- | WARNING: Relies heavily on the specific internal structure generated by `project`.
parseProjectHilbert :: ObjDeBr -> Maybe (Int, ObjDeBr)
parseProjectHilbert obj = do
    -- 1. Check for Hilbert Term: ε r . P(r)
    (p, norm_h) <- parseHilbert obj -- norm_h is the depth for 'r'

    -- 2. Parse the chain of Exists quantifiers: ∃ y_i ... (lhs == rhs)
    --    Get body, count of quantifiers (k), and depth of body (d)
    (equalityBody, quantifierCount, d) <- parseExistsChain p




    -- 3. Parse the Equality: lhs == rhs
    (lhs, rhs) <- parseEqual equalityBody
    let recovered_t = lhs -- Treat lhs as the recovered original term t

    -- 4. Parse the RHS Tuple: Tupl [arg0, ..., argN-1]
    let n = quantifierCount + 1 -- n is the number of arguments in the tuple
    parsedArgs <- parseTupleFixed rhs n
    


    -- 5. Find the argument matching the Hilbert binder (Bound norm_h).
    --    Its list index is the projection index 'm'.
    m <- findIndex (\case Bound b -> b == norm_h; _ -> False) parsedArgs

    -- 6. Verify other arguments and their indices
    let (r_arg_list, other_args) = partition (\case Bound b -> b == norm_h; _ -> False) parsedArgs
    guard (length r_arg_list == 1)
    guard (length other_args == quantifierCount)

    actualIndices <- mapM parseBound other_args


    let expectedIndices = [d .. d + quantifierCount - 1]
    guard (sort actualIndices == expectedIndices)

    -- == Validation Checks on recovered_t (lhs) ==
    guard (not (objDeBrBoundVarInside recovered_t norm_h))
    guard (not (any (objDeBrBoundVarInside recovered_t) expectedIndices))
    -- 8. Return result: projection index m and the recovered term t

    return (m, recovered_t)








parseIsTupleApp :: PropDeBr -> Maybe (Int, ObjDeBr)
parseIsTupleApp prop = do
    -- 1. Parse the chain of Exists quantifiers.
    (equalityBody, n, base_depth) <- parseExistsChain prop -- Returns (body, count, depth)

    -- 2. Parse the innermost body as an equality: term' == tuple_term
    (term', tuple_term) <- parseEqual equalityBody

    -- 3. Parse the RHS of the equality as a tuple: Tupl [arg_0, ..., arg_n_1]
    args <- parseTupleFixed tuple_term n


    -- 4. Verify that each argument 'arg_i' in the tuple is the correct Bound variable.
    --    The i-th argument (args !! i) should be Bound(base_depth + n - 1 - i)
    --    due to the order 'foldr eX' binds variables.
    let checkArgIndexed i arg = case arg of
            Bound actualIdx -> Just (actualIdx == (base_depth + n - 1 - i))
            _               -> Just False -- Argument is not a Bound var

    -- Check if all arguments match their expected Bound index using the corrected logic.
    allMatch <- Control.Monad.zipWithM checkArgIndexed [0 .. ] args
    guard (and allMatch) -- This guard is now logically correct.

    -- 5. Optional Sanity Check: Ensure 'term'' doesn't capture binders.
    --    The expected indices are base_depth to base_depth + n - 1
    let boundIndicesRange = [base_depth .. base_depth + n - 1]
    guard (not (any (objDeBrBoundVarInside term') boundIndicesRange))


    -- 6. If all checks passed, return the tuple length 'n' and the term 'term''
    return (n, term')


-- Helper function to collect all top-level conjuncts from a PropDeBr
-- Handles right-associativity: A && (B && C) -> [A, B, C]
getAllConjuncts :: PropDeBr -> [PropDeBr]
getAllConjuncts (p :&&: q) = p : getAllConjuncts q
getAllConjuncts p          = [p] -- Base case: not a conjunction





-- | Constructs the ObjDeBr term representing the set of functions from A to B.
--   Now asserts that the set of functions itself is a set.
funcsSet :: ObjDeBr -> ObjDeBr -> ObjDeBr
funcsSet setA setB =
    let
        setA_idx = 0; setB_idx = 1; f_idx = 2; s_idx = 3
        propTemplate = (X f_idx `In` X s_idx) :<->: isFunc (X f_idx) (X setA_idx) (X setB_idx)
        quantifiedProp = aX f_idx propTemplate
        
        condition_S_isSet = isSet (X s_idx)
        full_prop_for_S = condition_S_isSet :&&: quantifiedProp
        
        hilbertTemplate = hX s_idx full_prop_for_S
    in objDeBrSubXs [(setA_idx, setA), (setB_idx, setB)] hilbertTemplate

-- | Parses an ObjDeBr term to see if it matches the structure generated by 'funcsSet'.
--   Now expects isSet(S) as part of the definition.
parseFuncsSet :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseFuncsSet obj = do
    (p_conj, idx_S) <- parseHilbert obj
    (isSet_S_prop, forall_f_prop) <- parseConjunction p_conj
    s_object_from_isSet <- parseIsSet isSet_S_prop
    s_bound_from_isSet <- parseBound s_object_from_isSet
    guard (s_bound_from_isSet == idx_S)
    (bicond_prop, idx_f) <- parseForall2 forall_f_prop
    (f_in_S_prop, isFunc_call_prop) <- parseBiconditional bicond_prop
    (bound_f_lhs, bound_S_lhs) <- parseIn f_in_S_prop
    parsed_idx_f_lhs <- parseBound bound_f_lhs
    parsed_idx_S_lhs <- parseBound bound_S_lhs
    guard (parsed_idx_f_lhs == idx_f)
    guard (parsed_idx_S_lhs == idx_S)


    (funcTerm_from_isFunc, setA_cand, setB_cand) <- parseIsFunc isFunc_call_prop


    parsed_f_cand_idx <- parseBound funcTerm_from_isFunc
    guard (parsed_f_cand_idx == idx_f)
 
    guard (not (objDeBrBoundVarInside setA_cand idx_f || objDeBrBoundVarInside setA_cand idx_S))
    guard (not (objDeBrBoundVarInside setB_cand idx_f || objDeBrBoundVarInside setB_cand idx_S))
    return (setA_cand, setB_cand)




-- Asserts that x is the tuple formed by the elements in the list 'elements'
-- in that specific order.
isTupleWhere :: ObjDeBr -> [ObjDeBr] -> PropDeBr
isTupleWhere x elements =
    x :==: tuple elements

-- Parser for isTupleWhere
-- Takes an expected tuple length and a proposition.
-- If the proposition is 'x :==: tuple elements_candidate' and
-- 'elements_candidate' has the expected length,
-- it returns Just (x, elements_candidate). Otherwise, Nothing.
parseIsTupleWhere :: Int -> PropDeBr -> Maybe (ObjDeBr, [ObjDeBr])
parseIsTupleWhere expectedLength prop = do
    -- Step 1: Check if the proposition is an equality x :==: potentialTuple.
    (x, potentialTupleTerm) <- parseEqual prop

    -- Step 2: Try to parse potentialTupleTerm as a tuple of the expectedLength.
    -- parseTupleFixed will return Nothing if potentialTupleTerm is not a tuple
    -- of the precisely 'expectedLength' that matches the structure of tuple.
    elements_candidate <- parseTupleFixed potentialTupleTerm expectedLength

    -- If both steps succeeded, return the left-hand side of the equality (x)
    -- and the list of elements parsed from the right-hand side.
    return (x, elements_candidate)





-- | Predicate: Checks if an ObjDeBr term 'f' represents a function from setA to setB.
--   Asserts that there exists a graph such that
--   f is the tuple (setA, setB, graph) and these components satisfy
--   the necessary function properties.
isFunc :: ObjDeBr -> ObjDeBr -> ObjDeBr -> PropDeBr
isFunc f setA setB =
    let
        -- Template variable index for the existential quantifier
        gr_idx  = 0 -- for the graph component


        -- Placeholder for graph within the existential scope
        gr  = X gr_idx

        -- Template variable indicides for f, setA and setB
        f_idx = 1
        setA_idx = 2 -- Placeholder for the given setA
        setB_idx = 3 -- Placeholder for the given setB


        -- Functionality check: ∀x_fun (x_fun ∈ dom → ∃!y_fun (<x_fun,y_fun> ∈ gr))
        -- Using fresh template indices for the variables in the functionality check
        -- to avoid collision with dom_idx, cod_idx, gr_idx if they were also 0 or 1.
        x_fun_idx = 4 -- Placeholder for 'x' in functionality check
        y_fun_idx = 5 -- Placeholder for 'y' in functionality check

        -- Constructing functionality_check relative to 'dom' and 'gr'
        functionality_check_on_components =
            aX x_fun_idx (
                (X x_fun_idx `In` X setA_idx)
                :->:
                eXBang y_fun_idx (pair (X x_fun_idx) (X y_fun_idx) `In` gr)
            )

        -- The body of the existential quantifier:
        bound_properties =          -- C3: The bound properties
            isTupleWhere (X f_idx) [X setA_idx, X setB_idx, gr]  -- C3A: f is the tuple (dom, cod, gr)                -- C3: The codomain component is a set
            :&&: isRelationOn gr (X setA_idx) (X setB_idx)         -- C3B: gr is a relation from dom to cod
                                                 -- (implies gr isSet and elements are pairs from dom x cod)
            :&&: functionality_check_on_components -- C3C: f satisfies the functionality property

        properties = 
            isSet (X setA_idx) -- C1: The domain component is a set
            :&&: isSet (X setB_idx) -- C2: The codomain component is a set
            :&&: eX gr_idx bound_properties -- C3: The bound properties 

    in
        propDeBrSubXs [(f_idx,f),(setA_idx,setA),(setB_idx,setB)]  ( 
                properties
        )


-- | Parses a proposition to see if it matches the latest simplified structure
-- | created by 'isFunc f setA setB'.
-- | Returns Maybe (f, setA, setB) on success.
parseIsFunc :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr, ObjDeBr)
parseIsFunc prop = do
    -- 1. Deconstruct the top-level conjunctions:
    --    prop = (isSet setA_actual) :&&: (isSet setB_actual) :&&: (eX gr_idx (...))
    (c1_isSet_setA, rest1)     <- parseConjunction prop
    (c2_isSet_setB, c3_exists_gr_prop) <- parseConjunction rest1

    -- 2. Parse C1 to get setA_actual
    setA_actual <- parseIsSet c1_isSet_setA

    -- 3. Parse C2 to get setB_actual
    setB_actual <- parseIsSet c2_isSet_setB

    -- 4. Peel off the leading existential quantifier from C3 to get the inner properties.
    --    The graph 'gr' (which was X gr_idx = X 0 in the template for eX) is now
    --    Bound gr_b_expected_idx,
    --    within 'inner_properties_body'.
    (inner_properties_body, gr_b_expected_idx) <- parseExists c3_exists_gr_prop
    let gr_b_expected = Bound gr_b_expected_idx

    -- 5. The 'inner_properties_body' is itself a conjunction:
    --    InnerC1: isTupleWhere f_actual [setA_actual, setB_actual, gr_b_expected]
    --    InnerC2: isRelationOn gr_b_expected setA_actual setB_actual
    --    InnerC3: functionality_check(setA_actual, gr_b_expected)
    --    We only need to parse InnerC1 to extract f_actual for the reconstruction shortcut.
    (inner_c1_isTupleWhere, _rest_of_inner_props) <- parseConjunction inner_properties_body

    -- 6. Parse InnerC1 to extract f_actual and verify consistency of setA, setB, and gr_b.
    (f_extracted, components) <- parseIsTupleWhere 3 inner_c1_isTupleWhere
    guard (length components == 3)
    let setA_from_tuple = components !! 0
    let setB_from_tuple = components !! 1
    let gr_from_tuple   = components !! 2

    guard (setA_from_tuple == setA_actual) -- Check setA from tuple matches setA from isSet
    guard (setB_from_tuple == setB_actual) -- Check setB from tuple matches setB from isSet
    guard (gr_from_tuple == gr_b_expected) -- Check graph from tuple matches the bound graph

    -- At this point, f_extracted, setA_actual, and setB_actual
    -- are our candidates for the original arguments to isFunc.
    let f_candidate = f_extracted
    -- setA_actual and setB_actual are already defined from steps 2 & 3.

    -- 7. Shortcut: Reconstruct 'isFunc f_cand setA_cand setB_cand' and compare with the input 'prop'.
    --    This implicitly verifies the structure of InnerC2 (isRelationOn) and InnerC3 (functionality_check).
    guard (isFunc f_candidate setA_actual setB_actual == prop)

    -- If all checks passed
    return (f_candidate, setA_actual, setB_actual)




        
parseNotIn :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseNotIn p = case p of
    Neg (a `In` b) -> Just (a, b)
    _ -> Nothing


-- Negation Shorthands & Default
parseNotEqual :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseNotEqual p = case p of
    Neg (a :==: b) -> Just (a, b)
    _ -> Nothing

-- Now s1 ⊆ s2  is defined as  isSet(s1) ∧ (∀x (x ∈ s1 → x ∈ s2))
subset :: ObjDeBr -> ObjDeBr -> PropDeBr
subset a b =
    let
        -- The standard universal quantification part: ∀x (x ∈ a → x ∈ b)
        -- Uses template variables X 1 for 'a', X 0 for 'b', and X 2 for 'x' (bound by aX)
        forall_part = propDeBrSubXs [(1,a),(0,b)] (aX 2 (X 2 `In` X 1 :->: X 2 `In` X 0))
    in
        isSet a :&&: forall_part -- Conjoin with isSet a
infix 4 `subset`


-- Expects: (isSet s1_candidate) :&&: (∀x (x ∈ s1_candidate → x ∈ s2))
parseSubset :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseSubset p = do
    -- 1. Expect top level to be conjunction
    (isSet_prop_candidate, forall_part_candidate) <- parseConjunction p

    -- 2. Parse the first conjunct, expecting it to be `isSet s1`
    s1 <- parseIsSet isSet_prop_candidate -- s1 is the ObjDeBr from isSet
    -- 3. Parse the second conjunct, expecting the universal quantification part
    (implication, norm_idx_x) <- parseForall2 forall_part_candidate -- norm_idx_x is the depth of 'x'
    (xInS1_prop, xInS2_prop) <- parseImplication implication

    -- 4. Parse x ∈ s1' from the antecedent of the implication
    (x_obj_s1, s1_from_quantifier) <- parseIn xInS1_prop
    x_bound_idx_s1 <- parseBound x_obj_s1
    guard (x_bound_idx_s1 == norm_idx_x) -- Check if 'x' is the correct bound variable

    -- 5. Crucially, verify that s1 from `isSet` is the same as s1' from the quantifier
    guard (s1 == s1_from_quantifier)
    -- Also ensure s1 does not capture the universally quantified variable 'x'
    guard (not (objDeBrBoundVarInside s1 norm_idx_x))

    -- 6. Parse x ∈ s2 from the consequent of the implication
    (x_obj_s2, s2) <- parseIn xInS2_prop
    x_bound_idx_s2 <- parseBound x_obj_s2
    guard (x_bound_idx_s2 == norm_idx_x) -- Check if 'x' is the correct bound variable
    -- Ensure s2 does not capture the universally quantified variable 'x'
    guard (not (objDeBrBoundVarInside s2 norm_idx_x))

    -- 7. If all checks pass, return the identified s1 and s2
    return (s1, s2)



parseStrictSubset :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseStrictSubset p = do
    (forallImp,abIneq) <- parseConjunction p
    (a,b) <- parseSubset forallImp
    (a2,b2) <- parseNotEqual abIneq
    guard (a2==a)
    guard (b2==b)
    return (a,b)


parseNotSubset :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseNotSubset p = do
   imp <- parseNegation p
   (a,b) <- parseSubset imp
   return (a,b)


parseExistsUnique :: PropDeBr -> Maybe (PropDeBr, Int)
parseExistsUnique subexp = do
    (mainConj, norm1) <- parseExists subexp
    (p1,forallImp) <- parseConjunction mainConj
    (imp, norm2) <- parseForall2 forallImp
    (p2,equality) <- parseImplication imp
    let p1Decremented = boundDecrementPropDeBr norm1 p1
    guard (p1Decremented == p2)
    (x1,x2) <- parseEqual equality
    guard (x2 == Bound norm1 && x1 == Bound norm2)
    return (p2,norm2)







boundDecrementObjDeBr :: Int -> ObjDeBr -> ObjDeBr
boundDecrementObjDeBr idx obj = case obj of
     Integ num -> Integ num
     Constant name -> Constant name
     Hilbert prop -> Hilbert (boundDecrementPropDeBr idx prop)
     Bound i -> if i == idx then Bound (i - 1) else Bound i
     V i -> V i
     X i -> X i
     (:+:) o1 o2 -> (:+:) (boundDecrementObjDeBr idx o1) (boundDecrementObjDeBr idx o2)
     (:*:) o1 o2 -> (:*:) (boundDecrementObjDeBr idx o1) (boundDecrementObjDeBr idx o2)
     EmptySet -> EmptySet
     IntSet -> IntSet





boundDecrementPropDeBr :: Int -> PropDeBr -> PropDeBr
boundDecrementPropDeBr idx prop = case prop of
    Neg q -> Neg $ boundDecrementPropDeBr idx q
    (:&&:) p1 p2 -> (:&&:) (boundDecrementPropDeBr idx p1) (boundDecrementPropDeBr idx p2)
    (:||:) p1 p2 -> (:||:) (boundDecrementPropDeBr idx p1) (boundDecrementPropDeBr idx p2)
    (:->:) p1 p2 -> (:->:) (boundDecrementPropDeBr idx p1) (boundDecrementPropDeBr idx p2)
    (:<->:) p1 p2 -> (:<->:) (boundDecrementPropDeBr idx p1) (boundDecrementPropDeBr idx p2)
    (:==:) o1 o2 -> (:==:) (boundDecrementObjDeBr idx o1) (boundDecrementObjDeBr idx o2)
    In o1 o2 -> In (boundDecrementObjDeBr idx o1) (boundDecrementObjDeBr idx o2)
    Forall q -> Forall (boundDecrementPropDeBr idx q)
    Exists q -> Exists (boundDecrementPropDeBr idx q)
    (:<=:) o1 o2 -> (:<=:) (boundDecrementObjDeBr idx o1) (boundDecrementObjDeBr idx o2)
    F -> F






isPair :: ObjDeBr -> PropDeBr
isPair = isTuple 2



--isPair t = propDeBrSubX 2 t $  eX 0 $ eX 1 $ X 2 :==: Tupl [X 0,X 1]


isRelation :: ObjDeBr -> PropDeBr
isRelation s =
    let
        -- X 0 is the placeholder for 'x', bound by aX.
        -- 's' is passed directly.
        all_elements_are_pairs = aX 0 ((X 0 `In` s) :->: isPair (X 0))
    in
        isSet s :&&: all_elements_are_pairs -- Conjoin with isSet s




-- Parser for the modified isRelation structure
-- Expected: (isSet s_outer) :&&: (∀x (x ∈ s_outer → isPair(x)))
parseIsRelation :: PropDeBr -> Maybe ObjDeBr -- Returns the ObjDeBr s that is asserted to be a relation
parseIsRelation prop = do
    -- 1. Expect top level to be a conjunction
    (isSet_prop_candidate, forall_part_candidate) <- parseConjunction prop

    -- 2. Parse the first conjunct, expecting it to be `isSet s`
    s_from_isSet <- parseIsSet isSet_prop_candidate -- This is the s we are looking for

    -- 3. Parse the second conjunct: ∀x ( (x ∈ s_from_quantifier) → isPair(x) )
    --    idx_x_bound is the De Bruijn index for x, bound by aX.
    (implication_prop, idx_x_bound) <- parseForall2 forall_part_candidate

    -- 4. Parse the implication: x_in_s_prop :->: isPair_x_prop
    (x_in_s_prop, isPair_x_prop) <- parseImplication implication_prop

    -- 5. Parse the antecedent x_in_s_prop: (Bound idx_x_bound) `In` s_from_quantifier
    (x_obj, s_from_quantifier) <- parseIn x_in_s_prop
    x_bound_idx <- parseBound x_obj
    guard (x_bound_idx == idx_x_bound) -- Verify 'x' is the correct bound variable

    -- 6. Crucially, verify that s_from_isSet is the same 's' used in the quantifier part.
    guard (s_from_isSet == s_from_quantifier)
    -- And ensure this 's' does not capture the quantified variable 'x'.
    guard (not (objDeBrBoundVarInside s_from_isSet idx_x_bound))

    -- 7. Verify the consequent isPair_x_prop is indeed isPair(Bound idx_x_bound).
    --    We use parseIsTupleApp because isPair x is defined as isTuple 2 x.
    --    parseIsTupleApp returns Maybe (tuple_size, term_asserted_as_tuple)
    (tuple_size, term_is_pair_arg) <- parseIsTupleApp isPair_x_prop
    guard (tuple_size == 2) -- Check it's specifically about pairs (tuples of size 2)
    
    -- Check that the argument to isPair is indeed (Bound idx_x_bound)
    x_arg_bound_idx <- parseBound term_is_pair_arg
    guard (x_arg_bound_idx == idx_x_bound)

    -- 8. If all checks pass, return s_from_isSet (the object asserted to be a relation)
    return s_from_isSet

isRelationOn :: ObjDeBr -> ObjDeBr -> ObjDeBr -> PropDeBr
isRelationOn s domain codomain =
    s `subset` crossProd domain codomain


-- Parser for isRelationOn
-- If prop matches the structure s `subset` (crossProd domain codomain),
-- returns Just (s, domain, codomain). Otherwise, Nothing.
parseIsRelationOn :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr, ObjDeBr)
parseIsRelationOn prop = do
    -- Step 1: Attempt to parse the proposition as 's `subset` some_object'.
    -- 's_candidate' will be the relation itself.
    -- 'crossProd_candidate' should be the (crossProd domain codomain) term.
    (s_candidate, crossProd_candidate) <- parseSubset prop

    -- Step 2: Attempt to parse 'crossProd_candidate' as 'crossProd domain_candidate codomain_candidate'.
    (domain_candidate, codomain_candidate) <- parseCrossProduct crossProd_candidate

    -- If both parsing steps succeed, return the extracted components.
    return (s_candidate, domain_candidate, codomain_candidate)



-- Now specifies that the built object B (represented by XInternal b_placeholder_idx) satisfies isSet.
-- user_x_idx: The index used for the template variable X in the user's predicate p.
-- source_set_t: The ObjDeBr for the source set T.
-- user_predicate_p: The PropDeBr for the predicate P(X user_x_idx).
builderX :: Int -> ObjDeBr -> PropDeBr -> ObjDeBr
builderX user_x_idx source_set_t user_predicate_p =
    let
        -- Internal placeholder indices for the definition. These are distinct from user_x_idx.
        source_set_max_X = maybe (-1) id (objMaxXIdx source_set_t) -- Max template var index in source_set_t
        user_predicate_max_X = maybe (-1) id (propMaxXIdx user_predicate_p) -- Max template var index in user_predicate_p
        new_idx_base = maximum [
                                source_set_max_X,
                                user_predicate_max_X,
                                user_x_idx
                               ] + 1 
        b_placeholder_idx = new_idx_base -- Placeholder for the set B being built (becomes XInternal b_placeholder_idx)
        t_placeholder_idx = new_idx_base + 1 -- Placeholder for the source set T (becomes XInternal t_placeholder_idx)

        -- Core membership definition: (x ∈ B) ↔ (P(x) ∧ x ∈ T)
        -- Here:
        -- 'x' is represented by (X user_x_idx)
        -- 'B' (the set being defined) is represented by (XInternal b_placeholder_idx)
        -- 'T' (the source set) is represented by (XInternal t_placeholder_idx)
        -- 'P(x)' is user_predicate_p (which should use (X user_x_idx))
        membership_definition = (X user_x_idx `In` X b_placeholder_idx)
                              :<->:
                              (user_predicate_p :&&: (X user_x_idx `In` X t_placeholder_idx))

        -- Universally quantify over x: ∀x ( (x ∈ B) ↔ (P(x) ∧ x ∈ T) )
        -- The aX will bind (X user_x_idx) to a De Bruijn index.
        forall_x_membership_definition = aX user_x_idx membership_definition

        -- Condition that the built set B must be a set: isSet(B)
        -- 'B' is represented by (XInternal b_placeholder_idx)
        b_is_set_condition = isSet (X b_placeholder_idx)

        -- Combine: isSet(B) ∧ ∀x(...)
        -- This is the full property that B must satisfy.
        full_property_for_b = b_is_set_condition :&&: forall_x_membership_definition

        -- Hilbert term template: εB (isSet(B) ∧ ∀x(...))
        -- The hXInt will bind (XInternal b_placeholder_idx) to a De Bruijn index.
        hilbert_template_for_b = hX b_placeholder_idx full_property_for_b

    -- Substitute the actual source_set_t for its placeholder (XInternal t_placeholder_idx)
    -- in the constructed Hilbert term.
    in objDeBrSubX t_placeholder_idx source_set_t hilbert_template_for_b


-- Modified parseSetBuilder to recognize the new structure
-- Expected: Hilbert idx_B_bound (isSet(Bound idx_B_bound) ∧ ∀idx_x_bound ( (Bound idx_x_bound ∈ Bound idx_B_bound) ↔ (predicate_q ∧ (Bound idx_x_bound ∈ source_set_t)) ))
parseSetBuilder :: ObjDeBr -> Maybe (ObjDeBr, PropDeBr, Int)
parseSetBuilder obj = do
    -- 1. Match outer Hilbert: Hilbert p_conj
    --    idx_B_bound is the De Bruijn index for the built set B, bound by hX.
    (p_conj, idx_B_bound) <- parseHilbert obj

    -- 2. Expect p_conj to be a conjunction: isSet_B_prop :&&: forall_elements_prop
    (isSet_B_prop, forall_elements_prop) <- parseConjunction p_conj

    -- 3. Verify isSet_B_prop is isSet(Bound idx_B_bound)
    b_object_from_isSet <- parseIsSet isSet_B_prop
    b_bound_from_isSet <- parseBound b_object_from_isSet
    guard (b_bound_from_isSet == idx_B_bound) -- Check it's the correct Hilbert-bound variable B

    -- 4. Now parse forall_elements_prop, which is ∀x (x ∈ B ↔ (P(x) ∧ x ∈ T))
    --    idx_x_bound is the De Bruijn index for x, bound by aX.
    (bicond_prop, idx_x_bound) <- parseForall2 forall_elements_prop

    -- 5. Match Biconditional: lhs_membership :<->: rhs_condition
    (lhs_membership, rhs_condition) <- parseBiconditional bicond_prop

    -- 6. Parse LHS of biconditional: (Bound idx_x_bound) `In` (Bound idx_B_bound)
    (x_obj_lhs, b_obj_lhs) <- parseIn lhs_membership
    x_bound_lhs <- parseBound x_obj_lhs
    b_bound_lhs <- parseBound b_obj_lhs
    guard (x_bound_lhs == idx_x_bound) -- x matches aX-bound variable
    guard (b_bound_lhs == idx_B_bound) -- B matches hX-bound variable

    -- 7. Parse RHS of biconditional: predicate_q :&&: ((Bound idx_x_bound) `In` source_set_t)
    (predicate_q, x_in_t_prop) <- parseConjunction rhs_condition

    -- 8. Sanity Check: predicate_q (which contains Bound idx_x_bound for the user's X variable)
    --    should not accidentally capture the Hilbert-bound variable B (idx_B_bound).
    guard (not (propDeBrBoundVarInside predicate_q idx_B_bound))

    -- 9. Parse ((Bound idx_x_bound) `In` source_set_t) from the second part of the RHS conjunction
    (x_obj_rhs_in_t, source_set_t) <- parseIn x_in_t_prop
    x_bound_rhs_in_t <- parseBound x_obj_rhs_in_t
    guard (x_bound_rhs_in_t == idx_x_bound) -- x matches aX-bound variable

    -- 10. Sanity Checks for source_set_t:
    --     It should not capture the Hilbert-bound B (idx_B_bound).
    --     It should not capture the universally quantified x (idx_x_bound).
    guard (not (objDeBrBoundVarInside source_set_t idx_B_bound))
    guard (not (objDeBrBoundVarInside source_set_t idx_x_bound))

    -- 11. If all checks pass, return:
    --     - source_set_t: The ObjDeBr of the source set T.
    --     - predicate_q: The PropDeBr for P(x). Inside predicate_q, the user's original (X user_x_idx)
    --                    is now represented as (Bound idx_x_bound) due to the aX binding.
    --     - idx_x_bound: The De Bruijn index that 'x' (the element variable) is bound to by 'aX'.
    --                    This is the "normalization depth" or effective index of 'x' within predicate_q.
    return (source_set_t, predicate_q, idx_x_bound)




strictSubset :: ObjDeBr -> ObjDeBr -> PropDeBr
strictSubset a b = subset a b :&&: Neg (a :==: b)

infix 4 `strictSubset`

notSubset :: ObjDeBr -> ObjDeBr -> PropDeBr
notSubset a b = Neg (subset a b)

infix 4 `notSubset`

-- | Generates an ObjDeBr term representing the projection of the m-th element
-- | from an n-tuple t. Uses a Hilbert expression internally.
-- | project n m t = "the element r such that there exist y0..y(m-1),y(m+1)..y(n-1)
-- |                where t = tuple [y0, ..., y(m-1), r, y(m+1), ..., y(n-1)]"
project :: Int -> Int -> ObjDeBr -> ObjDeBr
project n m t =
    -- n: the length of the tuple (integer)
    -- m: the 0-based index to project (integer)
    -- t: the tuple object (ObjDeBr)

    -- Basic bounds check for the index
    if m < 0 || m >= n then
        error ("project: index " ++ show m ++ " out of bounds for length " ++ show n)
    else
        let
            -- Choose indices for template variables used within the generated expression:
            -- Index for the variable bound by hX (representing the result 'r')
            resultIdx   = n
            -- Index for the placeholder representing the input tuple 't'
            tupleIdx    = n + 1
            -- Indices for the existentially quantified variables 'yi' (0..n-1, excluding m)
            otherIndices = [i | i <- [0 .. n-1], i /= m]

            -- Construct the list of ObjDeBr arguments for the Tupl constructor
            -- inside the logical formula. Uses X i for placeholder elements,
            -- except at position m, where it uses X resultIdx.
            -- Result: [X 0, ..., X (m-1), X n, X (m+1), ..., X (n-1)]
            tuplArgs :: [ObjDeBr]
            tuplArgs = [ if i == m then X resultIdx else X i | i <- [0 .. n-1] ]

            -- Construct the core equality predicate: X_t == Tupl(...)
            -- This compares the placeholder for the input tuple 't' (X tupleIdx)
            -- with the tuple constructed from the template variables.
            equalityBody :: PropDeBr
            equalityBody = X tupleIdx :==: tuple tuplArgs -- Assumes Tupl constructor exists

            -- Construct the existentially quantified body using the multiEx helper:
            -- Exists X0 ... Exists X(m-1) Exists X(m+1) ... Exists X(n-1) ( equalityBody )
            quantifiedBody :: PropDeBr
            quantifiedBody = multiEx otherIndices equalityBody -- Assumes multiEx helper exists

            -- Construct the Hilbert expression template: hXn ( quantifiedBody )
            -- This defines the result 'r' (represented by Xn) as the object satisfying
            -- the quantified property.
            hilbertTemplate :: ObjDeBr
            hilbertTemplate = hX resultIdx quantifiedBody

            -- Substitute the actual input tuple 't' for its placeholder X(n+1)
            -- within the generated Hilbert expression template.
            finalExpression :: ObjDeBr
            finalExpression = objDeBrSubX tupleIdx t hilbertTemplate -- Assumes objDeBrSubX exists

        in
            finalExpression








relDomain :: ObjDeBr -> ObjDeBr
relDomain s = objDeBrSubX 0 s (hX 1(aX 2 (X 2 `In` X 1)  -- x ∈ D
                       :<->:                             -- iff
                            eX 3 (pair (X 2) (X 3) `In` X 0)))


-- let us assume that f is a pair
-- of form Pair(t,z) where t is a function in set theory
-- (a set of pairs serving as the function) as conventionally
-- understood, and z is the co-domain, being a non-strict
-- superset of the image.
-- Note that this is just a helper function. It doesn't test
-- that f really is a function. It also depends on pairFirst working correctly.
--

tripletLast :: ObjDeBr -> ObjDeBr
tripletLast = project 3 2



(.@.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .@. x = objDeBrSubXs [(0,f),(1,x)] (hX 2 ( pair (X 1) (X 2) `In` tripletLast (X 0) ))

infixl 9 .@.




compositionTemplate :: ObjDeBr
compositionTemplate =
    let
        f_idx = 1; g_idx = 2; h_idx = 99; x_idx = 11
        f_term = X f_idx; g_term = X g_idx; h_term = X h_idx; x_term = X x_idx
        dom_g = project 3 0 g_term
        cod_f = project 3 1 f_term
        funcs_set = funcsSet dom_g cod_f
        prop1 = h_term `In` funcs_set
        prop2 = aX x_idx ( (h_term .@. x_term) :==: (f_term .@. (g_term .@. x_term)) )
    in hX h_idx (prop1 :&&: prop2)

-- Infix operator for composition f .:. g = f o g
-- Substitutes f and g into the compositionTemplate
(.:.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .:. g = --objDeBrSubXs [(1, f), (2, g)] 
  objDeBrSubXs [(1,f),(2,g)] compositionTemplate

infixr 8 .:.



-- | Constructs the Cartesian product A × B.
--   A × B = hX S (isSet(S) ∧ ∀x ∀y ( (x ∈ A ∧ y ∈ B) ↔ <x,y> ∈ S ))
crossProd :: ObjDeBr -> ObjDeBr -> ObjDeBr
crossProd setA setB =
    let
        -- Template indices for placeholders
        a_idx = 0 -- Placeholder for setA
        b_idx = 1 -- Placeholder for setB
        s_idx = 2 -- Placeholder for the product set S (bound by hX)
        x_idx = 3 -- Placeholder for element x (bound by first aX)
        y_idx = 4 -- Placeholder for element y (bound by second aX)

        -- Core membership property: (x ∈ A ∧ y ∈ B) ↔ <x,y> ∈ S
        -- Using X x_idx for x, X y_idx for y, X a_idx for A, X b_idx for B, X s_idx for S
        membership_prop = ((X x_idx `In` X a_idx) :&&: (X y_idx `In` X b_idx))
                          :<->:
                          (pair (X x_idx) (X y_idx) `In` X s_idx)

        -- Universally quantify over x and y: ∀x ∀y (...)
        quantified_membership_prop = aX x_idx (aX y_idx membership_prop)

        -- Condition that S (the product set itself) must be a set: isSet(S)
        condition_S_isSet = isSet (X s_idx)

        -- Combine the conditions for S: isSet(S) ∧ ∀x ∀y (...)
        full_prop_for_S = condition_S_isSet :&&: quantified_membership_prop

        -- Hilbert term: hX S (isSet(S) ∧ ∀x ∀y (...))
        hilbertTemplate = hX s_idx full_prop_for_S

    -- Substitute actual setA and setB into the template
    in objDeBrSubXs [(a_idx, setA), (b_idx, setB)] hilbertTemplate

infixl 6 `crossProd` -- Keeping original infix declaration

-- | Parses an ObjDeBr term to see if it matches the structure generated by 'crossProd'.
-- | Returns Maybe (setA, setB) on success.
-- | Expected structure: hX S (isSet(S) ∧ ∀x ∀y ( (x ∈ A ∧ y ∈ B) ↔ <x,y> ∈ S ))
parseCrossProduct :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseCrossProduct obj = do
    -- 1. Match outer Hilbert: Hilbert p_conj
    --    idx_S is the De Bruijn index for the product set S, bound by hX.
    (p_conj, idx_S) <- parseHilbert obj

    -- 2. Expect p_conj to be a conjunction: isSet_S_prop :&&: forall_xy_prop
    (isSet_S_prop, forall_xy_prop) <- parseConjunction p_conj

    -- 3. Verify isSet_S_prop is isSet(Bound idx_S)
    s_object_from_isSet <- parseIsSet isSet_S_prop
    s_bound_from_isSet <- parseBound s_object_from_isSet
    guard (s_bound_from_isSet == idx_S) -- Check S is the correct Hilbert-bound variable

    -- 4. Match first Forall (binder for 'x') from forall_xy_prop
    --    idx_x is the De Bruijn index for x.
    (forall_y_prop, idx_x) <- parseForall2 forall_xy_prop

    -- 5. Match second Forall (binder for 'y') from forall_y_prop
    --    idx_y is the De Bruijn index for y.
    (bicond_prop, idx_y) <- parseForall2 forall_y_prop

    -- 6. Match Biconditional: lhs_conj_prop :<->: rhs_pair_in_S_prop
    (lhs_conj_prop, rhs_pair_in_S_prop) <- parseBiconditional bicond_prop

    -- 7. Match LHS Conjunction: x_in_A_prop :&&: y_in_B_prop
    (x_in_A_prop, y_in_B_prop) <- parseConjunction lhs_conj_prop

    -- 8. Match x_in_A_prop: (Bound idx_x) `In` setA_cand
    (bound_x_from_lhs, setA_cand) <- parseIn x_in_A_prop
    parsed_idx_x_from_lhs <- parseBound bound_x_from_lhs
    guard (parsed_idx_x_from_lhs == idx_x) -- x matches first aX-bound variable

    -- 9. Match y_in_B_prop: (Bound idx_y) `In` setB_cand
    (bound_y_from_lhs, setB_cand) <- parseIn y_in_B_prop
    parsed_idx_y_from_lhs <- parseBound bound_y_from_lhs
    guard (parsed_idx_y_from_lhs == idx_y) -- y matches second aX-bound variable

    -- 10. Match RHS In: pair_term `In` (Bound idx_S)
    (pair_term, bound_S_from_rhs) <- parseIn rhs_pair_in_S_prop
    parsed_idx_S_from_rhs <- parseBound bound_S_from_rhs
    guard (parsed_idx_S_from_rhs == idx_S) -- S matches hX-bound variable

    -- 11. Match pair_term: pair (Bound idx_x) (Bound idx_y)
    (pair_arg1, pair_arg2) <- parsePair pair_term -- Assuming parsePair extracts from pair
    parsed_idx_x_from_pair <- parseBound pair_arg1
    parsed_idx_y_from_pair <- parseBound pair_arg2
    guard (parsed_idx_x_from_pair == idx_x)
    guard (parsed_idx_y_from_pair == idx_y)

    -- 12. Sanity checks for setA_cand and setB_cand:
    --     They should not capture idx_S, idx_x, or idx_y.
    guard (not (objDeBrBoundVarInside setA_cand idx_S || objDeBrBoundVarInside setA_cand idx_x || objDeBrBoundVarInside setA_cand idx_y))
    guard (not (objDeBrBoundVarInside setB_cand idx_S || objDeBrBoundVarInside setB_cand idx_x || objDeBrBoundVarInside setB_cand idx_y))

    -- 13. If all checks pass, return setA_cand and setB_cand
    return (setA_cand, setB_cand)

isTuple :: Int -> ObjDeBr -> PropDeBr
isTuple i obj = propDeBrSubX i obj $ multiEx idxs 
      (X i :==: tuple [X j | j <- idxs ])
      where idxs = [0 .. i-1]


-- | Constructs the ObjDeBr term representing the binary union of sets A and B.
--   A ∪ B = hX S (isSet(S) ∧ ∀x (x ∈ S ↔ (x ∈ A ∨ x ∈ B)))
(.\/.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
setA .\/. setB =
    let
        setA_idx = 0 -- Placeholder for input setA
        setB_idx = 1 -- Placeholder for input setB
        x_idx    = 2 -- Placeholder for the element variable 'x'
        s_idx    = 3 -- Placeholder for the union set 'S' being defined by hX

        propTemplate = (X x_idx `In` X s_idx) :<->: ((X x_idx `In` X setA_idx) :||: (X x_idx `In` X setB_idx))
        quantifiedProp = aX x_idx propTemplate
        
        condition_S_isSet = isSet (X s_idx) -- Assert that S is a set
        full_prop_for_S = condition_S_isSet :&&: quantifiedProp
        
        hilbertTemplate = hX s_idx full_prop_for_S
    in objDeBrSubXs [(setA_idx, setA), (setB_idx, setB)] hilbertTemplate

infixr 2 .\/. 

-- | Parses an ObjDeBr term to see if it matches the structure generated by 'binaryUnion' (.\/.).
-- | Expected structure: hX S (isSet(S) ∧ ∀x (x ∈ S ↔ (x ∈ A ∨ x ∈ B)))
parseBinaryUnion :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseBinaryUnion obj = do
    (p_conj, idx_S) <- parseHilbert obj
    (isSet_S_prop, forall_x_prop) <- parseConjunction p_conj

    s_object_from_isSet <- parseIsSet isSet_S_prop
    s_bound_from_isSet <- parseBound s_object_from_isSet
    guard (s_bound_from_isSet == idx_S)

    (bicond_prop, idx_x) <- parseForall2 forall_x_prop
    (x_in_S_prop, x_in_A_or_B_prop) <- parseBiconditional bicond_prop

    (bound_x_lhs, bound_S_lhs) <- parseIn x_in_S_prop
    parsed_idx_x_lhs <- parseBound bound_x_lhs
    parsed_idx_S_lhs <- parseBound bound_S_lhs
    guard (parsed_idx_x_lhs == idx_x)
    guard (parsed_idx_S_lhs == idx_S)

    (x_in_A_prop, x_in_B_prop) <- parseDisjunction x_in_A_or_B_prop

    (bound_x_in_A, setA_cand) <- parseIn x_in_A_prop
    parsed_idx_x_in_A <- parseBound bound_x_in_A
    guard (parsed_idx_x_in_A == idx_x)

    (bound_x_in_B, setB_cand) <- parseIn x_in_B_prop
    parsed_idx_x_in_B <- parseBound bound_x_in_B
    guard (parsed_idx_x_in_B == idx_x)

    guard (not (objDeBrBoundVarInside setA_cand idx_S || objDeBrBoundVarInside setA_cand idx_x))
    guard (not (objDeBrBoundVarInside setB_cand idx_S || objDeBrBoundVarInside setB_cand idx_x))
    return (setA_cand, setB_cand)

-- | Constructs the ObjDeBr term representing the binary intersection of sets A and B.
--   A ∩ B = hX S (isSet(S) ∧ ∀x (x ∈ S ↔ (x ∈ A ∧ x ∈ B)))
(./\.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
setA ./\. setB =
    let
        setA_idx = 0; setB_idx = 1; x_idx = 2; s_idx = 3
        propTemplate = (X x_idx `In` X s_idx) :<->: ((X x_idx `In` X setA_idx) :&&: (X x_idx `In` X setB_idx))
        quantifiedProp = aX x_idx propTemplate

        condition_S_isSet = isSet (X s_idx) -- Assert that S is a set
        full_prop_for_S = condition_S_isSet :&&: quantifiedProp
        
        hilbertTemplate = hX s_idx full_prop_for_S
    in objDeBrSubXs [(setA_idx, setA), (setB_idx, setB)] hilbertTemplate

infixr 3 ./\.

-- | Parses an ObjDeBr term to see if it matches the structure generated by '(./\.)'.
-- | Expected structure: hX S (isSet(S) ∧ ∀x (x ∈ S ↔ (x ∈ A ∧ x ∈ B)))
parseIntersectionOp :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseIntersectionOp obj = do
    (p_conj, idx_S) <- parseHilbert obj
    (isSet_S_prop, forall_x_prop) <- parseConjunction p_conj

    s_object_from_isSet <- parseIsSet isSet_S_prop
    s_bound_from_isSet <- parseBound s_object_from_isSet
    guard (s_bound_from_isSet == idx_S)

    (bicond_prop, idx_x) <- parseForall2 forall_x_prop
    (x_in_S_prop, x_in_A_and_B_prop) <- parseBiconditional bicond_prop

    (bound_x_lhs, bound_S_lhs) <- parseIn x_in_S_prop
    parsed_idx_x_lhs <- parseBound bound_x_lhs
    parsed_idx_S_lhs <- parseBound bound_S_lhs
    guard (parsed_idx_x_lhs == idx_x)
    guard (parsed_idx_S_lhs == idx_S)

    (x_in_A_prop, x_in_B_prop) <- parseConjunction x_in_A_and_B_prop -- Changed from parseDisjunction

    (bound_x_in_A, setA_cand) <- parseIn x_in_A_prop
    parsed_idx_x_in_A <- parseBound bound_x_in_A
    guard (parsed_idx_x_in_A == idx_x)

    (bound_x_in_B, setB_cand) <- parseIn x_in_B_prop
    parsed_idx_x_in_B <- parseBound bound_x_in_B
    guard (parsed_idx_x_in_B == idx_x)

    guard (not (objDeBrBoundVarInside setA_cand idx_S || objDeBrBoundVarInside setA_cand idx_x))
    guard (not (objDeBrBoundVarInside setB_cand idx_S || objDeBrBoundVarInside setB_cand idx_x))
    return (setA_cand, setB_cand)




-- | Constructs the ObjDeBr term representing set difference A \ B.
--   Uses the definition: A \ B = {x ∈ A | x ∉ B}
--   Implemented via builderX.
(.\.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
setA .\. setB =
    let
        x_idx = 0 -- Index for the element variable x
        setB_idx = 1 -- Placeholder index for set B

        -- Predicate: x ∉ B (using placeholder)
        predicate = X x_idx `nIn` X setB_idx

        -- Build the set {x ∈ A | predicate}
        builderTemplate = builderX x_idx setA predicate

        -- Substitute the actual set B
    in objDeBrSubX setB_idx setB builderTemplate

infixl 5 .\.

-- | Parses an ObjDeBr term to see if it matches the structure generated by '(.\.)' (set difference).
--   Recognizes the specific builderX pattern: {x ∈ A | x ∉ B}
--   Returns Maybe (setA, setB) on success.
parseSetDifference :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseSetDifference obj = do
    -- 1. Use parseSetBuilder to deconstruct the general {x ∈ A | q(x)} structure
    (setA, q, normed_idx) <- parseSetBuilder obj

    -- 2. Check if the predicate 'q' has the specific form: Bound idx_x `nIn` setB
    (elemVar, setB) <- parseNotIn q -- Check if q is Neg(elemVar `In` setB)
    boundVar <- parseBound elemVar
    guard (boundVar == normed_idx) -- Ensure the element variable matches the builder index

    -- 3. Optional Sanity check: setB should not contain the bound variable idx_x
    --    (This should be guaranteed by parseSetBuilder if implemented carefully, but double check)
    guard (not (objDeBrBoundVarInside setB normed_idx))

    -- 4. If structure matches, return the identified sets A and B
    return (setA, setB)


-- | Constructs the ObjDeBr term representing the power set of A, P(A).
--   Uses the definition: P(A) = hX P (isSet(P) ∧ ∀x (x ∈ P ↔ x ⊆ A))
--   Since x ⊆ A itself implies isSet(x), this is inherently handled.
powerSet :: ObjDeBr -> ObjDeBr
powerSet setA =
    let
        -- Template indices
        setA_idx = 0 -- Placeholder for input setA (becomes XInternal in subset if used directly)
        x_idx    = 1 -- Placeholder for element 'x' (a potential subset, bound by aX)
        p_idx    = 2 -- Placeholder for the power set 'P' itself (bound by hX)

        -- Core property: x ∈ P ↔ x ⊆ A
        -- subset (X x_idx) (X setA_idx) will expand to:
        -- isSet(X x_idx) ∧ (∀z (z ∈ X x_idx → z ∈ X setA_idx))
        element_membership_prop = (X x_idx `In` X p_idx) :<->: subset (X x_idx) (X setA_idx)

        -- Universally quantify over x: ∀x (x ∈ P ↔ x ⊆ A)
        quantified_element_prop = aX x_idx element_membership_prop

        -- Condition that P (the power set itself) must be a set: isSet(P)
        condition_P_isSet = isSet (X p_idx)

        -- Combine the conditions for P: isSet(P) ∧ ∀x(...)
        full_prop_for_P = condition_P_isSet :&&: quantified_element_prop

        -- Hilbert term: hX P (isSet(P) ∧ ∀x P(x, P, A))
        hilbertTemplate = hX p_idx full_prop_for_P

    -- Substitute the actual setA into the template for the X setA_idx placeholder
    in objDeBrSubX setA_idx setA hilbertTemplate


-- | Parses an ObjDeBr term to see if it matches the structure generated by 'powerSet'.
-- | Returns Maybe setA (the original set whose power set is being defined) on success.
-- | Expected structure: hX P (isSet(P) ∧ ∀x (x ∈ P ↔ (x ⊆ A)))
parsePowerSet :: ObjDeBr -> Maybe ObjDeBr
parsePowerSet obj = do
    -- 1. Match outer Hilbert: Hilbert p_conj
    --    idx_P is the De Bruijn index for the power set P, bound by hX.
    (p_conj, idx_P) <- parseHilbert obj

    -- 2. Expect p_conj to be a conjunction: isSet_P_prop :&&: forall_elements_prop
    (isSet_P_prop, forall_elements_prop) <- parseConjunction p_conj

    -- 3. Verify isSet_P_prop is isSet(Bound idx_P)
    p_object_from_isSet <- parseIsSet isSet_P_prop
    p_bound_from_isSet <- parseBound p_object_from_isSet
    guard (p_bound_from_isSet == idx_P) -- Check it's the correct Hilbert-bound variable P

    -- 4. Match the second part of the conjunction: ∀x (biconditional_prop)
    --    idx_x is the De Bruijn index for x (an element of P), bound by aX.
    (biconditional_prop, idx_x) <- parseForall2 forall_elements_prop

    -- 5. Match Biconditional: x_in_P_prop :<->: x_subset_A_prop
    (x_in_P_prop, x_subset_A_prop) <- parseBiconditional biconditional_prop

    -- 6. Check LHS of biconditional: (Bound idx_x) `In` (Bound idx_P)
    (bound_x_lhs, bound_P_lhs) <- parseIn x_in_P_prop
    parsed_idx_x_lhs <- parseBound bound_x_lhs
    parsed_idx_P_lhs <- parseBound bound_P_lhs
    guard (parsed_idx_x_lhs == idx_x) -- x matches aX-bound variable
    guard (parsed_idx_P_lhs == idx_P) -- P matches hX-bound variable

    -- 7. Parse the RHS of biconditional (x_subset_A_prop) using `parseSubset`.
    --    `parseSubset` expects `isSet(element_x) ∧ ∀z (z ∈ element_x → z ∈ setA_cand)`.
    --    It should return `(element_x, setA_cand)`.
    (subset_element_x, setA_cand) <- parseSubset x_subset_A_prop
    
    -- 8. Verify that `subset_element_x` is indeed (Bound idx_x).
    parsed_idx_x_from_subset <- parseBound subset_element_x
    guard (parsed_idx_x_from_subset == idx_x)

    -- 9. Sanity checks for setA_cand:
    --    It should not capture the Hilbert-bound P (idx_P).
    --    It should not capture the universally quantified x (idx_x).
    guard (not (objDeBrBoundVarInside setA_cand idx_P))
    guard (not (objDeBrBoundVarInside setA_cand idx_x))

    -- 10. If all checks pass, return setA_cand
    return setA_cand


-- | Shorthand for Less Than (a < b). Defined as (a ≤ b) ∧ (a ≠ b).
(.<.) :: ObjDeBr -> ObjDeBr -> PropDeBr
a .<. b = (a :<=: b) :&&: (a ./=. b) -- Using :<=: and the existing ./=. shorthand


-- Define the parser function (place it near other PropDeBr parsers like parseSubset, parseStrictSubset):
-- | Parses a PropDeBr to see if it matches the structure for Less Than (a < b),
-- | which is defined as (a <= b) && (a /= b).
parseLessThan :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseLessThan prop = do
    -- 1. Expect top level to be conjunction: (a <= b) :&&: (a /= b)
    (leEqPart, neEqPart) <- parseConjunction prop

    -- 2. Parse the left conjunct: a :<=: b
    (a1, b1) <- parseLTE leEqPart -- Assuming parseLTE exists for :<=:

    -- 3. Parse the right conjunct: a :/:= b (using parseNotEqual)
    (a2, b2) <- parseNotEqual neEqPart -- Assuming parseNotEqual exists for :/:= (or Neg(:==:))

    -- 4. Check that the terms match across both parts
    guard (a1 == a2)
    guard (b1 == b2)

    -- 5. Return the matched terms a and b
    return (a1, b1)



-- Shorthand for the set of Natural Numbers (non-negative integers)
-- N = {x ∈ Z | x ≥ 0}
natSetObj :: ObjDeBr
natSetObj = builderX 0 IntSet predicate_non_negative
  where
    -- Predicate: (Integ 0) <= X 0  (i.e., 0 <= x)
    predicate_non_negative = Integ 0 :<=: X 0

-- Parser for the natSetObj structure.
-- Since natSetObj is a specific constant, we can just check for equality.
parseNatSet :: ObjDeBr -> Maybe ()
parseNatSet obj = guard (obj == natSetObj) 