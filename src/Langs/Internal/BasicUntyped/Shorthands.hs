{-# LANGUAGE LambdaCase #-}
module Langs.Internal.BasicUntyped.Shorthands (
    eXBang,
    (./=.),
    builderX,
    nIn,
    subset,
    strictSubset,
    boundDepthObjDeBr,
    boundDepthPropDeBr,
    notSubset,
    pairFirst,
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
    parseIntersectionOp

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
import qualified RuleSets.PropLogic as PL
import qualified RuleSets.PredLogic as PREDL
import qualified RuleSets.ZFC as ZFC
import RuleSets.PropLogic (LogicSent(parseIff))
import RuleSets.ZFC (emptySetAxiom, specification,parseMemberOf,memberOf)
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS )
import Text.XHtml (sub)
import qualified Internal.StdPattern
import Data.Maybe (isJust)

import Data.Text (Text, pack, unpack,concat, lines,intercalate)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )



parsePairFirstExp :: ObjDeBr -> Maybe ObjDeBr
parsePairFirstExp subexp = do
    (i,tupleObj) <- parseProjectHilbert subexp
    guard (i==0)
    return tupleObj



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

    -- 3. Match the tuple structure: Tupl [ arg_term, result_var ]
    args <- parseTupl tuple_term
    guard (length args == 2)
    let arg_term = head args        -- Potential argument 'x'
    let result_var = args !! 1     -- Potential bound variable 'y'

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





-- | Parses an ObjDeBr term to see if it matches the specific structure
--   generated for set builder notation: { x_a ∈ t | q(x_a) }
--   which internally might look like: Hilbert (Forall (Bound a In Bound b :<->: q :&&: Bound c In t))
--   Returns Maybe (SourceSet, Predicate, NormalizationDepth) on success.
parseSetBuilder :: ObjDeBr -> Maybe (ObjDeBr, PropDeBr, Int)
parseSetBuilder obj = do

    -- 1. Ensure the outermost term is a Hilbert term.
    --    Extract the inner proposition (forallProp) and the depth associated
    --    with the Hilbert binder (norm_h). This corresponds to index 'b'.
    (forallProp, norm_h) <- parseHilbert obj

    -- 2. Ensure the proposition inside the Hilbert is a Forall quantifier.
    --    Extract the body of the Forall (innerProp) and the depth associated
    --    with the Forall binder (norm_f). This corresponds to indices 'a' and 'c'.
    (innerProp, norm_f) <- parseForall2 forallProp

    -- 3. Ensure the body of the Forall is a Biconditional (<->).
    --    Split into the left-hand side (lhs: element inclusion) and
    --    right-hand side (rhs: predicate and source set check).
    (lhs, rhs) <- parseBiconditional innerProp

    -- 4. Parse the LHS, expecting 'Bound a `In` Bound b'.
    (bound_a_obj, bound_b_obj) <-parseIn lhs
    a <- parseBound bound_a_obj -- Extract index 'a'
    -- Guard: Check that index 'a' matches the inner binding depth 'norm_f'.
    guard (a == norm_f)

    b <- parseBound bound_b_obj -- Extract index 'b'
    -- Guard: Check that index 'b' matches the outer binding depth 'norm_h'.
    guard (b == norm_h)

    -- 5. Parse the RHS, expecting 'q :&&: (Bound c `In` t)'.
    (q, in_c_t) <- parseConjunction rhs -- Extract predicate 'q' and the 'In' expression.

    -- Guard: Ensure the predicate 'q' does not capture the outer bound variable 'b'.
    guard (not (propDeBrBoundVarInside q norm_h))

    -- 6. Parse the second part of the conjunction, expecting 'Bound c `In` t'.
    (bound_c_obj, t) <-parseIn in_c_t -- Extract 'Bound c' and the source set 't'.
    c <- parseBound bound_c_obj -- Extract index 'c'.
    -- Guard: Check that index 'c' matches the inner binding depth 'norm_f' (it must equal 'a').
    guard (c == norm_f)

    -- Guard: Ensure the source set 't' does not capture the outer bound variable 'b'.
    guard (not (objDeBrBoundVarInside t norm_h))
    -- Guard: Ensure the source set 't' does not capture the inner bound variable 'a'/'c'.
    guard (not (objDeBrBoundVarInside t norm_f))

    -- 7. If all parsing steps and guards succeed, return the extracted
    --    source set 't', the predicate 'q', and the inner normalization depth 'norm_f'.
    return (t, q, norm_f)



parseHilbertShort :: ObjDeBr -> Map PropDeBr [Int] -> Maybe [Int]
parseHilbertShort subexp dict = 
    case subexp of
        Hilbert p ->
            Just =<< Data.Map.lookup (Exists p) dict 
        _ -> Nothing

parsePair :: ObjDeBr -> Maybe (ObjDeBr,ObjDeBr)
parsePair subexp = do
    list <- parseTupl subexp
    guard (length list == 2)
    return (head list,list!!1)

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
    parsedArgs <- parseTupl rhs
    

    let n = length parsedArgs -- This is the tuple length

    -- == Structural Guards (Removed norm_h == n check) ==
    -- Guard: Ensure number of Exists binders is n-1
    guard (quantifierCount == n - 1)

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





parseCrossProduct :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseCrossProduct obj = do
    -- 1. Match outer Hilbert: Hilbert p'
    --    'bound_idx_S' is the index for the Bound var representing the product set S.
    (p', bound_idx_S) <- parseHilbert obj

    -- 2. Match first Forall (binder for 'x')
    (prop1, idx_x) <- parseForall2 p'

    -- 3. Match second Forall (binder for 'y')
    (bicond, idx_y) <- parseForall2 prop1

    -- 4. Match Biconditional: lhs :<->: rhs
    (lhs, rhs) <- parseBiconditional bicond

    -- 5. Match LHS Conjunction: conj1 :&&: conj2
    (conj1, conj2) <- parseConjunction lhs

    -- 6. Match first conjunct: bound_x `In` set_A
    (bound_x_lhs, set_A) <- parseIn conj1
    bound_x_idx_lhs <- parseBound bound_x_lhs
    guard (bound_x_idx_lhs == idx_x) -- Check index matches 'x' binder

    -- 7. Match second conjunct: bound_y `In` set_B
    (bound_y_lhs, set_B) <- parseIn conj2
    bound_y_idx_lhs <- parseBound bound_y_lhs
    guard (bound_y_idx_lhs == idx_y) -- Check index matches 'y' binder

    -- 8. Match RHS In: pair_term `In` bound_S_rhs
    (pair_term, bound_S_rhs) <- parseIn rhs

    -- 9. Match pair tuple: Tupl [bound_x_rhs, bound_y_rhs]
    pair_args <- parseTupl pair_term
    guard (length pair_args == 2)
    let bound_x_rhs = head pair_args
    let bound_y_rhs = pair_args !! 1

    -- 10. Check indices within the pair tuple match binders 'x' and 'y'
    bound_x_idx_rhs <- parseBound bound_x_rhs
    bound_y_idx_rhs <- parseBound bound_y_rhs
    guard (bound_x_idx_rhs == idx_x)
    guard (bound_y_idx_rhs == idx_y)

    -- 11. Check the set on the RHS is the Bound variable for the product set S
    bound_S_idx_rhs <- parseBound bound_S_rhs
    guard (bound_S_idx_rhs == bound_idx_S)

    -- Optional: Sanity checks for variable capture
    guard (not (objDeBrBoundVarInside set_A idx_x || objDeBrBoundVarInside set_A idx_y || objDeBrBoundVarInside set_A bound_idx_S))
    guard (not (objDeBrBoundVarInside set_B idx_x || objDeBrBoundVarInside set_B idx_y || objDeBrBoundVarInside set_B bound_idx_S))

    -- 12. If all checks pass, return the extracted original ObjDeBr terms for set A and set B
    return (set_A, set_B)


parseIsTupleApp :: PropDeBr -> Maybe (Int, ObjDeBr)
parseIsTupleApp prop = do
    -- 1. Parse the chain of Exists quantifiers.
    (equalityBody, n, base_depth) <- parseExistsChain prop -- Returns (body, count, depth)

    -- 2. Parse the innermost body as an equality: term' == tuple_term
    (term', tuple_term) <- parseEqual equalityBody

    -- 3. Parse the RHS of the equality as a tuple: Tupl [arg_0, ..., arg_n_1]
    args <- parseTupl tuple_term
    guard (length args == n) -- Check if tuple length matches quantifier count

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


-- Parses a proposition 'prop' to see if it matches the structure
-- created by 'isFunc f setA setB'. Extracts Just (f, setA, setB) on success.
parseIsFunc :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr, ObjDeBr)
parseIsFunc prop = do
    -- 1. Get all conjuncts
    let conjuncts = getAllConjuncts prop

    -- 2. Find the domain equality: (project 3 0 f) == setA
    let findDomEq conjunct = do
            (lhs, targetSetA) <- parseEqual conjunct
            (idx, f1)         <- parseProjectHilbert lhs
            guard (idx == 0)
            return (f1, targetSetA) -- Result is Maybe (ObjDeBr, ObjDeBr)
    -- Use '<-' to unwrap the Maybe and bind the tuple to maybe_f_A

    maybe_f_A <- find (isJust . findDomEq) conjuncts >>= findDomEq

    -- 3. Find the codomain equality: (project 3 1 f) == setB
    let findCodEq conjunct = do
            (lhs, targetSetB) <- parseEqual conjunct
            (idx, f2)         <- parseProjectHilbert lhs
            guard (idx == 1)
            return (f2, targetSetB) -- Result is Maybe (ObjDeBr, ObjDeBr)
    -- Use '<-' to unwrap the Maybe and bind the tuple to maybe_f_B


    maybe_f_B <- find (isJust . findCodEq) conjuncts >>= findCodEq

    -- 4. Extract results using 'let' since maybe_f_A and maybe_f_B are now plain tuples
    let (f1, setA) = maybe_f_A
    let (f2, setB) = maybe_f_B

    -- 5. Check that the 'f' extracted from both equalities is the same term
    guard (f1 == f2)
    let funcTerm = f1 -- Use f1 as the definitive function term

    -- 6. Check for the presence and correctness of the isTuple 3 f condition
    let findIsTuple3 conjunct = do
            (tupleSize, termChecked) <- parseIsTupleApp conjunct
            guard (tupleSize == 3)
            return termChecked

    -- Use '<-' to unwrap the Maybe and bind the term to maybe_f_tuple
    maybe_f_tuple <- find (isJust . findIsTuple3) conjuncts >>= findIsTuple3
    -- Check the term from isTuple matches our funcTerm


    guard (maybe_f_tuple == funcTerm)

    -- 7. If all key checks passed, return the extracted f, setA, setB
    return (funcTerm, setA, setB)


-- | Constructs the ObjDeBr term representing the set of functions from A to B.
--   Assumes functions are represented as Tupl[dom, cod, graph].
--   Uses Hilbert operator and the 3-argument isFunc predicate:
--   FUNCS(A,B) = hX S (forall f (f in S <-> isFunc(f, A, B)))
funcsSet :: ObjDeBr -> ObjDeBr -> ObjDeBr
funcsSet setA setB =
    let
        -- Choose distinct indices for template variables
        setA_idx = 0 -- Placeholder for input setA
        setB_idx = 1 -- Placeholder for input setB
        f_idx    = 2 -- Placeholder for the function variable 'f'
        s_idx    = 3 -- Placeholder for the set 'S' being defined by hX

        -- The core property defining membership in the set S:
        -- f ∈ S ↔ isFunc(f, A, B)
        -- where f = X f_idx, S = X s_idx, A = X setA_idx, B = X setB_idx
        propTemplate = (X f_idx `In` X s_idx) :<->: isFunc (X f_idx) (X setA_idx) (X setB_idx)

        -- The quantified property: ∀f ( P(f, S, A, B) )
        quantifiedProp = aX f_idx propTemplate

        -- The Hilbert term template defining S: hX S ( ∀f P(f, S, A, B) )
        hilbertTemplate = hX s_idx quantifiedProp

    -- Substitute the actual setA and setB into the template
    in objDeBrSubXs [(setA_idx, setA), (setB_idx, setB)] hilbertTemplate

parseFuncsSet :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseFuncsSet obj = do
    -- 1. Match outer Hilbert: Hilbert p'
    --    'idx_S' is the index for the Bound variable representing the set S (FUNCS(A,B)).
    (p', idx_S) <- parseHilbert obj -- Changed obj to prop

    -- 2. Match the Forall: Forall prop_f
    --    'idx_f' is the index for the Bound variable representing the function 'f'.
    (prop_f, idx_f) <- parseForall2 p'

    -- 3. Match the Biconditional: f_in_S :<->: isFunc_call_prop
    (f_in_S, isFunc_call_prop) <- parseBiconditional prop_f

    -- 4. Check LHS: bound_f_lhs `In` bound_S_lhs
    (bound_f_lhs, bound_S_lhs) <- parseIn f_in_S
    bound_f_idx_lhs <- parseBound bound_f_lhs
    bound_S_idx_lhs <- parseBound bound_S_lhs
    guard (bound_f_idx_lhs == idx_f) -- Check 'f' index matches Forall binder
    guard (bound_S_idx_lhs == idx_S) -- Check 'S' index matches Hilbert binder

    -- 5. Parse the RHS using the 'parseIsFunc' helper.
    --    This should extract the function term, domain set, and codomain set
    --    as they appear inside the isFunc(...) proposition.

    (funcTerm_from_isFunc, setA, setB) <- parseIsFunc isFunc_call_prop



    -- 6. Verify that the function term extracted by parseIsFunc is indeed
    --    the Bound variable bound by the Forall quantifier.
    bound_f_idx_rhs <- parseBound funcTerm_from_isFunc
    guard (bound_f_idx_rhs == idx_f)

    -- 7. Optional: Sanity checks for variable capture in setA and setB.
    guard (not (objDeBrBoundVarInside setA idx_f || objDeBrBoundVarInside setA idx_S))
    guard (not (objDeBrBoundVarInside setB idx_f || objDeBrBoundVarInside setB idx_S))

    -- 8. If all checks pass, return Just (setA, setB)
    return (setA, setB)




        
parseNotIn :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseNotIn p = case p of
    Neg (a `In` b) -> Just (a, b)
    _ -> Nothing


-- Negation Shorthands & Default
parseNotEqual :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseNotEqual p = case p of
    Neg (a :==: b) -> Just (a, b)
    _ -> Nothing


parseSubset :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseSubset p = do
    (imp, norm1) <- parseForall2 p
    (xInA,xInB) <- parseImplication imp
    (x,a) <-parseIn xInA
    xIdx <- parseBound x
    guard (xIdx == norm1)
    guard (not (objDeBrBoundVarInside a norm1))
    (x,b) <-parseIn xInB
    xIdx <- parseBound x
    guard (xIdx == norm1)
    guard (not (objDeBrBoundVarInside b norm1))
    return (a,b)


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
     Tupl xs ->
         -- Apply the decrement recursively to each element in the list
         Tupl $ Prelude.map (boundDecrementObjDeBr idx) xs





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
    (:>=:) o1 o2 -> (:>=:) (boundDecrementObjDeBr idx o1) (boundDecrementObjDeBr idx o2)
    F -> F






isPair :: ObjDeBr -> PropDeBr
isPair = isTuple 2



--isPair t = propDeBrSubX 2 t $  eX 0 $ eX 1 $ X 2 :==: Tupl [X 0,X 1]





isRelation :: ObjDeBr -> PropDeBr
isRelation s = aX 0 $ X 0 `In` s :->: isPair (X 0)


isFunction :: ObjDeBr -> PropDeBr
isFunction t = isRelation t :&&: 
          aX 0 ( X 0 `In` relDomain t :->: eXBang 1 $ Tupl [X 0, X 1] `In` t)

--propIsFuncOnSet :: ObjDeBr -> PropDeBr -> PropDeBr
--propIsFuncOnSet t p = 


--(isRelation (X 0) :&&: 
--                            (aX 1 $ (X 1) `In` relDomain (X 0) :->: eBangX 2 



builderX :: Int -> ObjDeBr -> PropDeBr -> ObjDeBr
-- t is the source set term.
-- p is the predicate template, expected to use X idx as its placeholder
--   for the variable being bound by the set builder.
-- This version uses XInternal 1 and XInternal 2 internally.
builderX idx t p =
    -- Substitute the source set 't' for the internal placeholder 'XInternal 2'
    objDeBrSubXInt 2 t $
    -- Create a Hilbert term binding the internal placeholder 'XInternal 1'
    -- (which represents the set being defined)
    hXInt 1 $
    -- Create a Universal quantifier binding the user's template variable 'X idx'
    -- (which represents the element being tested)
    aX idx $
        -- The core predicate defining the set membership:
        -- (x ∈ y) ↔ (P(x) ∧ x ∈ t)
        -- where x is (X idx), y is (XInternal 1), t is (XInternal 2)
        (X idx `In` XInternal 1) :<->: (p :&&: (X idx `In` XInternal 2))



subset :: ObjDeBr -> ObjDeBr -> PropDeBr
subset a b = propDeBrSubXs [(1,a),(0,b)] 
          (aX 2 (X 2 `In` X 1 :->: X 2 `In` X 0))


strictSubset :: ObjDeBr -> ObjDeBr -> PropDeBr
strictSubset a b = subset a b :&&: Neg (a :==: b)

notSubset :: ObjDeBr -> ObjDeBr -> PropDeBr
notSubset a b = Neg (subset a b)

-- | Generates an ObjDeBr term representing the projection of the m-th element
-- | from an n-tuple t. Uses a Hilbert expression internally.
-- | project n m t = "the element r such that there exist y0..y(m-1),y(m+1)..y(n-1)
-- |                where t = Tupl [y0, ..., y(m-1), r, y(m+1), ..., y(n-1)]"
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
            equalityBody = X tupleIdx :==: Tupl tuplArgs -- Assumes Tupl constructor exists

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


-- | Predicate: Checks if an ObjDeBr term 'f' represents a function
--   structured as Tupl [dom, cod, graph], AND that its declared
--   domain is equal to 'setA' and its declared codomain is equal to 'setB'.
isFunc :: ObjDeBr -> ObjDeBr -> ObjDeBr -> PropDeBr
isFunc f setA setB =
    -- Condition 1: f must be a 3-tuple
    isTuple 3 f :&&:
    let
        -- Condition 2: Extract components from the triple f
        -- These are terms within the logical formula being built.
        dom   = project 3 0 f
        cod   = project 3 1 f
        graph = project 3 2 f

        -- Condition 3: Declared domain in f must equal the provided setA
        cond3 = (dom :==: setA)

        -- Condition 4: Declared codomain in f must equal the provided setB
        cond4 = (cod :==: setB)

        -- Condition 5: The 'graph' component must be a relation (set of pairs)
        cond5 = isRelation graph

        -- Condition 6: The 'graph' must be a subset of the Cartesian product
        --              of the triple's declared domain and codomain.
        --              This checks internal consistency of the triple.
        prodDomCod =  crossProd dom cod
        cond6 = subset graph prodDomCod

        -- Condition 7: Functionality property over the declared domain 'dom'.
        --              Forall x (x In dom -> Exists! y (<x,y> In graph))
        --              Ensures each element in the declared domain maps to exactly one element.
        cond7 = aX 0 ( (X 0 `In` dom) :->: eXBang 1 (Tupl [X 0, X 1] `In` graph) )

    -- Combine all conditions using logical AND
    in
        cond3 :&&: cond4 :&&: cond5 :&&: cond6 :&&: cond7




pairFirst :: ObjDeBr -> ObjDeBr
pairFirst = project 2 0




--pairFirst :: ObjDeBr -> ObjDeBr
--pairFirst pair = objDeBrSubX 0 pair (hX 2 (eX 1 (X 0 :==: Tupl [X 2,X 1])))


relDomain :: ObjDeBr -> ObjDeBr
relDomain s = objDeBrSubX 0 s (hX 1(aX 2 (X 2 `In` X 1)  -- x ∈ D
                       :<->:                             -- iff
                            eX 3 (Tupl [X 2, X 3] `In` X 0)))


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
f .@. x = objDeBrSubXs [(0,f),(1,x)] (hX 2 ( Tupl [X 1, X 2] `In` tripletLast (X 0) ))

--f .@. x = objDeBrSubXs [(0, project 3 2 f), (1, x)] (hX 2 ( Tupl [X 1, X 2] `In` X 0 ))

--f .@. x = objDeBrSubXs [(0,f),(1,x)] 




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

infixr 9 .:. -- Same precedence and associativity as Haskell's .


-- Infix operator for composition f .:. g = f o g
-- Substitutes f and g into the compositionTemplate
(.:.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .:. g = --objDeBrSubXs [(1, f), (2, g)] 
  objDeBrSubXs [(1,f),(2,g)] compositionTemplate




crossProd :: ObjDeBr -> ObjDeBr -> ObjDeBr
crossProd a b = objDeBrSubXs [(0,a),(1,b)] (hX 2 (multiAx [3,4]
              (X 3 `In` X 0 :&&: X 4 `In` X 1 :<->:
            Tupl [X 3, X 4] `In` X 2)))


isTuple :: Int -> ObjDeBr -> PropDeBr
isTuple i obj = propDeBrSubX i obj $ multiEx idxs 
      (X i :==: Tupl [X j | j <- idxs ])
      where idxs = [0 .. i-1]



-- | Constructs the ObjDeBr term representing the binary union of sets A and B.
--   A ∪ B = hX S (∀x (x ∈ S ↔ (x ∈ A ∨ x ∈ B)))
(.\/.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
(.\/.) setA setB =
    let
        -- Choose distinct indices for template variables
        setA_idx = 0 -- Placeholder for input setA
        setB_idx = 1 -- Placeholder for input setB
        x_idx    = 2 -- Placeholder for the element variable 'x'
        s_idx    = 3 -- Placeholder for the union set 'S' being defined by hX

        -- The core property defining membership in the set S:
        -- x ∈ S ↔ (x ∈ A ∨ x ∈ B)
        -- where x = X x_idx, S = X s_idx, A = X setA_idx, B = X setB_idx
        propTemplate = (X x_idx `In` X s_idx) :<->: ((X x_idx `In` X setA_idx) :||: (X x_idx `In` X setB_idx))

        -- The quantified property: ∀x P(x, S, A, B)
        quantifiedProp = aX x_idx propTemplate

        -- The Hilbert term template defining S: hX S ( ∀x P(x, S, A, B) )
        hilbertTemplate = hX s_idx quantifiedProp

    -- Substitute the actual setA and setB into the template
    in objDeBrSubXs [(setA_idx, setA), (setB_idx, setB)] hilbertTemplate


-- | Parses an ObjDeBr term to see if it matches the structure generated by 'binaryUnion'.
-- | Returns Maybe (setA, setB) on success.
parseBinaryUnion :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseBinaryUnion obj = do
    -- 1. Match outer Hilbert: Hilbert p'
    --    'idx_S' is the index for the Bound var representing the union set S.
    (p', idx_S) <- parseHilbert obj

    -- 2. Match the Forall: Forall prop_x
    --    'idx_x' is the index for the Bound variable representing the element 'x'.
    (prop_x, idx_x) <- parseForall2 p'

    -- 3. Match the Biconditional: x_in_S :<->: x_in_A_or_B
    (x_in_S, x_in_A_or_B) <- parseBiconditional prop_x

    -- 4. Check LHS: bound_x_lhs `In` bound_S_lhs
    (bound_x_lhs, bound_S_lhs) <- parseIn x_in_S
    bound_x_idx_lhs <- parseBound bound_x_lhs
    bound_S_idx_lhs <- parseBound bound_S_lhs
    guard (bound_x_idx_lhs == idx_x) -- Check 'x' index matches Forall binder
    guard (bound_S_idx_lhs == idx_S) -- Check 'S' index matches Hilbert binder

    -- 5. Parse the RHS Disjunction: x_in_A :||: x_in_B
    (x_in_A, x_in_B) <- parseDisjunction x_in_A_or_B

    -- 6. Parse x_in_A: bound_x_rhs_A `In` setA
    (bound_x_rhs_A, setA) <- parseIn x_in_A
    bound_x_idx_rhs_A <- parseBound bound_x_rhs_A
    guard (bound_x_idx_rhs_A == idx_x) -- Check 'x' index matches Forall binder

    -- 7. Parse x_in_B: bound_x_rhs_B `In` setB
    (bound_x_rhs_B, setB) <- parseIn x_in_B
    bound_x_idx_rhs_B <- parseBound bound_x_rhs_B
    guard (bound_x_idx_rhs_B == idx_x) -- Check 'x' index matches Forall binder

    -- 8. Optional: Sanity checks for variable capture in setA and setB.
    guard (not (objDeBrBoundVarInside setA idx_x || objDeBrBoundVarInside setA idx_S))
    guard (not (objDeBrBoundVarInside setB idx_x || objDeBrBoundVarInside setB idx_S))

    -- 9. If all checks pass, return Just (setA, setB)
    return (setA, setB)


    -- | Constructs the ObjDeBr term representing the binary intersection of sets A and B.
--   A ∩ B = hX S (∀x (x ∈ S ↔ (x ∈ A ∧ x ∈ B)))
(./\.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
setA ./\. setB =
    let
        -- Choose distinct indices for template variables
        setA_idx = 0 -- Placeholder for input setA
        setB_idx = 1 -- Placeholder for input setB
        x_idx    = 2 -- Placeholder for the element variable 'x'
        s_idx    = 3 -- Placeholder for the intersection set 'S' being defined by hX

        -- The core property defining membership in the set S:
        -- x ∈ S ↔ (x ∈ A ∧ x ∈ B)
        -- where x = X x_idx, S = X s_idx, A = X setA_idx, B = X setB_idx
        propTemplate = (X x_idx `In` X s_idx) :<->: ((X x_idx `In` X setA_idx) :&&: (X x_idx `In` X setB_idx)) -- Using :&&:

        -- The quantified property: ∀x P(x, S, A, B)
        quantifiedProp = aX x_idx propTemplate

        -- The Hilbert term template defining S: hX S ( ∀x P(x, S, A, B) )
        hilbertTemplate = hX s_idx quantifiedProp

    -- Substitute the actual setA and setB into the template
    in objDeBrSubXs [(setA_idx, setA), (setB_idx, setB)] hilbertTemplate


-- | Parses an ObjDeBr term to see if it matches the structure generated by '(./\.)'.
-- | Returns Maybe (setA, setB) on success.
parseIntersectionOp :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseIntersectionOp obj = do
    -- 1. Match outer Hilbert: Hilbert p'
    (p', idx_S) <- parseHilbert obj

    -- 2. Match the Forall: Forall prop_x
    (prop_x, idx_x) <- parseForall2 p'

    -- 3. Match the Biconditional: x_in_S :<->: x_in_A_and_B
    (x_in_S, x_in_A_and_B) <- parseBiconditional prop_x

    -- 4. Check LHS: bound_x_lhs `In` bound_S_lhs
    (bound_x_lhs, bound_S_lhs) <- parseIn x_in_S
    bound_x_idx_lhs <- parseBound bound_x_lhs
    bound_S_idx_lhs <- parseBound bound_S_lhs
    guard (bound_x_idx_lhs == idx_x)
    guard (bound_S_idx_lhs == idx_S)

    -- 5. Parse the RHS Conjunction: x_in_A :&&: x_in_B  -- Changed from parseDisjunction
    (x_in_A, x_in_B) <- parseConjunction x_in_A_and_B   -- Changed from parseDisjunction

    -- 6. Parse x_in_A: bound_x_rhs_A `In` setA
    (bound_x_rhs_A, setA) <- parseIn x_in_A
    bound_x_idx_rhs_A <- parseBound bound_x_rhs_A
    guard (bound_x_idx_rhs_A == idx_x)

    -- 7. Parse x_in_B: bound_x_rhs_B `In` setB
    (bound_x_rhs_B, setB) <- parseIn x_in_B
    bound_x_idx_rhs_B <- parseBound bound_x_rhs_B
    guard (bound_x_idx_rhs_B == idx_x)

    -- 8. Optional: Sanity checks for variable capture in setA and setB.
    guard (not (objDeBrBoundVarInside setA idx_x || objDeBrBoundVarInside setA idx_S))
    guard (not (objDeBrBoundVarInside setB idx_x || objDeBrBoundVarInside setB idx_S))

    -- 9. If all checks pass, return Just (setA, setB)
    return (setA, setB)