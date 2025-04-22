{-# LANGUAGE PatternGuards #-}
module Langs.BasicUntyped (
    ObjDeBr(Integ,Constant,V,X,Tupl,Hilbert, Bound),
    PropDeBr(Neg,(:&&:),(:||:),(:->:),(:<->:),(:==:),In,(:>=:),F,Exists),
    DeBrSe(..),
    SubexpDeBr(..),
    PrfStdStepPredDeBr,
    PropErrDeBr,
    PropRuleDeBr,
    PredErrDeBr,
    PredRuleDeBr,
    showPropDeBrStepsBase,
    showPropDeBrStepsBaseM,
    eX, hX, aX,
    showProp,
    showObj,
    showPropM,
    showObjM,
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
    parseProjectHilbert

) where
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
import RuleSets.ZFC (emptySetAxiom, specification,parseMemberOf,memberOf)
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS )
import Text.XHtml (sub)
import qualified Internal.StdPattern
import Data.Maybe (isJust)





data PropDeBr where
      Neg :: PropDeBr -> PropDeBr
      (:&&:)  :: PropDeBr -> PropDeBr -> PropDeBr
      (:||:) :: PropDeBr -> PropDeBr -> PropDeBr
      (:->:)  :: PropDeBr -> PropDeBr -> PropDeBr
      (:<->:) :: PropDeBr -> PropDeBr -> PropDeBr
      (:==:) :: ObjDeBr -> ObjDeBr -> PropDeBr
 --     (`In`) :: ObjDeBr -> ObjDeBr -> PropDeBr
      In :: ObjDeBr -> ObjDeBr -> PropDeBr
      Forall :: PropDeBr -> PropDeBr
      Exists :: PropDeBr -> PropDeBr
      (:>=:) :: ObjDeBr -> ObjDeBr -> PropDeBr
      F :: PropDeBr
    deriving (Show, Eq, Ord)


infixr 3 :&&:
infixr 2 :||:
infixr 0 :->:
infixr 0 :<->:
infix  4 :==:
infix  4 `In`
infix  4 :>=:

--inSet :: ObjDeBr -> ObjDeBr -> PropDeBr
--inSet = In

--infix 4 `inSet`

data SubexpParseTree where
    BinaryOp :: Text -> SubexpParseTree -> SubexpParseTree -> SubexpParseTree
    UnaryOp :: Text -> SubexpParseTree ->SubexpParseTree
    Binding :: Text -> SubexpParseTree -> SubexpParseTree
    HilbertShort :: [Int] -> SubexpParseTree
    ParseTreeConst :: Text -> SubexpParseTree
    ParseTreeFreeVar :: Int -> SubexpParseTree
    ParseTreeBoundVar :: Int -> SubexpParseTree
    ParseTreeX :: Int -> SubexpParseTree
    Tuple :: [SubexpParseTree] -> SubexpParseTree
    ParseTreeF :: SubexpParseTree
    ParseTreeInt :: Int -> SubexpParseTree
    Builder :: SubexpParseTree -> SubexpParseTree -> SubexpParseTree
    FuncApp :: SubexpParseTree -> SubexpParseTree -> SubexpParseTree
    TupleProject :: Int -> SubexpParseTree -> SubexpParseTree
    TestText :: Text -> SubexpParseTree



subexpParseTreeBoundDepth :: SubexpParseTree -> Int
subexpParseTreeBoundDepth sub = case sub of
    BinaryOp _ sub1 sub2 -> max (subexpParseTreeBoundDepth sub1) (subexpParseTreeBoundDepth sub2)
    UnaryOp _ sub1 -> subexpParseTreeBoundDepth sub1
    Binding _ sub1 -> 1 + subexpParseTreeBoundDepth sub1
    HilbertShort idxs -> 0
    ParseTreeConst const -> 0
    ParseTreeFreeVar idx -> 0
    ParseTreeBoundVar idx -> 0
    ParseTreeX idx -> 0
    Tuple as -> maximum $ Prelude.map subexpParseTreeBoundDepth as
    ParseTreeF -> 0
    ParseTreeInt _ -> 0
    Builder sub1 sub2 -> 1 + max (subexpParseTreeBoundDepth sub1) (subexpParseTreeBoundDepth sub2)
    FuncApp sub1 sub2 -> max (subexpParseTreeBoundDepth sub1) (subexpParseTreeBoundDepth sub2)
    TupleProject int sub -> subexpParseTreeBoundDepth sub

sbParseTreeNormalize :: Int -> SubexpParseTree -> SubexpParseTree
-- Be ultra-careful with this function. It will probably break indexing if
-- boundVarIdx is greater than than subepParseTreeDepth sub.
sbParseTreeNormalize boundVarIdx sub =
       sbParseTreeNormalize' (subexpParseTreeBoundDepth sub) sub
    where
        sbParseTreeNormalize' :: Int -> SubexpParseTree -> SubexpParseTree
        sbParseTreeNormalize' depth sub = case sub of
            BinaryOp opSymb sub1 sub2 -> BinaryOp opSymb (sbParseTreeNormalize' depth sub1)
                            (sbParseTreeNormalize' depth sub2)
            UnaryOp opSymb sub1 -> UnaryOp opSymb (sbParseTreeNormalize' depth sub1)
            Binding quant sub1 -> Binding quant (sbParseTreeNormalize' depth sub1)
            HilbertShort idxs -> HilbertShort idxs
            ParseTreeConst const -> ParseTreeConst const
            ParseTreeFreeVar idx -> ParseTreeFreeVar idx
            ParseTreeBoundVar idx -> if idx == boundVarIdx then
                                          ParseTreeBoundVar depth
                                        else
                                            ParseTreeBoundVar idx

            Tuple as -> Tuple $ Prelude.map (sbParseTreeNormalize' depth) as
            ParseTreeX idx -> ParseTreeX idx
            ParseTreeF -> ParseTreeF
            ParseTreeInt i -> ParseTreeInt i
            Builder sub1 sub2 -> Builder (sbParseTreeNormalize' depth sub1) (sbParseTreeNormalize' depth sub2)
            FuncApp sub1 sub2 -> FuncApp (sbParseTreeNormalize' depth sub1) (sbParseTreeNormalize' depth sub2)
            TupleProject n obj -> TupleProject n (sbParseTreeNormalize' depth obj)
  

class SubexpDeBr sub where
    toSubexpParseTree :: sub -> Map PropDeBr [Int] -> SubexpParseTree




binaryOpInData :: [(Text,(Associativity,Int))]
binaryOpInData = [("=",(NotAssociative,5)),("→",(RightAssociative,1)),("↔",(RightAssociative,1)),("∈",(NotAssociative,5)),("∧",(RightAssociative,4)),("∨",(RightAssociative,3)),
     ("≥",(NotAssociative,5)),
     ("≠",(NotAssociative,5)),("∉",(NotAssociative,5)),
     ("⊆",(NotAssociative,5)),("⊂",(NotAssociative,5)),("⊈",(NotAssociative,5)), 
     ("∘",(RightAssociative,9)),
     ("×",(NotAssociative,7))
     
     ]


--The Int is it's precedence number.
binaryOpData :: Map Text (Associativity, Int)
binaryOpData = Data.Map.fromList binaryOpInData



objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx = case obj of
    Integ num -> False
    Constant const -> False
    Hilbert p -> propDeBrBoundVarInside p idx
    Bound i -> idx == i
    V i -> False
    X i -> False
    Tupl as -> or $ Prelude.map (\a -> objDeBrBoundVarInside a idx) as





propDeBrHasBoundVar :: PropDeBr -> Int -> Bool
propDeBrHasBoundVar sub idx = case sub of
    Neg p -> propDeBrBoundVarInside p idx
    (:&&:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:||:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:->:)  p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:<->:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:==:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    In o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    Forall p -> propDeBrBoundVarInside p idx
    Exists p -> propDeBrBoundVarInside p idx
    (:>=:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    F -> False




-- Swaps Bound fromIdx to Bound toIdx within a PropDeBr
swapBoundIndexProp :: Int -> Int -> PropDeBr -> PropDeBr
swapBoundIndexProp fromIdx toIdx p = case p of
    Neg q -> Neg (swapBoundIndexProp fromIdx toIdx q)
    (:&&:) p1 p2 -> (:&&:) (swapBoundIndexProp fromIdx toIdx p1) (swapBoundIndexProp fromIdx toIdx p2)
    (:||:) p1 p2 -> (:||:) (swapBoundIndexProp fromIdx toIdx p1) (swapBoundIndexProp fromIdx toIdx p2)
    (:->:) p1 p2 -> (:->:) (swapBoundIndexProp fromIdx toIdx p1) (swapBoundIndexProp fromIdx toIdx p2)
    (:<->:) p1 p2 -> (:<->:) (swapBoundIndexProp fromIdx toIdx p1) (swapBoundIndexProp fromIdx toIdx p2)
    (:==:) o1 o2 -> (:==:) (swapBoundIndexObj fromIdx toIdx o1) (swapBoundIndexObj fromIdx toIdx o2)
    In o1 o2 -> In (swapBoundIndexObj fromIdx toIdx o1) (swapBoundIndexObj fromIdx toIdx o2)
    Forall q -> Forall (swapBoundIndexProp fromIdx toIdx q) -- Recurses under binder
    Exists q -> Exists (swapBoundIndexProp fromIdx toIdx q) -- Recurses under binder
    (:>=:) o1 o2 -> (:>=:) (swapBoundIndexObj fromIdx toIdx o1) (swapBoundIndexObj fromIdx toIdx o2)
    F -> F



-- Swaps Bound fromIdx to Bound toIdx within an ObjDeBr
swapBoundIndexObj :: Int -> Int -> ObjDeBr -> ObjDeBr
swapBoundIndexObj fromIdx toIdx o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapBoundIndexProp fromIdx toIdx p) -- Recurses into Hilbert predicate
    Bound i -> if i == fromIdx then Bound toIdx else Bound i -- *** Perform swap if index matches ***
    V i -> V i             -- Free variables are untouched
    X i -> X i             -- Template variables are untouched
    XInternal i -> XInternal i -- Internal template variables are untouched
    Tupl os -> Tupl $ Prelude.map (swapBoundIndexObj fromIdx toIdx) os 


-- Calculates depth, returning substitutionDepth if X targetIdx is found.
boundDepthObjDeBrX :: Int -> Int -> ObjDeBr -> Int
boundDepthObjDeBrX targetIdx substitutionDepth obj = case obj of
    Integ num -> 0
    Constant name -> 0
    -- Use recursive call to the corresponding Prop version
    Hilbert prop -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth prop
    Bound idx -> 0 -- Bound variables themselves have 0 depth contribution
    V idx -> 0     -- Free variables have 0 depth contribution
    X idx -> if idx == targetIdx then substitutionDepth else 0 -- *** Return substitutionDepth if target X found ***
    XInternal idx -> 0 -- Ignore XInternal in this version
    Tupl xs ->
        -- Calculate the max depth needed by any element in the list xs.
        -- If the list is empty, the depth is 0.
        if null xs then
            0
        else
            -- Recursively find the max depth required by any element
            maximum $ Prelude.map (boundDepthObjDeBrX targetIdx substitutionDepth) xs


-- Calculates depth, returning substitutionDepth if X targetIdx is found.
boundDepthPropDeBrX :: Int -> Int -> PropDeBr -> Int
boundDepthPropDeBrX targetIdx substitutionDepth prop = case prop of
    Neg p -> boundDepthPropDeBrX targetIdx substitutionDepth p
    (:&&:) p1 p2 -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (:||:) p1 p2 -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (:->:) p1 p2 -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (:<->:) p1 p2 -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    -- Use recursive call to the corresponding Obj version
    (:==:) o1 o2 -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    In o1 o2 -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    -- Standard depth increase for binders, using recursive call
    Forall p -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth p
    Exists p -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth p
    -- Use recursive call to the corresponding Obj version
    (:>=:) o1 o2 -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    F -> 0

-- Calculates depth, returning substitutionDepth if XInternal targetIdx is found.
boundDepthObjDeBrXInt :: Int -> Int -> ObjDeBr -> Int
boundDepthObjDeBrXInt targetIdx substitutionDepth obj = case obj of
    Integ num -> 0
    Constant name -> 0
    -- Use recursive call to the corresponding Prop version
    Hilbert prop -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth prop
    Bound idx -> 0
    V idx -> 0
    X idx -> 0 -- Ignore regular X in this version
    XInternal idx -> if idx == targetIdx then substitutionDepth else 0 -- *** Return substitutionDepth if target XInternal found ***
    -- Use recursive calls for pairs
 -- Added Tupl case:
    Tupl xs ->
        -- Calculate the max depth needed by any element in the list xs.
        -- If the list is empty, the depth is 0.
        if null xs then
            0
        else
            -- Recursively find the max depth required by any element using ...XInt
            maximum $ Prelude.map (boundDepthObjDeBrXInt targetIdx substitutionDepth) xs


-- Calculates depth, returning substitutionDepth if XInternal targetIdx is found.
boundDepthPropDeBrXInt :: Int -> Int -> PropDeBr -> Int
boundDepthPropDeBrXInt targetIdx substitutionDepth prop = case prop of
    Neg p -> boundDepthPropDeBrXInt targetIdx substitutionDepth p
    (:&&:) p1 p2 -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (:||:) p1 p2 -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (:->:) p1 p2 -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (:<->:) p1 p2 -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    -- Use recursive call to the corresponding Obj version
    (:==:) o1 o2 -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    In o1 o2 -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    -- Standard depth increase for binders, using recursive call
    Forall p -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth p
    Exists p -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth p
    -- Use recursive call to the corresponding Obj version
    (:>=:) o1 o2 -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    F -> 0



parsePairFirstExp :: ObjDeBr -> Maybe ObjDeBr
parsePairFirstExp subexp = do
    (i,tupleObj) <- parseProjectHilbert subexp
    guard (i==0)
    return tupleObj


parseFuncApplication' :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseFuncApplication' subexp = do
    (p, norm1) <- parseHilbert subexp

    (obj1, obj2) <- parseIn p

    (x, bound_d_obj) <- parsePair obj1

    guard (not (objDeBrBoundVarInside x norm1))

    d <- parseBound bound_d_obj
    guard (d==norm1)
    f <- parsePairFirstExp obj2
    guard (not (objDeBrBoundVarInside f norm1))

    return (f, x)



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
    let arg_term = args !! 0        -- Potential argument 'x'
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
            maybe Nothing Just (Data.Map.lookup (Exists p) dict) 
        _ -> Nothing


parseHilbert :: ObjDeBr -> Maybe (PropDeBr, Int)
parseHilbert subexp =            
  case subexp of 
     Hilbert p
                -> Just $ (p, pDepth)
            where
             pDepth = boundDepthPropDeBr p
     _ -> Nothing
 

parseForall2 :: PropDeBr -> Maybe (PropDeBr, Int)
parseForall2 subexp =            
  case subexp of 
     Forall p
                -> Just $ (p, pDepth)
            where
             pDepth = boundDepthPropDeBr p
     _ -> Nothing


parseInteg :: ObjDeBr -> Maybe Int
parseInteg subexp = case subexp of
    Integ i -> Just i
    _ -> Nothing



parseConst :: ObjDeBr -> Maybe Text
parseConst subexp = case subexp of
    Constant c -> Just c
    _ -> Nothing




parseBound :: ObjDeBr -> Maybe Int
parseBound subexp = case subexp of
    Bound i -> Just i
    _ -> Nothing

parseV :: ObjDeBr -> Maybe Int
parseV subexp = case subexp of
    V i -> Just i
    _ -> Nothing

parseTupl :: ObjDeBr ->  Maybe [ObjDeBr]
parseTupl subexp = case subexp of
    Tupl xs -> Just xs
    _ -> Nothing


parsePair :: ObjDeBr -> Maybe (ObjDeBr,ObjDeBr)
parsePair subexp = do
    list <- parseTupl subexp
    guard (length(list) == 2)
    return (list!!0,list!!1)





parseX :: ObjDeBr -> Maybe Int
parseX subexp = case subexp of
    X i -> Just i
    _ -> Nothing


parseEqual :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseEqual subexp = case subexp of
    (:==:) ls rs -> Just (ls,rs)
    _           -> Nothing

parseComposition' :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseComposition' obj = do
    --not (objDeBrBoundVarInside a1 idx1)
    (inner1, norm1) <- parseHilbert obj
    (inner2, norm2) <- parseForall2 inner1
    (ls,rs) <- parseEqual inner2
    (h,x) <- parseFuncApplication ls
    hIdx <- parseBound h
    guard (hIdx == norm1)
    xIdx <- parseBound x
    guard (xIdx == norm2)
    (f,gAtX) <- parseFuncApplication rs
    guard (not (objDeBrBoundVarInside f norm1))
    guard (not (objDeBrBoundVarInside f norm2))
    (g,x) <- parseFuncApplication gAtX
    xIdx <- parseBound x
    guard (xIdx == norm2)
    guard (not (objDeBrBoundVarInside g norm1))
    guard (not (objDeBrBoundVarInside g norm2))
    return (f,g)

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
    m <- findIndex (\arg -> case arg of Bound b -> b == norm_h; _ -> False) parsedArgs

    -- 6. Verify other arguments and their indices
    let (r_arg_list, other_args) = partition (\arg -> case arg of Bound b -> b == norm_h; _ -> False) parsedArgs
    guard (length r_arg_list == 1)
    guard (length other_args == quantifierCount)

    actualIndices <- mapM parseBound other_args


    let expectedIndices = [d .. d + quantifierCount - 1]
    guard (sort actualIndices == expectedIndices)

    -- == Validation Checks on recovered_t (lhs) ==
    guard (not (objDeBrBoundVarInside recovered_t norm_h))
    guard (all (\idx -> not (objDeBrBoundVarInside recovered_t idx)) expectedIndices)
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
    let bound_x_rhs = pair_args !! 0
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
    allMatch <- sequence $ zipWith checkArgIndexed [0..] args
    guard (all id allMatch) -- This guard is now logically correct.

    -- 5. Optional Sanity Check: Ensure 'term'' doesn't capture binders.
    --    The expected indices are base_depth to base_depth + n - 1
    let boundIndicesRange = [base_depth .. base_depth + n - 1]
    guard (all (\idx -> not (objDeBrBoundVarInside term' idx)) boundIndicesRange)

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



instance SubexpDeBr ObjDeBr where
    toSubexpParseTree :: ObjDeBr -> Map PropDeBr [Int] -> SubexpParseTree
    



    toSubexpParseTree obj dict =
         maybe (error $ "Ubable to parse term " <> show obj <> ". This shouldn't have happened.")
             id fullParse 
      where fullParse =
             parseInteg'
              <|> parseConst'
              <|> parseBound'
              <|> parseV'
              <|> parseX'
              <|> parseTuple'
              <|> parseFuncsSet'
              <|> parseProject'
              <|> parseHilbertShort'
              <|> parseFuncApplication'
              <|> parseCrossProduct'
              <|> parseComposition'
              <|> parseSetBuilder'
              <|> parseHilbert'
       
            parseFuncApplication' =
               do
                (f,x) <- parseFuncApplication obj
                return $ FuncApp (toSubexpParseTree f dict) (toSubexpParseTree x dict)
            parseSetBuilder' = do
               (t,q,norm) <- parseSetBuilder obj
               let qTree = toSubexpParseTree q dict
               return $  Builder (toSubexpParseTree t dict) (sbParseTreeNormalize norm qTree)
            parseHilbertShort' = do
               idx <- parseHilbertShort obj dict
               return $ HilbertShort idx
            parseHilbert' = do
               (inner, norm) <- parseHilbert obj
               let pTree = toSubexpParseTree inner dict
               let normalized = sbParseTreeNormalize norm pTree
               return $ Binding "ε" (sbParseTreeNormalize norm pTree)
            parseConst' = do
               c <- parseConst obj
               return $ ParseTreeConst c
            parseBound' = do
                i <- parseBound obj
                return $ ParseTreeBoundVar i
            parseV' = do
                i <- parseV obj
                return $ ParseTreeFreeVar i
            parseX' = do
                i <- parseX obj
                return $ ParseTreeX i
            parseInteg' = do
                i <- parseInteg obj
                return $ ParseTreeInt i

            parseTuple' = do
               tuple <- parseTupl obj
               return $ Tuple $ Prelude.map (\x -> toSubexpParseTree x dict) tuple
            parseComposition' = do
                (f,g) <- parseComposition obj
                return $ BinaryOp "∘" (toSubexpParseTree f dict) (toSubexpParseTree g dict)
            parseProject' = do
                (i, o) <- parseProjectHilbert obj
                let pTree = toSubexpParseTree o dict
                return $ TupleProject i (pTree)
            parseCrossProduct' = do
                (a,b) <- parseCrossProduct obj
                return $ BinaryOp "×" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
            parseFuncsSet'= do
                (a,b) <- parseFuncsSet obj
                let treeA = toSubexpParseTree a dict
                let treeB = toSubexpParseTree b dict
                return $ FuncApp (ParseTreeConst "𝗙𝗨𝗡𝗖𝗦") (Tuple [treeA, treeB])

boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     Integ num -> 0
     Constant name -> 0
     Hilbert prop -> boundDepthPropDeBr prop + 1
     Bound idx -> 0
     V idx -> 0
     X idx -> 0
     XInternal idx -> 0
     Tupl xs ->
         -- Depth is the maximum depth of any element in the list.
         -- Return 0 for an empty tuple.
         if null xs then
             0
         else
             maximum $ Prelude.map boundDepthObjDeBr xs




boundDepthPropDeBr :: PropDeBr -> Int
boundDepthPropDeBr prop = case prop of
    Neg p -> boundDepthPropDeBr p
    (:&&:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:||:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:->:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (:<->:) p1 p2 -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    In o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    (:==:) o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    Forall p -> boundDepthPropDeBr p + 1
    Exists p -> boundDepthPropDeBr p + 1
    (:>=:) o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    F -> 0


parseConjunction :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
parseConjunction p = case p of
    (a :&&: b) -> Just (a, b)
    _ -> Nothing

parseImplication :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
parseImplication p = case p of
    (a :->: b) -> Just (a,b)
    _ -> Nothing

parseIn :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseIn p = case p of
    (a `In` b) -> Just (a, b)
    _ -> Nothing


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

parseNegation :: PropDeBr -> Maybe PropDeBr
parseNegation p = case p of
    Neg q -> Just q
    _ -> Nothing



parseNotSubset :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseNotSubset p = do
   imp <- parseNegation p
   (a,b) <- parseSubset imp
   return (a,b)

    





parseDisjunction :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
parseDisjunction p = case p of
    (a :||: b) -> Just (a,b)
    _ -> Nothing

parseExists :: PropDeBr -> Maybe (PropDeBr, Int)
parseExists p = case p of
    Exists inner -> Just (inner, boundDepthPropDeBr inner)
    _ -> Nothing

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


parseBiconditional :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
parseBiconditional p = case p of
    (a :<->: b) -> Just (a,b)
    _ -> Nothing


parseGTE :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseGTE p = case p of
    (a :>=: b) -> Just (a, b)
    _ -> Nothing

parseFalsum :: PropDeBr -> Maybe ()
parseFalsum p = case p of
    F -> Just ()
    _ -> Nothing


instance SubexpDeBr PropDeBr where
  toSubexpParseTree :: PropDeBr -> Map PropDeBr [Int] -> SubexpParseTree
  toSubexpParseTree prop dict =
      maybe (error $ "Unable to parse proposition " <> show prop <> ". This shouldn't have happened.")
          id fullParse
    where
      fullParse =
            parseNotEqual'      -- Negation shorthands first
        <|> parseNotIn'
        <|> parseNotSubset'
        <|> parseNegation'      -- Default negation
        <|> parseStrictSubset'  -- Conjunction shorthand first
        <|> parseConjunction'   -- Default conjunction

        <|> parseSubset'        -- Forall shorthand first
        <|> parseForall2'       -- Default forall

        <|> parseExistsUnique'  -- Exists shorthand first
        <|> parseExists'        -- Default exists

        <|> parseDisjunction'   -- Other standard operators
        <|> parseImplication'
        <|> parseBiconditional'
        <|> parseEqual'
        <|> parseIn'
        <|> parseGTE'
        <|> parseFalsum'        -- Falsum


      -- Helper functions using the basic parsers to build the tree
      parseNotEqual' = do
          (o1, o2) <- parseNotEqual prop
          return $ BinaryOp "≠" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)
      parseNotIn' = do
          (o1, o2) <- parseNotIn prop
          return $ BinaryOp "∉" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)
      parseNotSubset' = do
          (a1, a2) <- parseNotSubset prop
          return $ BinaryOp "⊈" (toSubexpParseTree a1 dict) (toSubexpParseTree a2 dict)
      parseNegation' = do
          q <- parseNegation prop
          return $ UnaryOp "¬" (toSubexpParseTree q dict)

      parseStrictSubset' = do
          (a1, a2) <- parseStrictSubset prop
          return $ BinaryOp "⊂" (toSubexpParseTree a1 dict) (toSubexpParseTree a2 dict)
      parseConjunction' = do
          (a, b) <- parseConjunction prop
          return $ BinaryOp "∧" (toSubexpParseTree a dict) (toSubexpParseTree b dict)

      parseSubset' = do
          (a1, a2) <- parseSubset prop
          return $ BinaryOp "⊆" (toSubexpParseTree a1 dict) (toSubexpParseTree a2 dict)
      parseForall2' = do
          (inner, norm) <- parseForall2 prop
          let pTree = toSubexpParseTree inner dict
          return $ Binding "∀" (sbParseTreeNormalize norm pTree)

      parseExistsUnique' = do
          (innerP, norm) <- parseExistsUnique prop
          let pTree = toSubexpParseTree innerP dict
          return $ Binding "∃!" (sbParseTreeNormalize norm pTree)
      parseExists' = do
          (inner, norm) <- parseExists prop
          let pTree = toSubexpParseTree inner dict
          return $ Binding "∃" (sbParseTreeNormalize norm pTree)

      parseDisjunction' = do
          (a, b) <- parseDisjunction prop
          return $ BinaryOp "∨" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseImplication' = do
          (a, b) <- parseImplication prop
          return $ BinaryOp "→" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseBiconditional' = do
          (a, b) <- parseBiconditional prop
          return $ BinaryOp "↔" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseEqual' = do
          (a, b) <- parseEqual prop
          return $ BinaryOp "=" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseIn' = do
          (a, b) <-parseIn prop
          return $ BinaryOp "∈" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseGTE' = do
          (a, b) <- parseGTE prop
          return $ BinaryOp "≥" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseFalsum' = do
          () <- parseFalsum prop
          return $ ParseTreeF






showSubexpParseTree :: SubexpParseTree -> Text
showSubexpParseTree sub = case sub of
    UnaryOp opSymb sub1 ->
           opSymb
        <> case sub1 of
              UnaryOp _ _ -> showSubexpParseTree sub1
              BinaryOp {} -> "(" <>  showSubexpParseTree sub1 <> ")"
              Binding {} -> showSubexpParseTree sub1
              ParseTreeConst const -> showSubexpParseTree sub1
              ParseTreeFreeVar idx -> showSubexpParseTree sub1
              ParseTreeBoundVar idx -> showSubexpParseTree sub1
              HilbertShort idx -> showSubexpParseTree sub1
              Tuple as -> showSubexpParseTree sub1
              ParseTreeF -> showSubexpParseTree sub1
              ParseTreeX idx -> showSubexpParseTree sub1
              ParseTreeInt i -> showSubexpParseTree sub1
              Builder {} -> showSubexpParseTree sub1
              FuncApp {} -> showSubexpParseTree sub1
              TupleProject {} -> showSubexpParseTree sub1
    BinaryOp opSymb sub1 sub2 ->
           case sub1 of
              UnaryOp _ _ -> showSubexpParseTree sub1
              BinaryOp opSymbL _ _ -> 
                 (   
                   if prec opSymb < prec opSymbL
                      || prec opSymb == prec opSymbL 
                          && assoc opSymbL == LeftAssociative && assoc opSymb == LeftAssociative
                    then
                        showSubexpParseTree sub1
                    else
                        "(" <> showSubexpParseTree sub1 <> ")"

                   )
              Binding {} -> showSubexpParseTree sub1
              ParseTreeConst const -> showSubexpParseTree sub1
              ParseTreeFreeVar idx -> showSubexpParseTree sub1
              ParseTreeBoundVar idx -> showSubexpParseTree sub1

              HilbertShort idx -> showSubexpParseTree sub1
              Tuple as -> showSubexpParseTree sub1
              ParseTreeF -> showSubexpParseTree sub1
              ParseTreeX idx -> showSubexpParseTree sub1
              ParseTreeInt i -> showSubexpParseTree sub1
              Builder {} -> showSubexpParseTree sub1
              FuncApp {} -> showSubexpParseTree sub1
              TupleProject {} -> showSubexpParseTree sub1

          <> " " <> opSymb <> " "
          <> case sub2 of
               UnaryOp _ _-> showSubexpParseTree sub2
               BinaryOp opSymbR _ _ -> 
                 (
                  if prec opSymb < prec opSymbR
                      || prec opSymb == prec opSymbR 
                          && assoc opSymbR == RightAssociative && assoc opSymb == RightAssociative
                    then
                        showSubexpParseTree sub2
                    else
                        "(" <> showSubexpParseTree sub2 <> ")"
                   )
               Binding {} -> showSubexpParseTree sub2
               ParseTreeConst const -> showSubexpParseTree sub2
               ParseTreeFreeVar idx -> showSubexpParseTree sub2
               ParseTreeBoundVar idx -> showSubexpParseTree sub2

               HilbertShort idx -> showSubexpParseTree sub2
               Tuple as -> showSubexpParseTree sub2
               ParseTreeF -> showSubexpParseTree sub2
               ParseTreeX idx -> showSubexpParseTree sub2
               ParseTreeInt i -> showSubexpParseTree sub2
               Builder {} -> showSubexpParseTree sub2
               FuncApp {} -> showSubexpParseTree sub2
               TupleProject {} -> showSubexpParseTree sub2


    Binding quant sub1 -> quant <> "𝑥" <> showIndexAsSubscript idx <> "(" <> showSubexpParseTree sub1 <> ")"
        where
            idx = subexpParseTreeBoundDepth sub1 
    ParseTreeConst const -> const
    ParseTreeX idx -> "X" <> showIndexAsSubscript idx
    ParseTreeFreeVar idx -> "𝑣" <> showIndexAsSubscript idx
    ParseTreeBoundVar idx -> "𝑥" <> showIndexAsSubscript idx


    HilbertShort idx -> "ε" <> showHierarchalIdxAsSubscript idx
    Tuple as -> "(" <> Data.Text.concat (intersperse "," $ Prelude.map showSubexpParseTree as ) <> ")"
    ParseTreeF -> "⊥"
    ParseTreeInt i -> pack $ show i
    Builder sub1 sub2 -> "{" 
                             <> "𝑥" <> showIndexAsSubscript idx
                             <> " ∈ "
                             <> showSubexpParseTree sub1 
                             <> " | " 
                             <> showSubexpParseTree sub2
                             <> "}"
          where
            idx = subexpParseTreeBoundDepth sub2
    FuncApp f x -> case f of
        ParseTreeConst c -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        ParseTreeX idx -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        Tuple _ -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        ParseTreeFreeVar idx -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        ParseTreeBoundVar idx -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        HilbertShort _ -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        Builder _ _ -> showSubexpParseTree f <> "(" <> showSubexpParseTree x <> ")"
        _ -> "(" <> showSubexpParseTree f <> ")" <> "(" <> showSubexpParseTree x <> ")"
    TupleProject idx obj -> "𝛑" <> showIndexAsSubscript idx 
                               <> "(" <> showSubexpParseTree obj <> ")"



  where 
    showHierarchalIdxAsSubscript :: [Int] -> Text
    showHierarchalIdxAsSubscript idxs = Data.Text.concat (intersperse "." (Prelude.map showIndexAsSubscript idxs))
    assoc opSymb = fst $ binaryOpData!opSymb
    prec opSymb = snd $ binaryOpData!opSymb


--instance Show ObjDeBr where
--    show :: ObjDeBr -> String
--    show obj = unpack $ showSubexpParseTree $ toSubexpParseTree obj mempty                         


--instance Show PropDeBr where
--    show :: PropDeBr -> String
--    show obj = unpack $ showSubexpParseTree $ toSubexpParseTree obj mempty


showObj :: Map PropDeBr [Int] -> ObjDeBr -> Text
showObj dict obj = showSubexpParseTree $ toSubexpParseTree obj dict



showObjM :: (Monad m, Monoid r, 
             Proof eL r (PrfStdState PropDeBr Text ()) (PrfStdContext ()) [PrfStdStep PropDeBr Text ()] PropDeBr) 
                     => ObjDeBr -> ProofGenTStd () r PropDeBr Text m Text
showObjM obj = 
    do
      state <- getProofState
      let dict = provenSents state
      return $ showObj dict obj
           

showProp :: Map PropDeBr [Int] -> PropDeBr -> Text
showProp dict prop = showSubexpParseTree $ toSubexpParseTree prop dict

showPropM :: (Monad m, Monoid r, 
             Proof eL r (PrfStdState PropDeBr Text ()) (PrfStdContext ()) [PrfStdStep PropDeBr Text ()] PropDeBr) 
                     => PropDeBr -> ProofGenTStd () r PropDeBr Text m Text
showPropM obj = 
    do
      state <- getProofState
      let dict = provenSents state
      return $ showProp dict obj

data ObjDeBr where
    Integ :: Int -> ObjDeBr
    Constant :: Text -> ObjDeBr
    Hilbert :: PropDeBr -> ObjDeBr
    -- The hilbere operator. This constructor is not public facing.
    Bound :: Int -> ObjDeBr
    -- This is a variable which should always be bound to a binding
    -- operator such as a quantifier or a hilbert operator.
    -- In this system, if it's not bound to something, some kind of
    -- error has probably ocurred. Free-floating variables of this type
    -- are *not* considered free variables in a conventional sense.
    -- Perhaps they could be refered to as "erratic bound variables".
    -- This constructor is not public facing.
    V :: Int ->ObjDeBr
    -- This is a free variable in the conventional sense. The index
    -- is meant to match with a type on a stack of free variable types.
    -- Since this module only concerns untyped variables,
    -- this stack will just have members of form (). The index is a position
    -- on the stack. The stack gets a new member pushed to it whenever
    -- a proof by universal generalisation gets initiated. The free variable
    -- is then used to form the generalization.
    X :: Int -> ObjDeBr
    -- This is a template variable. It is used to identify a point of substitution
    -- when a substitution operation occurs.
    XInternal :: Int -> ObjDeBr
    -- This is another kind of template variable. It is needed to stop premature
    -- consumption of template variables in certain cases.
    -- This constructor is not public facing.

    Tupl :: [ObjDeBr] -> ObjDeBr
    deriving (Eq, Ord, Show)









data DeBrSe where
    ObjDeBrSeConstNotDefd :: Text -> DeBrSe
    ObjDeBrBoundVarIdx :: Int -> DeBrSe
    ObjDeBrFreeVarIdx :: Int -> DeBrSe
    ObjDeBrTemplateVarIdx :: Int -> DeBrSe
    ObjDeBrUnconsumedX :: Int -> DeBrSe
   deriving Show






checkSanityObjDeBr :: ObjDeBr -> Int -> Set Int -> Set Text -> Set Int -> Maybe DeBrSe

checkSanityObjDeBr obj varStackHeight tmpltVarIndices constSet boundSet = case obj of
     Integ num -> Nothing
     Constant name -> if name `Set.member` constSet then
                           Nothing
                       else
                           (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> checkSanityPropDeBr prop varStackHeight tmpltVarIndices constSet 
                            (Set.insert (boundDepthPropDeBr prop) boundSet )
     Bound idx -> 
        if idx `Set.member` boundSet then
            Nothing
        else
            (return . ObjDeBrBoundVarIdx) idx
     V idx ->
        if idx >= 0 && idx < varStackHeight then
            Nothing
        else
            (return . ObjDeBrFreeVarIdx) idx
     X idx -> 
        if idx >= 0 && idx `Set.member` tmpltVarIndices then
            Nothing
        else
            (return . ObjDeBrTemplateVarIdx) idx
     Tupl xs ->
         -- Check sanity of all elements recursively.
         -- Use msum (or asum) to return the *first* error found, or Nothing if all are sane.
         msum $ Prelude.map (\x -> checkSanityObjDeBr x varStackHeight tmpltVarIndices constSet boundSet) xs
  


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



checkSanityPropDeBr :: PropDeBr -> Int -> Set Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityPropDeBr prop freevarStackHeight tmpltVarIndices consts boundVars = 
      case prop of
        Neg p -> checkSanityPropDeBr p freevarStackHeight tmpltVarIndices consts boundVars
        (:&&:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        (:||:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        (:->:)  p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        (:<->:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        In o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars
        (:==:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars
        Forall prop -> checkSanityPropDeBr prop freevarStackHeight tmpltVarIndices consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        Exists prop -> checkSanityPropDeBr prop freevarStackHeight tmpltVarIndices consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        (:>=:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars
        F -> Nothing



instance TypeableTerm ObjDeBr Text () DeBrSe where
 
     getTypeTerm :: Map Int () -> [()] -> Map Text () -> ObjDeBr -> Either DeBrSe ()
     getTypeTerm ts vs constDict term = 
         maybe (return ()) throwError (checkSanityObjDeBr term (Prelude.length vs) 
                        (Data.Map.keysSet ts) (keysSet constDict) mempty)
     const2Term :: Text -> ObjDeBr
     const2Term = Constant
     free2Term :: Int -> ObjDeBr
     free2Term = V


instance TypedSent  Text () DeBrSe PropDeBr where
    checkSanity :: Map Int () -> [()] -> Map Text () -> PropDeBr -> Maybe DeBrSe
    checkSanity tsTypes freeVarStack constDict prop = checkSanityPropDeBr
        prop (Prelude.length freeVarStack) 
        (Data.Map.keysSet tsTypes)  (keysSet constDict) mempty



instance PL.LogicSent PropDeBr () where
  
  (.&&.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.&&.) = (:&&:)

  parseAdj :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseAdj p = case p of
                 (:&&:) p1 p2 -> Just (p1,p2) 
                 _ -> Nothing

  (.->.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.->.) = (:->:)

  parse_implication :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parse_implication p = case p of
                 (:->:) p1 p2 -> Just (p1,p2) 
                 _ -> Nothing


  neg :: PropDeBr -> PropDeBr
  neg = Neg

  parseNeg :: PropDeBr -> Maybe PropDeBr
  parseNeg p = case p of
    Neg p1 -> Just p1
    _ -> Nothing

  (.||.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.||.) = (:||:)
  parseDisj :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseDisj p = case p of
                 (:||:) p1 p2 -> Just(p1,p2)
                 _ -> Nothing
  false :: PropDeBr
  false = F
  (.<->.) :: PropDeBr -> PropDeBr -> PropDeBr
  (.<->.) = (:<->:)
  parseIff  :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseIff p = case p of
                (:<->:) p1 p2 -> Just(p1,p2)
                _ -> Nothing
   


propDeBrBoundVarInside :: PropDeBr -> Int -> Bool
propDeBrBoundVarInside prop idx = case prop of
    Neg p -> propDeBrBoundVarInside p idx
    (:&&:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:||:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:->:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:<->:) p1 p2 -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (:==:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    In o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    Forall p -> propDeBrBoundVarInside p idx
    Exists p -> propDeBrBoundVarInside p idx
    (:>=:) o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    F -> False



objDeBrXInside :: Int -> ObjDeBr -> Bool
objDeBrXInside subidx obj =
    case obj of
        Integ num -> False
        Constant const -> False
        Hilbert p -> propDeBrXInside subidx p
        Bound i -> False
        V i -> False
        X idx | idx == subidx -> True
              | otherwise -> False
        XInternal idx -> False
        Tupl xs ->
            -- True if X subidx is inside ANY element of the list xs
            any (objDeBrXInside subidx) xs
            -- Alternatively: or $ map (objDeBrXInside subidx) xs

objDeBrXInsideInt :: Int -> ObjDeBr -> Bool
objDeBrXInsideInt subidx obj =
    case obj of
        Integ num -> False
        Constant const -> False
        Hilbert p -> propDeBrXInsideInt subidx p
        Bound i -> False
        V i -> False
        XInternal idx | idx == subidx -> True
              | otherwise -> False
        X idx -> False
        Tupl xs ->
            -- True if XInternal subidx is inside ANY element of the list xs
            any (objDeBrXInsideInt subidx) xs
            -- Alternatively: or $ map (objDeBrXInsideInt subidx) xs






propDeBrXInside :: Int -> PropDeBr -> Bool
propDeBrXInside subidx prop = case prop of
    Neg p -> propDeBrXInside subidx p
    (:&&:) p1 p2 -> propDeBrXInside subidx p1 || propDeBrXInside subidx p2
    (:||:) p1 p2 -> propDeBrXInside subidx p1 || propDeBrXInside subidx p2
    (:->:) p1 p2 -> propDeBrXInside subidx p1 || propDeBrXInside subidx p2
    (:<->:) p1 p2 -> propDeBrXInside subidx p1 || propDeBrXInside subidx p2
    (:==:) o1 o2 -> objDeBrXInside subidx o1  || objDeBrXInside subidx o2
    In o1 o2 -> objDeBrXInside subidx o1 || objDeBrXInside subidx o2
    Forall p -> propDeBrXInside subidx p
    Exists p -> propDeBrXInside subidx p
    (:>=:) o1 o2 -> objDeBrXInside subidx o1 || objDeBrXInside subidx o2
    F -> False

propDeBrXInsideInt :: Int -> PropDeBr -> Bool
propDeBrXInsideInt subidx prop = case prop of
    Neg p -> propDeBrXInsideInt subidx p
    (:&&:) p1 p2 -> propDeBrXInsideInt subidx p1 || propDeBrXInsideInt subidx p2
    (:||:) p1 p2 -> propDeBrXInsideInt subidx p1 || propDeBrXInsideInt subidx p2
    (:->:) p1 p2 -> propDeBrXInsideInt subidx p1 || propDeBrXInsideInt subidx p2
    (:<->:) p1 p2 -> propDeBrXInsideInt subidx p1 || propDeBrXInsideInt subidx p2
    (:==:) o1 o2 -> objDeBrXInsideInt subidx o1  || objDeBrXInsideInt subidx o2
    In o1 o2 -> objDeBrXInsideInt subidx o1 || objDeBrXInsideInt subidx o2
    Forall p -> propDeBrXInsideInt subidx p
    Exists p -> propDeBrXInsideInt subidx p
    (:>=:) o1 o2 -> objDeBrXInsideInt subidx o1 || objDeBrXInsideInt subidx o2
    F -> False



-- targetIdx is the index of an internal template variable.
-- substition is the term that the template variable will be substituted for
-- template is the template containing the template variable.
objDeBrSubXInt :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubXInt targetIdx substitution template = case template of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> 
        Hilbert $ propDeBrSubXInt targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        newBoundDepth = boundDepthPropDeBrXInt boundDepth subBoundDepth p
        subBoundDepth = boundDepthObjDeBr substitution 
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p   
    Bound idx -> Bound idx
    V idx -> V idx
    XInternal idx 
        | idx == targetIdx -> substitution
        | otherwise -> XInternal idx
    X idx -> X idx
    Tupl xs ->
        -- Apply the substitution recursively to each element in the list
        Tupl $ Prelude.map (objDeBrSubXInt targetIdx substitution) xs





-- targetIdx is the index of an intnernal template variable.
-- substition is the term that the template variable will be substituted for
-- template is the template containing the template variable.
propDeBrSubXInt :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubXInt targetIdx substitution template = case template of
    Neg p -> Neg $ propDeBrSubXInt targetIdx substitution p
    (:&&:) p1 p2 -> propDeBrSubXInt targetIdx substitution p1 :&&: 
                propDeBrSubXInt targetIdx substitution p2
    (:||:) p1 p2 ->  propDeBrSubXInt targetIdx substitution p1 :||: 
                propDeBrSubXInt targetIdx substitution p2
    (:->:) p1 p2 -> propDeBrSubXInt targetIdx substitution p1 :->: 
                propDeBrSubXInt targetIdx substitution p2
    (:<->:) p1 p2 -> propDeBrSubXInt targetIdx substitution p1 :<->: 
                propDeBrSubXInt targetIdx substitution p2

    (:==:) o1 o2 ->  objDeBrSubXInt targetIdx substitution o1 :==: 
                objDeBrSubXInt targetIdx substitution o2
    In o1 o2 -> objDeBrSubXInt targetIdx substitution o1 `In`
                objDeBrSubXInt targetIdx substitution o2
    Forall p -> Forall $ propDeBrSubXInt targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        newBoundDepth = boundDepthPropDeBrXInt boundDepth subBoundDepth p
        subBoundDepth = boundDepthObjDeBr substitution 
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p  
    Exists p -> Exists $ propDeBrSubXInt targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        newBoundDepth = boundDepthPropDeBrXInt boundDepth subBoundDepth p
        subBoundDepth = boundDepthObjDeBr substitution 
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p  
    (:>=:) o1 o2 -> objDeBrSubXInt targetIdx substitution o1 :>=:
                objDeBrSubXInt targetIdx substitution o2
    F -> F



-- Substitutes X targetIdx with substitution in an ObjDeBr.
-- Directly parallels the user's provided objDeBrSubXInt logic.
-- WARNING: Logic under Hilbert (and Forall/Exists in propDeBrSubX)
-- may differ from standard capture-avoiding substitution.
objDeBrSubX :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubX targetIdx substitution template = case template of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p ->
        Hilbert $ propDeBrSubX targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        -- Parallel logic: Use boundDepthPropDeBrX, assuming 3 args needed
        -- Note: Original user code for ...XInt seemed to have arg mismatch here.
        -- Assuming intended use with targetIdx:
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    Bound idx -> Bound idx         -- Bound variables are untouched (mirroring user's ...XInt)
    V idx -> V idx             -- Free variables are untouched
    X idx
        | idx == targetIdx -> substitution -- *** Substitute X targetIdx ***
        | otherwise -> X idx
    XInternal idx -> XInternal idx -- Leave XInternal alone
    Tupl xs ->
        -- Apply the substitution recursively to each element in the list
        Tupl $ Prelude.map (objDeBrSubX targetIdx substitution) xs


-- Substitutes X targetIdx with substitution in a PropDeBr.
-- Directly parallels the user's provided propDeBrSubXInt logic.
-- WARNING: Logic under Forall/Exists (and Hilbert in objDeBrSubX)
-- may differ from standard capture-avoiding substitution.
propDeBrSubX :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubX targetIdx substitution template = case template of
    Neg p -> Neg $ propDeBrSubX targetIdx substitution p
    (:&&:) p1 p2 -> propDeBrSubX targetIdx substitution p1 :&&:
                    propDeBrSubX targetIdx substitution p2
    (:||:) p1 p2 -> propDeBrSubX targetIdx substitution p1 :||:
                    propDeBrSubX targetIdx substitution p2
    (:->:) p1 p2 -> propDeBrSubX targetIdx substitution p1 :->:
                    propDeBrSubX targetIdx substitution p2
    (:<->:) p1 p2 -> propDeBrSubX targetIdx substitution p1 :<->:
                     propDeBrSubX targetIdx substitution p2
    (:==:) o1 o2 -> objDeBrSubX targetIdx substitution o1 :==:
                    objDeBrSubX targetIdx substitution o2
    In o1 o2 -> objDeBrSubX targetIdx substitution o1 `In`
                objDeBrSubX targetIdx substitution o2
    Forall p -> Forall $ propDeBrSubX targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        -- Parallel logic: Use boundDepthPropDeBrX, assuming 3 args needed
        -- Note: Original user code for ...XInt seemed to have arg mismatch here.
        -- Assuming intended use with targetIdx:
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    Exists p -> Exists $ propDeBrSubX targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        -- Parallel logic: Use boundDepthPropDeBrX, assuming 3 args needed
        -- Note: Original user code for ...XInt seemed to have arg mismatch here.
        -- Assuming intended use with targetIdx:
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    (:>=:) o1 o2 -> objDeBrSubX targetIdx substitution o1 :>=:
                    objDeBrSubX targetIdx substitution o2
    F -> F









-- Swap X i to XInternal i recursively

swapXtoXIntProp :: PropDeBr -> PropDeBr
swapXtoXIntProp p = case p of
    Neg q -> Neg (swapXtoXIntProp q)
    (:&&:) p1 p2 -> (:&&:) (swapXtoXIntProp p1) (swapXtoXIntProp p2)
    (:||:) p1 p2 -> (:||:) (swapXtoXIntProp p1) (swapXtoXIntProp p2)
    (:->:) p1 p2 -> (:->:) (swapXtoXIntProp p1) (swapXtoXIntProp p2)
    (:<->:) p1 p2 -> (:<->:) (swapXtoXIntProp p1) (swapXtoXIntProp p2)
    (:==:) o1 o2 -> (:==:) (swapXtoXIntObj o1) (swapXtoXIntObj o2)
    In o1 o2 -> In (swapXtoXIntObj o1) (swapXtoXIntObj o2)
    Forall q -> Forall (swapXtoXIntProp q)
    Exists q -> Exists (swapXtoXIntProp q)
    (:>=:) o1 o2 -> (:>=:) (swapXtoXIntObj o1) (swapXtoXIntObj o2)
    F -> F


swapXtoXIntObj :: ObjDeBr -> ObjDeBr
swapXtoXIntObj o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapXtoXIntProp p)
    Bound i -> Bound i         -- Bound variables are untouched
    V i -> V i             -- Free variables are untouched
    X i -> XInternal i     -- *** Swap X to XInternal ***
    XInternal i -> XInternal i -- Leave existing XInternal alone


    Tupl xs ->
        -- Apply the swap recursively to each element in the list
        Tupl $ Prelude.map swapXtoXIntObj xs



-- Swap XInternal i back to X i recursively

swapXIntToXProp :: PropDeBr -> PropDeBr
swapXIntToXProp p = case p of
    Neg q -> Neg (swapXIntToXProp q)
    (:&&:) p1 p2 -> (:&&:) (swapXIntToXProp p1) (swapXIntToXProp p2)
    (:||:) p1 p2 -> (:||:) (swapXIntToXProp p1) (swapXIntToXProp p2)
    (:->:) p1 p2 -> (:->:) (swapXIntToXProp p1) (swapXIntToXProp p2)
    (:<->:) p1 p2 -> (:<->:) (swapXIntToXProp p1) (swapXIntToXProp p2)
    (:==:) o1 o2 -> (:==:) (swapXIntToXObj o1) (swapXIntToXObj o2)
    In o1 o2 -> In (swapXIntToXObj o1) (swapXIntToXObj o2)
    Forall q -> Forall (swapXIntToXProp q)
    Exists q -> Exists (swapXIntToXProp q)
    (:>=:) o1 o2 -> (:>=:) (swapXIntToXObj o1) (swapXIntToXObj o2)
    F -> F




swapXIntToXObj :: ObjDeBr -> ObjDeBr
swapXIntToXObj o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapXIntToXProp p)
    Bound i -> Bound i         -- Bound variables are untouched
    V i -> V i             -- Free variables are untouched
    X i -> X i             -- Leave existing X alone
    XInternal i -> X i     -- *** Swap XInternal back to X ***
    Tupl xs ->
        -- Apply the swap recursively to each element in the list
        Tupl $ Prelude.map swapXIntToXObj xs



-- | Applies a list of substitutions [(Index, Term)] to an ObjDeBr term.
objDeBrSubXs :: [(Int, ObjDeBr)] -> ObjDeBr -> ObjDeBr
objDeBrSubXs subs term =
    -- 3. Finally, swap any remaining XInternal back to X in the overall result.
    swapXIntToXObj $
    -- 1. Sequentially apply each substitution using foldl.
    foldl (\currentTerm (idx, substitutionTerm) ->
             -- 2. Before substituting, protect X vars inside the substitutionTerm
             --    by converting them to XInternal. Then use the original
             --    objDeBrSubX, which only targets X idx and leaves XInternal alone.
             objDeBrSubX idx (swapXtoXIntObj substitutionTerm) currentTerm
          ) term subs

-- Performs multiple substitutions simultaneously into a proposition.
-- Uses the original propDeBrSubX function internally.
propDeBrSubXs :: [(Int, ObjDeBr)] -> PropDeBr -> PropDeBr
propDeBrSubXs subs prop =
    -- 3. Finally, swap any remaining XInternal back to X in the overall result.
    swapXIntToXProp $
    -- 1. Sequentially apply each substitution using foldl.
    foldl (\currentProp (idx, substitutionTerm) ->
             -- 2. Before substituting, protect X vars inside the substitutionTerm.
             --    Then use the original propDeBrSubX.
             propDeBrSubX idx (swapXtoXIntObj substitutionTerm) currentProp
          ) prop subs









objDeBrApplyUG :: ObjDeBr -> Int -> Int -> ObjDeBr
objDeBrApplyUG obj freevarIdx boundvarIdx =
    case obj of
        Integ num -> Integ num
        Constant name -> Constant name
        Hilbert p1 -> Hilbert (propDeBrApplyUG p1 freevarIdx boundvarIdx)
        Bound idx -> Bound idx
        V idx -> if idx == freevarIdx then
                               Bound boundvarIdx
                           else
                               V idx
        Tupl xs ->
            -- Apply the substitution recursively to each element in the list
            Tupl $ Prelude.map (\x -> objDeBrApplyUG x freevarIdx boundvarIdx) xs



propDeBrApplyUG :: PropDeBr -> Int -> Int -> PropDeBr
propDeBrApplyUG prop freevarIdx boundvarIdx =
    case prop of
        Neg p -> Neg (propDeBrApplyUG p freevarIdx boundvarIdx)
        (:&&:) p1 p2 -> (:&&:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx) 
        (:||:) p1 p2 -> (:||:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (:->:) p1 p2 -> (:->:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (:<->:) p1 p2 -> (:<->:) (propDeBrApplyUG p1 freevarIdx boundvarIdx) (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (:==:) o1 o2 -> (:==:) (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        In o1 o2 -> In (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        Forall p -> Forall (propDeBrApplyUG p freevarIdx boundvarIdx)
        Exists p -> Exists (propDeBrApplyUG p freevarIdx boundvarIdx)
        (:>=:) o1 o2 -> (:>=:) (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
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


    

type PropErrDeBr = PL.LogicError PropDeBr DeBrSe Text ObjDeBr
type PropRuleDeBr = PL.LogicRule () PropDeBr DeBrSe Text

type PredErrDeBr = PREDL.LogicError PropDeBr DeBrSe Text ObjDeBr () 
type PredRuleDeBr = PREDL.LogicRule PropDeBr DeBrSe Text ObjDeBr ()

type PrfStdStepPredDeBr = PrfStdStep PropDeBr Text ()

subscriptCharTable :: [Text]
subscriptCharTable = ["₀","₁","₂","₃","₄","₅","₆","₇","₈","₉"]

showIndexAsSubscript :: Int -> Text
showIndexAsSubscript n =  Data.Text.concat (Prelude.map f (show n))
      where
          f char = subscriptCharTable!!read [char]



data PropDeBrStepContext where
  PropDeBrStepContext :: {stepContextFrames :: [Bool],
                            lineIndex :: [Int],
                            notFromMonad :: Bool,
                            lastLineNum :: Int} ->
                           PropDeBrStepContext

data PropDeBrStepState where
    PropDeBrStepState :: {sentMap :: Map PropDeBr [Int],
                          stpCount :: Int} -> PropDeBrStepState



showPropDeBrStep :: PrfStdStep PropDeBr Text () -> RWS PropDeBrStepContext Text PropDeBrStepState ()
showPropDeBrStep step = do
        context <- ask
        let cf = stepContextFrames context
        let lIndex = lineIndex context
        state <- get
        let dictMap = sentMap state
        let lineNum = stpCount state
        let notMonadic = notFromMonad context
        let lastLineN = lastLineNum context
        tell $ contextFramesShown cf
          <> showIndex lIndex
                <> (if (not . Prelude.null) lIndex then "." else "")
                <> (pack . show) lineNum
                <> ": "
        let newIndex = lIndex <> [lineNum]
        let qed = if notMonadic && lineNum == lastLineN && (not . null) cf then " ◻" else ""
        case step of
            PrfStdStepStep prop justification depends -> do
                let newDictMap = insert prop newIndex dictMap
                put $ PropDeBrStepState newDictMap (lineNum + 1)
                tell $ showProp newDictMap prop
                       <> "    "
                       <> justification
                       <> showIndices depends
                       <> qed
            PrfStdStepLemma prop mayWhereProven -> do
                let newDictMap = insert prop newIndex dictMap
                put $ PropDeBrStepState newDictMap (lineNum + 1)
                tell $ showProp newDictMap prop
                       <> "    LEMMA"
                       <> maybe "" (("[⬅ " <>) . (<> "]"). showIndexDepend) mayWhereProven
                       <> qed
            PrfStdStepConst constName _ mayWhereDefined -> do
                put $ PropDeBrStepState dictMap (lineNum + 1)
                tell $ "Const "
                     <> (pack .show) constName
                     <> "    CONSTDEF"
                     <> maybe "" (("[⬅ " <>) . (<> "]"). showIndexDepend) mayWhereDefined
            PrfStdStepTheorem prop steps -> do
                let newDictMap = insert prop newIndex dictMap
                put $ PropDeBrStepState newDictMap (lineNum + 1)
                tell $ showProp newDictMap prop
                       <> "    THEOREM"
                       <> showSubproofF steps True notMonadic mempty cf []
                       <> qed
            PrfStdStepSubproof prop subproofName steps -> do
                let newDictMap = insert prop newIndex dictMap
                put $ PropDeBrStepState newDictMap (lineNum + 1)
                tell $ showProp newDictMap prop
                       <> "    "
                       <> subproofName
                       <> qed
                       <> showSubproofF steps False notMonadic newDictMap cf newIndex
            PrfStdStepTheoremM prop -> do
                let newDictMap = insert prop newIndex dictMap
                put $ PropDeBrStepState newDictMap (lineNum + 1)
                tell $ showProp newDictMap prop
                       <> "    ALGORITHMIC_THEOREM"
                       <> qed
            PrfStdStepFreevar index _ -> do
                put $ PropDeBrStepState dictMap (lineNum + 1)
                tell $ "FreeVar 𝑣"
                     <> showIndexAsSubscript index
                     <> "    VARDEF"
            PrfStdStepFakeConst constName _ -> do
                put $ PropDeBrStepState dictMap (lineNum + 1)
                tell $ "Const "
                     <> constName
                     <> "    FAKE_CONST"
            PrfStdStepRemark text -> do
                put $ PropDeBrStepState dictMap (lineNum + 1)
                tell $ "REMARK"
                     <> qed
                     <> (if text == "" then "" else "\n" <> contextFramesShown cf <> "║") 
                     <> intercalate ("\n" <> contextFramesShown cf <> "║") (Data.Text.lines text)
                     <> "\n"
                     <> contextFramesShown cf
                     <> "╚"
        let eol = if lineNum < lastLineN then "\n" else ""
        tell eol
        return ()
      where
        contextFramesShown cf = Data.Text.concat (Prelude.map mapBool cf)
        mapBool frameBool =  if frameBool
                                then
                                    "┃"
                                else
                                    "│"
        showIndices idxs = if Prelude.null idxs then "" else "[" 
                            <> Data.Text.concat (intersperse "," (Prelude.map showIndexDepend idxs))
                            <> "]"
        showIndexDepend i = if Prelude.null i then "?" else showIndex i 
        showIndex i = Data.Text.concat (intersperse "." (Prelude.map (pack . show) i))
        showSubproofF steps isTheorem notMonadic dictMap cf newIndex = 
                    if notMonadic then
                         "\n"
                        <> showPropDeBrSteps (cf <> [isTheorem]) newIndex 0 notMonadic newDictMap steps
                        <> "\n"
                       <> Data.Text.concat (Prelude.map mapBool cf) 
                               <> cornerFrame
                      else ""
                     where
                        newDictMap = if isTheorem then
                                        mempty
                                        else
                                        dictMap
                        cornerFrame = if isTheorem then
                                 "┗"
                              else
                                  "└"


objDeBrSubBoundVarToX0 :: Int -> ObjDeBr -> ObjDeBr
objDeBrSubBoundVarToX0 boundVarIdx obj = case obj of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert (propDeBrSubBoundVarToX0 boundVarIdx p)                            
    Bound idx -> if idx == boundVarIdx then X 0
                   else Bound idx
    V idx -> V idx
    Tupl xs ->
        -- Apply the substitution recursively to each element in the list
        Tupl $ Prelude.map (objDeBrSubBoundVarToX0 boundVarIdx) xs



propDeBrSubBoundVarToX0 :: Int -> PropDeBr -> PropDeBr
propDeBrSubBoundVarToX0 boundVarIdx prop = case prop of
    Neg p -> Neg $ propDeBrSubBoundVarToX0 boundVarIdx p
    p :&&: q -> propDeBrSubBoundVarToX0 boundVarIdx p :&&: propDeBrSubBoundVarToX0 boundVarIdx q
    p :||: q -> propDeBrSubBoundVarToX0 boundVarIdx p :||: propDeBrSubBoundVarToX0 boundVarIdx q
    p :->: q -> propDeBrSubBoundVarToX0 boundVarIdx p :->: propDeBrSubBoundVarToX0 boundVarIdx q
    p :<->: q -> propDeBrSubBoundVarToX0 boundVarIdx p :<->: propDeBrSubBoundVarToX0 boundVarIdx q
    -- Uses the already implemented objDeBrSubBoundVarToX0 for terms
    a :==: b -> objDeBrSubBoundVarToX0 boundVarIdx a :==: objDeBrSubBoundVarToX0 boundVarIdx b
    In a b -> In (objDeBrSubBoundVarToX0 boundVarIdx a) (objDeBrSubBoundVarToX0 boundVarIdx b)
    -- Simple recursion for quantifiers, no index adjustment needed as per requirement
    Forall p -> Forall (propDeBrSubBoundVarToX0 boundVarIdx p)
    Exists p -> Exists (propDeBrSubBoundVarToX0 boundVarIdx p)
    a :>=: b -> objDeBrSubBoundVarToX0 boundVarIdx a :>=: objDeBrSubBoundVarToX0 boundVarIdx b
    F -> F
                
                

instance StdPrfPrintMonadFrame IO where
    printStartFrame :: [Bool] -> IO ()
    printStartFrame contextFrames = do
        unless (Prelude.null contextFrames) ( do
            let mapBool frameBool = 
                                   if frameBool
                                   then
                                      "┃"
                                   else
                                      "│"
            let contextFramesPre = Prelude.take (length contextFrames - 1) contextFrames
            let cornerBool =  last contextFrames
            let cornerFrame = if cornerBool then
                                 "┏"
                              else
                                  "┌"
            let frames = Data.Text.concat (Prelude.map mapBool contextFramesPre) <> cornerFrame 
            (putStrLn . unpack) frames
            )




instance StdPrfPrintMonadFrame (Either SomeException) where
    printStartFrame :: [Bool] -> Either SomeException ()
    printStartFrame _ = return ()

instance StdPrfPrintMonad PropDeBr Text () IO where
  printSteps :: [Bool] -> [Int] -> Int -> Map PropDeBr [Int] -> [PrfStdStep PropDeBr Text ()] -> IO ()
  printSteps contextFrames idx stepStart dictMap steps = do
    let outputTxt = showPropDeBrSteps contextFrames idx stepStart False dictMap steps
    (putStrLn . unpack) outputTxt



instance StdPrfPrintMonad PropDeBr Text () (Either SomeException) where
  printSteps :: [Bool] -> [Int] -> Int ->  Map PropDeBr [Int] -> [PrfStdStep PropDeBr Text ()] -> Either SomeException ()
  printSteps _ _ _ _ _ = return ()

showPropDeBrStepsPre :: [Bool] -> [Int] -> Int -> Bool -> Map PropDeBr [Int] -> [PrfStdStepPredDeBr] -> Text
showPropDeBrStepsPre contextFrames index startLine notFromMonad dictMap steps = 

    resultText runResult
    where
       lastLineN = startLine + length steps
       runResult = runRWS (mapM_ showPropDeBrStep steps) context state
       resultText (a,b,c) = c
       context = PropDeBrStepContext contextFrames index notFromMonad lastLineN
       state = PropDeBrStepState dictMap startLine

showPropDeBrSteps :: [Bool] -> [Int] -> Int -> Bool -> Map PropDeBr [Int] -> [PrfStdStepPredDeBr] -> Text
showPropDeBrSteps contextFrames index startLine notFromMonad dictMap steps = 

    resultText runResult
    where
       lastLineN = startLine + length steps - 1
       runResult = runRWS (mapM_ showPropDeBrStep steps) context state
       resultText (a,b,c) = c
       context = PropDeBrStepContext contextFrames index notFromMonad lastLineN
       state = PropDeBrStepState dictMap startLine
    
    
--    fst foldResult
--    where 

--        foldResult = Prelude.foldl f ("", stepStart) steps
--           where
--             f (accumText,stepNum) step = (accumText 
--                                             <> showPropDeBrStep contextFrames index stepNum 
--                                                   notFromMonad isLastLine dictMap step <> eol,
--                                           stepNum+1)
--                  where
--                    isLastLine = stepNum == stepStart + length steps - 1
--                    eol = if isLastLine then "" else "\n"



showPropDeBrStepsBase :: [PrfStdStepPredDeBr] -> Text
showPropDeBrStepsBase = showPropDeBrSteps [] [] 0 True mempty


showPropDeBrStepsBaseM :: (Monad m, Monoid r, 
             Proof eL r (PrfStdState PropDeBr Text ()) (PrfStdContext ()) [PrfStdStep PropDeBr Text ()] PropDeBr) 
                     => [PrfStdStepPredDeBr] -> ProofGenTStd () r PropDeBr Text m Text
showPropDeBrStepsBaseM steps = do 
      state <- getProofState
      let dict = provenSents state
      return $ showPropDeBrStepsBase steps



xsubPropDeBr :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBr p idx depth = case p of
    Neg p -> Neg (xsubPropDeBr p idx depth)
    (:&&:) p1 p2 -> (:&&:) (xsubPropDeBr p1 idx depth) (xsubPropDeBr p2 idx depth)
    (:||:) p1 p2 -> (:||:) (xsubPropDeBr p1 idx depth) (xsubPropDeBr p2 idx depth)
    (:->:) p1 p2 -> (:->:) (xsubPropDeBr p1 idx depth) (xsubPropDeBr p2 idx depth)
    (:<->:) p1 p2 -> (:<->:) (xsubPropDeBr p1 idx depth) (xsubPropDeBr p2 idx depth)
    (:==:) o1 o2 -> (:==:) (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)
    In o1 o2 -> In (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)
    Forall p -> Forall (xsubPropDeBr p idx depth)
    Exists p -> Exists (xsubPropDeBr p idx depth)
    (:>=:) o1 o2 -> (:>=:) (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)
    F -> F



xsubObjDeBr :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBr o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (xsubPropDeBr p idx depth)
    Bound i -> Bound i
    V i -> V i
    X i -> if i == idx then
                Bound depth 
            else
                X i
    XInternal i -> XInternal i
    Tupl xs ->
        -- Apply the substitution recursively to each element in the list
        Tupl $ Prelude.map (\x -> xsubObjDeBr x idx depth) xs


    


-- Substitutes XInternal idx with Bound depth in a PropDeBr expression.
-- Leaves regular X idx variables untouched.
xsubPropDeBrXInt :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBrXInt p idx depth = case p of
    Neg q -> Neg (xsubPropDeBrXInt q idx depth)
    (:&&:) p1 p2 -> (:&&:) (xsubPropDeBrXInt p1 idx depth) (xsubPropDeBrXInt p2 idx depth)
    (:||:) p1 p2 -> (:||:) (xsubPropDeBrXInt p1 idx depth) (xsubPropDeBrXInt p2 idx depth)
    (:->:) p1 p2 -> (:->:) (xsubPropDeBrXInt p1 idx depth) (xsubPropDeBrXInt p2 idx depth)
    (:<->:) p1 p2 -> (:<->:) (xsubPropDeBrXInt p1 idx depth) (xsubPropDeBrXInt p2 idx depth)
    (:==:) o1 o2 -> (:==:) (xsubObjDeBrXInt o1 idx depth) (xsubObjDeBrXInt o2 idx depth)
    In o1 o2 -> In (xsubObjDeBrXInt o1 idx depth) (xsubObjDeBrXInt o2 idx depth)
    Forall q -> Forall (xsubPropDeBrXInt q idx depth) -- Depth decreases implicitly in recursive calls if needed, handled by caller usually
    Exists q -> Exists (xsubPropDeBrXInt q idx depth) -- Depth decreases implicitly in recursive calls if needed, handled by caller usually
    (:>=:) o1 o2 -> (:>=:) (xsubObjDeBrXInt o1 idx depth) (xsubObjDeBrXInt o2 idx depth)
    F -> F



-- Substitutes XInternal idx with Bound depth in an ObjDeBr expression.
-- Leaves regular X idx variables untouched.
xsubObjDeBrXInt :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBrXInt o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (xsubPropDeBrXInt p idx depth) -- Recurse into Hilbert predicate
    Bound i -> Bound i -- Bound variables are untouched
    V i -> V i       -- Free variables are untouched
    X i -> X i       -- Regular X template variables are untouched
    XInternal i -> if i == idx then
                       Bound depth -- Substitute the target XInternal index with Bound depth
                   else
                       XInternal i -- Leave other XInternal indices alone

    Tupl xs ->
        -- Apply the substitution recursively to each element in the list
        Tupl $ Prelude.map (\x -> xsubObjDeBrXInt x idx depth) xs









instance LogicConst Text where
    newConst :: Set Text -> Text
    newConst constSet = head $ Prelude.filter (`notMember` constSet) $ Prelude.map (\i -> pack ("c" ++ show i)) [0..]
   
(./=.) :: ObjDeBr -> ObjDeBr -> PropDeBr
(./=.) a b = Neg $ a :==: b

infix 4 ./=.



nIn :: ObjDeBr -> ObjDeBr -> PropDeBr
nIn a b = Neg $ a `In` b

infix 4 `nIn`

eX :: Int -> PropDeBr -> PropDeBr
eX idx p = Exists $ xsubPropDeBr p idx (boundDepthPropDeBr p)



-- Creates an Exists quantifier, substituting XInternal idx with Bound depth within p.
eXInt :: Int -> PropDeBr -> PropDeBr
eXInt idx p = Exists $ xsubPropDeBrXInt p idx (boundDepthPropDeBr p)

-- Creates a Forall quantifier, substituting XInternal idx with Bound depth within p.
aXInt :: Int -> PropDeBr -> PropDeBr
aXInt idx p = Forall $ xsubPropDeBrXInt p idx (boundDepthPropDeBr p)

-- Creates a Hilbert term, substituting XInternal idx with Bound depth within p.
hXInt :: Int -> PropDeBr -> ObjDeBr
hXInt idx p = Hilbert $ xsubPropDeBrXInt p idx (boundDepthPropDeBr p)


eXBang :: Int -> PropDeBr -> PropDeBr
eXBang idx p = eX idx (p :&&: aX idx (p :->: Bound depth :==: Bound (depth+1)))
    where
        depth = boundDepthPropDeBr p         



aX :: Int -> PropDeBr -> PropDeBr
aX idx p = Forall $ xsubPropDeBr p idx (boundDepthPropDeBr p)

hX :: Int -> PropDeBr -> ObjDeBr
hX idx p = Hilbert (xsubPropDeBr p idx (boundDepthPropDeBr p))




isTuple :: Int -> ObjDeBr -> PropDeBr
isTuple i obj = propDeBrSubX i obj $ multiEx idxs 
      (X i :==: (Tupl [X j | j <- idxs ]))
      where idxs = [0 .. i-1]




isPair :: ObjDeBr -> PropDeBr
isPair t = isTuple 2 t



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



-- Helper function to apply a binder function (like eX or aX) for a list of indices.
-- Relies on the binder function itself (e.g., eX, aX) correctly calculating the
-- necessary depth and substituting X idx with the appropriate Bound depth index
-- at each step of the fold.
-- Binds indices from right-to-left (innermost binder corresponds to last index in list).
multiBinder :: (Int -> PropDeBr -> PropDeBr) -> [Int] -> PropDeBr -> PropDeBr
multiBinder binder indices body =
    foldr binder body indices

multiEx :: [Int] -> PropDeBr -> PropDeBr
multiEx indices body = multiBinder eX indices body

multiAx :: [Int] -> PropDeBr -> PropDeBr
multiAx indices body = multiBinder aX indices body


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
            equalityBody = (X tupleIdx) :==: (Tupl tuplArgs) -- Assumes Tupl constructor exists

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
        cond7 = aX 0 ( (X 0 `In` dom) :->: (eXBang 1 (Tupl [X 0, X 1] `In` graph)) )

    -- Combine all conditions using logical AND
    in
        cond3 :&&: cond4 :&&: cond5 :&&: cond6 :&&: cond7




pairFirst :: ObjDeBr -> ObjDeBr
pairFirst pair = project 2 0 pair




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
tripletLast triplet = project 3 2 triplet



(.@.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .@. x = objDeBrSubXs [(0,f),(1,x)] (hX 2 ( Tupl [X 1, X 2] `In` tripletLast (X 0) ))

--f .@. x = objDeBrSubXs [(0, project 3 2 f), (1, x)] (hX 2 ( Tupl [X 1, X 2] `In` X 0 ))

--f .@. x = objDeBrSubXs [(0,f),(1,x)] 


-- Template representing the composition h = f o g, defined implicitly
-- via the property: forall x ( h(x) == f(g(x)) )
compositionTemplate' :: ObjDeBr
compositionTemplate' =
   hX 99 $
     aX 11
       ( (X 99 .@. X 11) -- h(x)
          :==: -- ==
          (X 1 .@. (X 2 .@. X 11)) -- f(g(x))
       )


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



instance ZFC.LogicTerm ObjDeBr where
    parseTuple :: ObjDeBr -> Maybe [ObjDeBr]
    parseTuple = parseTupl
    buildTuple :: [ObjDeBr] -> ObjDeBr
    buildTuple = Tupl


             
instance ZFC.LogicSent PropDeBr ObjDeBr where
    emptySetAxiom :: PropDeBr
    emptySetAxiom = eX 0 $ Neg $ aX 1 $ X 1 `In` X 0


    specAxiom :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
    specAxiom idx t p =
    -- Substitute the actual input set term 't' for the internal placeholder 'XInternal 1'
        propDeBrSubXInt 1 t $
            -- Assert the existence of the result set 'B', represented by internal placeholder 'XInternal 2'
            -- Uses eXInt to bind this internal placeholder.
            eXInt 2 $
                -- Define the property of the result set 'B': Forall x...
            --  Uses user's 'aX' to bind the user's template variable 'X idx'.
                aX idx $
                   -- x ∈ B  <-> ( P(x) ∧ x ∈ t )
                   -- Uses X idx for 'x', XInternal 2 for 'B', XInternal 1 for 't'.
                   (X idx `In` XInternal 2)
                     :<->:
                   (p :&&: (X idx `In` XInternal 1))

    replaceAxiom :: Int -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
    replaceAxiom idx1 idx2 t p =
    -- Substitute the actual term 't' for the internal placeholder 'XInternal 1'
        propDeBrSubXInt 1 t
           (
              -- Premise: Forall a (a in t -> Exists! b P(a,b))
              -- Uses user's 'aX' and 'eXBang' as they operate on user template 'p' with user indices X idx1, X idx2
              -- Uses 'XInternal 1' as the placeholder for 't' before substitution
              aX idx1 ( (X idx1 `In` XInternal 1) :->: eXBang idx2 p )
                :->:
              -- Conclusion: Exists B (Forall a (a in B <-> Exists b (b in t AND P(a,b))))
              -- Uses internal 'eXInt' to bind the result set placeholder 'XInternal 2'
              -- Uses user's 'aX' and 'eX' for user variables X idx1, X idx2
              -- Uses 'XInternal 1' for placeholder 't', 'XInternal 2' for placeholder 'B'
              eXInt 2 (
                    aX idx1 ( (X idx1 `In` XInternal 2)
                        :<->:
                        eX idx2 ( (X idx2 `In` XInternal 1) :&&: p )
                      )
                    )
        )
     
                              
            
                           
      
 



 





