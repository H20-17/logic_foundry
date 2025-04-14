module Langs.BasicUntyped (
    ObjDeBr(Integ,Constant,V,X,Pair),
    PropDeBr(Neg,(:&&:),(:||:),(:->:),(:<->:),(:==:),In,(:>=:),F),
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
    (.:.)
) where
import Control.Monad ( unless )
import Data.List (intersperse)
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
import RuleSets.ZFC (emptySetAxiom, specification,parseIn,memberOf)
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS )
import Text.XHtml (sub)
import qualified Internal.StdPattern
import Distribution.Backpack.ConfiguredComponent (newPackageDepsBehaviour)




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
    
    
  

class SubexpDeBr sub where
    toSubexpParseTree :: sub -> Map PropDeBr [Int] -> SubexpParseTree




binaryOpInData :: [(Text,(Associativity,Int))]
binaryOpInData = [("=",(NotAssociative,5)),("→",(RightAssociative,1)),("↔",(RightAssociative,1)),("∈",(NotAssociative,5)),("∧",(RightAssociative,4)),("∨",(RightAssociative,3)),
     ("≥",(NotAssociative,5)),
     ("≠",(NotAssociative,5)),("∉",(NotAssociative,5)),
     ("⊆",(NotAssociative,5)),("⊂",(NotAssociative,5)),("⊈",(NotAssociative,5)) ]


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
    Pair a b -> objDeBrBoundVarInside a idx || objDeBrBoundVarInside b idx




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
    Pair o1 o2 -> Pair (swapBoundIndexObj fromIdx toIdx o1) (swapBoundIndexObj fromIdx toIdx o2)

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
    -- Use recursive calls for pairs
    Pair a b -> max (boundDepthObjDeBrX targetIdx substitutionDepth a) (boundDepthObjDeBrX targetIdx substitutionDepth b)

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
    Pair a b -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth a) (boundDepthObjDeBrXInt targetIdx substitutionDepth b)

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


        
instance SubexpDeBr ObjDeBr where
    toSubexpParseTree :: ObjDeBr -> Map PropDeBr [Int] -> SubexpParseTree
    toSubexpParseTree obj dict = case obj of
        Integ i -> ParseTreeInt i
        Constant c -> ParseTreeConst c
        Bound i -> ParseTreeBoundVar i
        V i -> ParseTreeFreeVar i
        X i -> ParseTreeX i
        Pair a b -> Tuple [toSubexpParseTree a dict, toSubexpParseTree b dict]

        Hilbert p ->
            -- First, check if Exists p is proven, for the ε[line] shorthand
            case Data.Map.lookup (Exists p) dict of
                Just idxs -> HilbertShort idxs -- Use ε[line] shorthand

                -- If Exists p is NOT proven, THEN check structure of p for other shorthands
                Nothing ->
                    case p of
                        -- Pattern 1: Function Application (User's detailed version)
                        Pair x (Bound d) `In` (Hilbert (Exists ( f :==: Pair (Bound dp1) (Bound dp0) ))) ->
                            if    d == max (boundDepthObjDeBr f + 2) (boundDepthObjDeBr x)
                               && dp0 == boundDepthObjDeBr f
                               && dp1 == dp0 + 1
                               && not (objDeBrBoundVarInside f dp0)
                               && not (objDeBrBoundVarInside f dp1)
                               && not (objDeBrBoundVarInside f d)
                               && not (objDeBrBoundVarInside x d)
                            then
                               FuncApp (toSubexpParseTree f dict) (toSubexpParseTree x dict)
                            else
                               renderDefaultHilbert p -- Use local helper

                        -- Pattern 2: Set Builder
                        Forall (Bound a `In` Bound b :<->: q :&&: Bound c `In` t) ->
                             let pDepth = boundDepthPropDeBr p
                                 qTree = toSubexpParseTree q dict
                             in if a == pDepth - 1
                                   && c == a
                                   && b == pDepth
                                   && not (propDeBrBoundVarInside q b)
                                   && not (objDeBrBoundVarInside t a)
                                   && not (objDeBrBoundVarInside t b) then
                                       Builder (toSubexpParseTree t dict) (sbParseTreeNormalize (pDepth-1) qTree)
                                else
                                   renderDefaultHilbert p -- Use local helper

                        -- Default for other Hilbert structures
                        _ -> renderDefaultHilbert p -- Use local helper
      where
        -- Define renderDefaultHilbert locally within toSubexpParseTree
        -- It can capture 'dict' from the outer scope.
        renderDefaultHilbert :: PropDeBr -> SubexpParseTree
        renderDefaultHilbert currentP = Binding "ε" (sbParseTreeNormalize pDepth pTree)
            where
                pDepth = boundDepthPropDeBr currentP
                pTree = toSubexpParseTree currentP dict -- Use 'dict' from outer scope

boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     Integ num -> 0
     Constant name -> 0
     Hilbert prop -> boundDepthPropDeBr prop + 1
     Bound idx -> 0
     V idx -> 0
     X idx -> 0
     XInternal idx -> 0
     Pair a b -> max (boundDepthObjDeBr a) (boundDepthObjDeBr b)



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


instance SubexpDeBr PropDeBr where
  toSubexpParseTree :: PropDeBr -> Map PropDeBr [Int] -> SubexpParseTree
  toSubexpParseTree prop dict = case prop of

      Neg q -> case q of
        -- Existing case for Inequality (≠)
        o1 :==: o2 -> BinaryOp "≠" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)

        -- Existing case for Not Member (∉)
        In o1 o2 -> BinaryOp "∉" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)

        -- >>> New case for Not Subset (⊈) <<<
        -- Check if q matches the structure Forall(Bound idx `In` a :->: Bound idx `In` b)
        Forall (Bound idx1 `In` a1 :->: Bound idx2 `In` a2) ->
            -- Check if it matches the specific structure generated by your 'subset' helper
            if idx1 == max (boundDepthObjDeBr a1) (boundDepthObjDeBr a2) -- Corrected depth check
               && idx2 == idx1             -- Index consistency check
               && not (objDeBrBoundVarInside a1 idx1) -- Precondition check on a1
               && not (objDeBrBoundVarInside a2 idx1) -- Precondition check on a2
            then
               -- If it matches, render using the ⊈ symbol
               BinaryOp "⊈" (toSubexpParseTree a1 dict) (toSubexpParseTree a2 dict)
            else
               -- If it's a Forall but doesn't match the subset conditions, render as ¬(∀...)
               UnaryOp "¬" (toSubexpParseTree q dict) -- q is the Forall(...) expression

        -- Fallback for any other Neg expression (e.g., ¬(A ∧ B))
        _ -> UnaryOp "¬" (toSubexpParseTree q dict)

      (:&&:) a b -> andBuild a b 
        
        
        --BinaryOp "∧" (toSubexpParseTree a dict) (toSubexpParseTree b dict)


      (:||:) a b -> BinaryOp "∨" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:->:)  a b -> BinaryOp "→" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:<->:) a b -> BinaryOp "↔"(toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:==:) a b -> BinaryOp "=" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      In a b -> BinaryOp "∈" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      Forall a ->  abuild a
      Exists a -> ebuild a
      (:>=:) a b -> BinaryOp "≥" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      F -> ParseTreeF
    where
        andBuild (Forall (Bound idx1 `In` a1 :->: Bound idx2 `In` a2))
                        (Neg (a3 :==: a4)) =
                 if idx1 == max (boundDepthObjDeBr a1) (boundDepthObjDeBr a2)
                    && idx2 == idx1
                    && a1 == a3
                    && a2 == a4
                    && not (objDeBrBoundVarInside a1 idx1) 
                    && not (objDeBrBoundVarInside a2 idx1)
                 then
                    BinaryOp "⊂" (toSubexpParseTree a1 dict) (toSubexpParseTree a2 dict)
                 else
                    andBuildDefault (Forall (Bound idx1 `In` a1 :->: Bound idx2 `In` a2))
                         (Neg (a3 :==: a4))
        andBuild a b = andBuildDefault a b                    
        andBuildDefault a b = BinaryOp "∧" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
        
        abuild a = case a of
            Bound idx1 `In` a1 :->: Bound idx2 `In` a2 ->
                 if idx1 == max (boundDepthObjDeBr a1) (boundDepthObjDeBr a2)
                    && idx2 == idx1
                    && not (objDeBrBoundVarInside a1 idx1) 
                    && not (objDeBrBoundVarInside a2 idx1)
                 then
                    BinaryOp "⊆" (toSubexpParseTree a1 dict) (toSubexpParseTree a2 dict)
                 else
                    defaultExp
            _ -> defaultExp
          where
            defaultExp = Binding "∀" (sbParseTreeNormalize pDepth pTree) 
                  where
                      pDepth = boundDepthPropDeBr a
                      pTree = toSubexpParseTree a dict
        ebuild a = case a of  
            p :&&: q -> if Forall (pDecremented :->: Bound (depth - 1):==: Bound depth) == q then
                            Binding "∃!" (sbParseTreeNormalize pDepth pTree)
                        else
                            defaultP
                    where
                            pDepth = boundDepthPropDeBr p
                            pTree = toSubexpParseTree pDecremented dict
                            pDecremented = boundDecrementPropDeBr depth p

            _ -> defaultP
         where
           defaultP = Binding "∃" (sbParseTreeNormalize pDepth pTree) 
                where
                    pDepth = boundDepthPropDeBr a
                    pTree = toSubexpParseTree a dict
           depth = boundDepthPropDeBr a     
 





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

    Pair :: ObjDeBr -> ObjDeBr -> ObjDeBr

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
     Pair a b -> checkSanityObjDeBr a varStackHeight tmpltVarIndices constSet boundSet
                 <|> checkSanityObjDeBr b varStackHeight tmpltVarIndices constSet boundSet

boundDecrementObjDeBr :: Int -> ObjDeBr -> ObjDeBr
boundDecrementObjDeBr idx obj = case obj of
     Integ num -> Integ num
     Constant name -> Constant name
     Hilbert prop -> Hilbert (boundDecrementPropDeBr idx prop)
     Bound i -> if i == idx then Bound (i - 1) else Bound i
     V i -> V i
     X i -> X i
     Pair a b -> Pair (boundDecrementObjDeBr idx a) (boundDecrementObjDeBr idx b)



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
        Pair a b -> objDeBrXInside subidx a || objDeBrXInside subidx b

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
        Pair a b -> objDeBrXInsideInt subidx a || objDeBrXInsideInt subidx b





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
    Pair o1 o2 -> 
        Pair (objDeBrSubXInt targetIdx substitution o1) 
                (objDeBrSubXInt targetIdx substitution o2)






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
    Pair o1 o2 ->
        Pair (objDeBrSubX targetIdx substitution o1)
             (objDeBrSubX targetIdx substitution o2)

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
    Pair o1 o2 -> Pair (swapXtoXIntObj o1) (swapXtoXIntObj o2)

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
    Pair o1 o2 -> Pair (swapXIntToXObj o1) (swapXIntToXObj o2)
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
        Pair a b -> Pair (objDeBrApplyUG a freevarIdx boundvarIdx) (objDeBrApplyUG b freevarIdx boundvarIdx)



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
    parseEq p = case p of
                (:==:) o1 o2 -> Just(o1,o2)
                _ -> Nothing
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
    Pair o1 o2 -> Pair (objDeBrSubBoundVarToX0 boundVarIdx o1) 
           (objDeBrSubBoundVarToX0 boundVarIdx o2) 
 

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
    Pair o1 o2 -> Pair (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)


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
    Pair o1 o2 -> Pair (xsubObjDeBrXInt o1 idx depth) (xsubObjDeBrXInt o2 idx depth)







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




isPair :: ObjDeBr -> PropDeBr
isPair t = propDeBrSubX 2 t $  eX 0 $ eX 1 $ X 2 :==: Pair (X 0) (X 1)


isRelation :: ObjDeBr -> PropDeBr
isRelation s = aX 0 $ X 0 `In` s :->: isPair (X 0)


isFunction :: ObjDeBr -> PropDeBr
isFunction t = isRelation t :&&: 
          aX 0 ( X 0 `In` relDomain t :->: eXBang 1 $ Pair (X 0) (X 1) `In` t)

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


pairFirstTemplate :: ObjDeBr
pairFirstTemplate = hX 2 (eX 1 (X 0 :==: Pair (X 2) (X 1)))
                             --  f        -- fGraph Domain


pairFirst :: ObjDeBr -> ObjDeBr
pairFirst pair = objDeBrSubX 0 pair (hX 2 (eX 1 (X 0 :==: Pair (X 2) (X 1))))



relDomain :: ObjDeBr -> ObjDeBr
relDomain s = objDeBrSubX 0 s (hX 1(aX 2 (X 2 `In` X 1)  -- x ∈ D
                       :<->:                             -- iff
                            eX 3 (Pair (X 2) (X 3) `In` X 0)))


-- let us assume that f is a pair
-- of form Pair(t,z) where t is a function in set theory
-- (a set of pairs serving as the function) as conventionally
-- understood, and z is the co-domain, being a non-strict
-- superset of the image.
-- Note that this is just a helper function. It doesn't test
-- that f really is a function. It also depends on pairFirst working correctly.
--


(.@.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .@. x = objDeBrSubXs [(0,f),(1,x)] (hX 2 ( Pair (X 1) (X 2) `In` pairFirst (X 0) ))




-- Template representing the composition h = f o g, defined implicitly
-- via the property: forall x ( h(x) == f(g(x)) )
compositionTemplate :: ObjDeBr
compositionTemplate =
   hX 99 $
     aX 11
       ( (X 99 .@. X 11) -- h(x)
          :==: -- ==
          (X 1 .@. (X 2 .@. X 11)) -- f(g(x))
       )


infixr 9 .:. -- Same precedence and associativity as Haskell's .


-- Infix operator for composition f .:. g = f o g
-- Substitutes f and g into the compositionTemplate
(.:.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .:. g = --objDeBrSubXs [(1, f), (2, g)] 
  objDeBrSubXs [(1,f),(2,g)] compositionTemplate




             
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
                              
            
                           
      
 



 





