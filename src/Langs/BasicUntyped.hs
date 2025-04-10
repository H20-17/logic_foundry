module Langs.BasicUntyped (
    ObjDeBr(..),
    PropDeBr(..),
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
    (.@.)
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
    deriving (Eq, Ord)


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






-- instance SubexpDeBr ObjDeBr where
--    toSubexpParseTree :: ObjDeBr -> Map PropDeBr [Int]  -> SubexpParseTree
--    toSubexpParseTree obj dict = case obj of
--        Integ i -> ParseTreeInt i
--        Constant c -> ParseTreeConst c
--        Hilbert p -> case Data.Map.lookup (Exists p) dict of
--            Just idxs -> HilbertShort idxs
--            Nothing -> case p of
--                Forall (Bound a `In` Bound b :<->: q :&&: Bound c `In` t) -> 
--                    if a == pDepth - 1 
--                        && c == a 
--                        && b == pDepth 
--                        && not (propDeBrBoundVarInside q b) 
--                        && not (objDeBrBoundVarInside t a) 
--                        && not (objDeBrBoundVarInside t b) then
--                               Builder tTree (sbParseTreeNormalize (pDepth-1) qTree)
--                        -- For this to be a proper usage, q cannot bind b, and t cannot
--                        -- bind a or b.
--                        -- so we have to check for this before using the builder notation.
--                        -- If either of these two conditions are not met and we used
--                        -- the builder notation, then we would would lose
--                        -- quantifiers that are quantifying over b or a.
--                    else 
--                        Binding "ε" (sbParseTreeNormalize pDepth pTree) 
--                          where
--                            pDepth = boundDepthPropDeBr p
--                            pTree = toSubexpParseTree p dict
--                            tTree = toSubexpParseTree t dict
--                            qTree = toSubexpParseTree q dict
--                Pair x (Bound d) `In` (Hilbert (Exists ( f :==: Pair (Bound dp_fPlus1) (Bound dp_f) ))) ->
--                    if    d == max (boundDepthObjDeBr f + 2) (boundDepthObjDeBr x)
--                       && dp_f == boundDepthObjDeBr f
--                       && dp_fPlus1 == dp_f + 1
--                       && not (objDeBrBoundVarInside f dp_f)
--                       && not (objDeBrBoundVarInside f (dp_f+1))
--                       && not (objDeBrBoundVarInside f d)
--                       && not (objDeBrBoundVarInside x d)
--                   then
--                       FuncApp (toSubexpParseTree f dict) (toSubexpParseTree x dict)
--                   else
--                       Binding  "ε" (sbParseTreeNormalize pDepth pTree)  
--                           where
--                            pDepth = boundDepthPropDeBr p
--                            pTree = toSubexpParseTree p dict
--                _ -> Binding "ε" (sbParseTreeNormalize pDepth pTree) 
--                          where
--                            pDepth = boundDepthPropDeBr p
--                            pTree = toSubexpParseTree p dict
--        Bound i -> ParseTreeBoundVar i
--        V i -> ParseTreeFreeVar i
--        X i -> ParseTreeX i
--        Pair a b -> Tuple [toSubexpParseTree a dict,toSubexpParseTree b dict]
        
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


instance Show ObjDeBr where
    show :: ObjDeBr -> String
    show obj = unpack $ showSubexpParseTree $ toSubexpParseTree obj mempty                         


instance Show PropDeBr where
    show :: PropDeBr -> String
    show obj = unpack $ showSubexpParseTree $ toSubexpParseTree obj mempty


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
      Bound :: Int -> ObjDeBr
      V :: Int ->ObjDeBr
      X :: Int -> ObjDeBr
      Pair :: ObjDeBr -> ObjDeBr -> ObjDeBr
   deriving (Eq, Ord)








data DeBrSe where
    ObjDeBrSeConstNotDefd :: Text -> DeBrSe
    ObjDeBrBoundVarIdx :: Int -> DeBrSe
    ObjDeBrFreeVarIdx :: Int -> DeBrSe
    ObjDeBrTemplateVarIdx :: Int -> DeBrSe
    ObjDeBrUnconsumedX :: Int -> DeBrSe
   deriving Show






checkSanityObjDeBr :: ObjDeBr -> Int -> Int -> Set Text -> Set Int -> Maybe DeBrSe

checkSanityObjDeBr obj varStackHeight templateVarCount constSet boundSet = case obj of
     Integ num -> Nothing
     Constant name -> if name `Set.member` constSet then
                           Nothing
                       else
                           (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> checkSanityPropDeBr prop varStackHeight templateVarCount constSet 
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
        if idx >= 0 && idx < templateVarCount then
            Nothing
        else
            (return . ObjDeBrTemplateVarIdx) idx
     Pair a b -> checkSanityObjDeBr a varStackHeight templateVarCount constSet boundSet
                 <|> checkSanityObjDeBr b varStackHeight templateVarCount constSet boundSet

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



checkSanityPropDeBr :: PropDeBr -> Int -> Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityPropDeBr prop freevarStackHeight templateVarCount consts boundVars = 
      case prop of
        Neg p -> checkSanityPropDeBr p freevarStackHeight templateVarCount consts boundVars
        (:&&:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight templateVarCount consts boundVars
        (:||:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight templateVarCount consts boundVars
        (:->:)  p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight templateVarCount consts boundVars
        (:<->:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight templateVarCount consts boundVars
        In o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight templateVarCount consts boundVars
        (:==:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight templateVarCount consts boundVars
        Forall prop -> checkSanityPropDeBr prop freevarStackHeight templateVarCount consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        Exists prop -> checkSanityPropDeBr prop freevarStackHeight templateVarCount consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        (:>=:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight templateVarCount consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight templateVarCount consts boundVars
        F -> Nothing



instance TypeableTerm ObjDeBr Text () DeBrSe where
 
     getTypeTerm :: [()] -> [()] -> Map Text () -> ObjDeBr -> Either DeBrSe ()
     getTypeTerm ts vs constDict term = 
         maybe (return ()) throwError (checkSanityObjDeBr term (Prelude.length vs) 
                        (Prelude.length ts) (keysSet constDict) mempty)
     const2Term :: Text -> ObjDeBr
     const2Term = Constant
     free2Term :: Int -> ObjDeBr
     free2Term = V


instance TypedSent  Text () DeBrSe PropDeBr where
    checkSanity :: [()] -> [()] -> Map Text () -> PropDeBr -> Maybe DeBrSe
    checkSanity tsTypes freeVarStack constDict prop = checkSanityPropDeBr
        prop (Prelude.length freeVarStack) 
        (Prelude.length tsTypes)  (keysSet constDict) mempty



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
    false -> False



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
        Pair a b -> objDeBrXInside subidx a || objDeBrXInside subidx b




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
    false -> False




objDeBrSubX' :: Int -> ObjDeBr -> ObjDeBr -> Int -> ObjDeBr
objDeBrSubX' subidx substitution template threshold = case template of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert $ propDeBrSubX' subidx substitution p newThreshold
      where
         newThreshold = 
            if propDeBrXInside subidx p then
                threshold - 1
            else
                threshold

                                    
    Bound idx -> if idx < threshold  then
          Bound idx
        else
          Bound (idx+termDepth)
        where
            termDepth = boundDepthObjDeBr substitution
    V idx -> V idx
    X idx 
        | idx == subidx -> substitution
        | otherwise -> X idx
    Pair o1 o2 -> 
        Pair (objDeBrSubX' subidx substitution o1 threshold) (objDeBrSubX' subidx substitution o2 threshold) where
      
        







propDeBrSubX' :: Int -> ObjDeBr -> PropDeBr -> Int -> PropDeBr
propDeBrSubX' subidx t template threshold = case template of
    Neg p -> Neg $ propDeBrSubX' subidx t p threshold
    (:&&:) p1 p2 -> propDeBrSubX' subidx t p1 threshold :&&: propDeBrSubX' subidx t p2 threshold
    (:||:) p1 p2 ->  propDeBrSubX' subidx t p1 threshold :||: propDeBrSubX' subidx t p2 threshold
    (:->:) p1 p2 ->  propDeBrSubX' subidx t p1 threshold :->: propDeBrSubX' subidx t p2 threshold
    (:<->:) p1 p2 ->  propDeBrSubX' subidx t p1 threshold :<->: propDeBrSubX' subidx t p2 threshold

    (:==:) o1 o2 ->  objDeBrSubX' subidx t o1 threshold :==: objDeBrSubX' subidx t o2 threshold
    In o1 o2 ->  objDeBrSubX' subidx t o1 threshold `In` objDeBrSubX' subidx t o2 threshold
    Forall p -> Forall $ propDeBrSubX' subidx t p newThreshold
       where
           newThreshold = 
            if propDeBrXInside subidx p then
                threshold - 1
            else
                threshold
    Exists p -> Exists $ propDeBrSubX' subidx t p newThreshold
       where
           newThreshold = 
            if propDeBrXInside subidx p then
                threshold - 1
            else
                threshold
    (:>=:) o1 o2 -> objDeBrSubX' subidx t o1 threshold :>=: objDeBrSubX' subidx t o2 threshold
    F -> F

objDeBrSubX :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubX subidx t template = 
    objDeBrSubX' subidx t template startThreshold
       where
          startThreshold = boundDepthObjDeBr template

propDeBrSubX :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubX subidx t template = 
    propDeBrSubX' subidx t template startThreshold
       where
          startThreshold = boundDepthPropDeBr template


-- | Applies a list of substitutions [(Index, Term)] to an ObjDeBr term.
objDeBrSubXs :: [(Int, ObjDeBr)]  -- List of (Index to replace, Substitution Term) pairs
              -> ObjDeBr        -- Initial proposition template
              -> ObjDeBr        -- Resulting proposition after all substitutions
objDeBrSubXs substitutions initialObj =
    -- Use foldl' to iteratively apply each substitution from the list
    foldl' applySub initialObj substitutions
  where
    -- Helper function for the fold: applies one substitution step
    applySub :: ObjDeBr          -- The object from the previous step
             -> (Int, ObjDeBr)    -- The current substitution (idx, term)
             -> ObjDeBr          -- The object after this substitution
    applySub currentObj (idx, term) =
        -- Call propDeBrSubX to substitute X idx with term in currentObj
        objDeBrSubX idx term currentObj








-- | Applies a list of substitutions [(Index, Term)] to a PropDeBr term.
propDeBrSubXs :: [(Int, ObjDeBr)]  -- List of (Index to replace, Substitution Term) pairs
              -> PropDeBr        -- Initial proposition template
              -> PropDeBr        -- Resulting proposition after all substitutions
propDeBrSubXs substitutions initialProp =
    -- Use foldl' to iteratively apply each substitution from the list
    foldl' applySub initialProp substitutions
  where
    -- Helper function for the fold: applies one substitution step
    applySub :: PropDeBr          -- The proposition from the previous step
             -> (Int, ObjDeBr)    -- The current substitution (idx, term)
             -> PropDeBr          -- The proposition after this substitution
    applySub currentProp (idx, term) =
        -- Call propDeBrSubX to substitute X idx with term in currentProp
        propDeBrSubX idx term currentProp



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
    substX0 :: PropDeBr -> ObjDeBr -> PropDeBr
    substX0 template obj = propDeBrSubX 0 obj template


    

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
           (objDeBrSubBoundVarToX0 boundVarIdx o1) 
 

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
    Pair o1 o2 -> Pair (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)






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


eXBang :: Int -> PropDeBr -> PropDeBr
eXBang idx p = eX idx (p :&&: aX idx (p :->: Bound depth :==: Bound (depth+1)))
    where
        depth = boundDepthPropDeBr p         



aX :: Int -> PropDeBr -> PropDeBr
aX idx p = Forall $ xsubPropDeBr p idx (boundDepthPropDeBr p)

hX :: Int -> PropDeBr -> ObjDeBr
hX idx p = Hilbert (xsubPropDeBr p idx (boundDepthPropDeBr p))




isPair :: ObjDeBr -> PropDeBr
isPair t = eX 0 $ eX 1 $ t :==: Pair (X 0) (X 1)

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

-- Assumes that t is a term with no template variables.
-- and p is predicate template with X i as a template variable and
-- no other template variables. Free variables allowed.
-- For this to be a proper usage, p cannot bind the outer hilbert
-- quantifier variable, and t cannot
-- bind X i or the outer hilbert quantifier variable. 
-- It is not an actual programmatic error if these conditions
-- are not met, but the result won't be representable in set
-- builder notation, and when corresponding output is shown, 
-- set builder notation
-- will NOT be used. Essentially, improper usage results in a GIGO
-- situation.
                       
                          
builderX idx t p = Hilbert $ aX idx $ X idx `In` Bound hilbertIdx :->: p :&&: X idx `In` t
     where hilbertIdx = max (boundDepthObjDeBr t) (boundDepthPropDeBr p) + 1


-- For intended usage,
-- a and b should both not have any template variables occuring within it.
-- If they do, they can effectively result in variable capture, if they are consumed,
-- or an insane sentence, if any are left unconsumed. Consider this a GIGO situation.
subset :: ObjDeBr -> ObjDeBr -> PropDeBr
subset a b = propDeBrSubXs [(1,a),(0,b)] 
          (eX 2 (X 2 `In` X 1 :->: X 2 `In` X 0))


strictSubset :: ObjDeBr -> ObjDeBr -> PropDeBr
strictSubset a b = subset a b :&&: Neg (a :==: b)

notSubset :: ObjDeBr -> ObjDeBr -> PropDeBr
notSubset a b = Neg (subset a b)

-- The following function projects the first element of a pair.
-- For intended usage, pair should not have any template variables occuring within it.
-- If it does, it can effectively result in variable capture, if they are consumed,
-- or an insane sentence, if any are left unconsumed. Consider this a GIGO situation.
pairFirst :: ObjDeBr -> ObjDeBr
pairFirst pair = objDeBrSubX 0 pair (hX 2 (eX 1 (X 0 :==: Pair (X 2) (X 1))))


relDomain :: ObjDeBr -> ObjDeBr
relDomain s = Hilbert $ Forall
                       (    (Bound (d+1) `In` Bound (d+2))  -- x ∈ D
                       :<->:                             -- iff
                            Exists (Pair (Bound (d+1)) (Bound d) `In` s) -- exists y such that <x, y> in s
                       )
   where
    -- Calculate base depth based on free vars/bindings within 's'
    d = boundDepthObjDeBr s
    -- Note: Assumes 's' itself doesn't contain indices d, d+1, d+2
    -- in a way that clashes, similar to preconditions for subset.
    -- Indices used:
    -- d   represents 'y' bound by Exists
    -- d+1 represents 'x' bound by Forall
    -- d+2 represents 'D' (the domain set) bound by Hilbert

--relDomain' :: ObjDeBr -> ObjDeBr
--relDomain s = 


-- let us assume that f is a pair
-- of form Pair(t,z) where t is a function in set theory
-- (a set of pairs serving as the function) as conventionally
-- understood, and z is the co-domain, being a non-strict
-- superset of the image.
-- Note that this is just a helper function. It doesn't test
-- that f really is a function. It also depends on pairFirst working correctly.
--
-- >> Precondition Note for Indexing <<
-- This helper calculates d = max (boundDepthObjDeBr f + 2) (boundDepthObjDeBr x).
-- It uses `Bound d` for the 'y' variable (the function result y=f(x))
-- bound by the `Hilbert` operator.
-- For this representation to work reliably within this system's indexing convention:
-- 1. The term `f` should NOT already contain free occurrences of `Bound dp_f` or `Bound (dp_f + 1)`,
--    where `dp_f = boundDepthObjDeBr f` (these indices are used internally by `pairFirst f`).
-- 2. Neither the term `f` nor the term `x` should contain free occurrences of `Bound d`,
--    where `d` is the calculated index `max (boundDepthObjDeBr f + 2) (boundDepthObjDeBr x)`.
-- Violating these preconditions might lead to unintended variable capture or meaning (GIGO).
--
(.@.) :: ObjDeBr -> ObjDeBr -> ObjDeBr
f .@. x = Hilbert ( Pair x (Bound d) `In` pairFirst f )
           -- Calculate index 'd' for 'y' (bound by Hilbert) using the specific rule for this helper
           where d = max (boundDepthObjDeBr f + 2) (boundDepthObjDeBr x)
           -- Here Hilbert binds 'y', represented by 'Bound d' inside the property
           -- The property is P(y) = <x, y> ∈ f_graph (where f_graph = pairFirst f).


instance ZFC.LogicSent PropDeBr ObjDeBr where
    emptySetAxiom :: PropDeBr
    emptySetAxiom = eX 0 $ Neg $ aX 1 $ X 1 `In` X 0
    specAxiom :: ObjDeBr -> PropDeBr -> PropDeBr
    -- specification axiom composed from term t and predicate P(x)
    specAxiom t p = eX 0 $ aX 1 $ X 1 `In` X 0 :<->: p :&&: X 1 `In` t
    replaceAxiom:: ObjDeBr -> PropDeBr -> PropDeBr
    replaceAxiom t p = aX 0 (X 0 `In` t :->: eXBang 1 p)
                         :->: eX 2 (aX 1 (X 1 `In` X 2 :<->: eX 0 (X 0 `In` t :&&: p)))  
      
 



 





