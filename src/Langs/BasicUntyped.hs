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
    eXBang
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
import qualified RuleSets.Internal.PropLogic as PL
import qualified RuleSets.Internal.PredLogic as PREDL
import qualified RuleSets.Internal.ZFC as ZFC
import RuleSets.Internal.PropLogic (LogicSent(parseIff))
import RuleSets.Internal.ZFC (emptySetAxiom, specification,parseIn,memberOf)
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS )



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
    Binding :: Text -> Int -> SubexpParseTree -> SubexpParseTree
    HilbertShort :: [Int] -> SubexpParseTree
    Atom :: Text -> SubexpParseTree
    Tuple :: [SubexpParseTree] -> SubexpParseTree



class SubexpDeBr sub where
    toSubexpParseTree :: sub -> Map PropDeBr [Int] -> SubexpParseTree




binaryOpInData :: [(Text,(Associativity,Int))]
binaryOpInData = [("=",(NotAssociative,5)),("→",(RightAssociative,1)),("↔",(RightAssociative,1)),("∈",(NotAssociative,5)),("∧",(RightAssociative,4)),("∨",(RightAssociative,3)),
     ("≥",(NotAssociative,5)),
     ("≠",(NotAssociative,5)),("∉",(NotAssociative,5))]


--The Int is it's precedence number.
binaryOpData :: Map Text (Associativity, Int)
binaryOpData = Data.Map.fromList binaryOpInData


instance SubexpDeBr ObjDeBr where
    toSubexpParseTree :: ObjDeBr -> Map PropDeBr [Int]  -> SubexpParseTree
    toSubexpParseTree obj dict = case obj of
        Integ i -> (Atom . pack . show) i
        Constant c -> Atom c
        Hilbert p -> case Data.Map.lookup (Exists p) dict of
            Just idxs -> HilbertShort idxs
            Nothing -> Binding "ε" (boundDepthPropDeBr p) (toSubexpParseTree p dict)
        Bound i -> Atom $ "𝑥" <> showIndexAsSubscript i
        V i -> Atom $ "𝑣" <> showIndexAsSubscript i
        X i -> Atom $ "X" <> showIndexAsSubscript i
        Pair a b -> Tuple [toSubexpParseTree a dict,toSubexpParseTree b dict]
        


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
boundDepthPropDeBr p = case p of
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
        o1 :==: o2 -> BinaryOp "≠" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)  
        In o1 o2 -> BinaryOp "∉" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)      
        _ -> UnaryOp "¬" (toSubexpParseTree q dict)
      (:&&:) a b -> BinaryOp "∧" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:||:) a b -> BinaryOp "∨" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:->:)  a b -> BinaryOp "→" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:<->:) a b -> BinaryOp "↔"(toSubexpParseTree a dict) (toSubexpParseTree b dict)
      (:==:) a b -> BinaryOp "=" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      In a b -> BinaryOp "∈" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      Forall a -> Binding "∀" (boundDepthPropDeBr a) (toSubexpParseTree a dict)
      Exists a -> ebuild a
      (:>=:) a b -> BinaryOp "≥" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      F -> Atom "⊥"
    where
        ebuild a = case a of  
            p :&&: q -> if Forall (pDecremented :->: Bound (depth - 1):==: Bound depth) == q then
                            Binding "∃!" (depth-1) (toSubexpParseTree pDecremented dict)
                        else
                            error (show pDecremented)
                            -- defaultP
                where
                    pDecremented = boundDecrementPropDeBr depth p
            _ -> defaultP
         where
           defaultP = Binding "∃" depth (toSubexpParseTree a dict)
           depth = boundDepthPropDeBr a     
 





showSubexpParseTree :: SubexpParseTree -> Text
showSubexpParseTree sub = case sub of
    UnaryOp opSymb sub1 ->
           opSymb
        <> case sub1 of
              UnaryOp _ _ -> showSubexpParseTree sub1
              BinaryOp {} -> "(" <>  showSubexpParseTree sub1 <> ")"
              Binding {} -> showSubexpParseTree sub1
              Atom _ -> showSubexpParseTree sub1
              HilbertShort idx -> showSubexpParseTree sub1
              Tuple as -> showSubexpParseTree sub1
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
              Atom _ -> showSubexpParseTree sub1
              HilbertShort idx -> showSubexpParseTree sub1
              Tuple as -> showSubexpParseTree sub1
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
               Atom _ -> showSubexpParseTree sub2
               HilbertShort idx -> showSubexpParseTree sub2
               Tuple as -> showSubexpParseTree sub2
    Binding quant idx sub1 -> quant <> "𝑥" <> showIndexAsSubscript idx <> "(" <> showSubexpParseTree sub1 <> ")" 
    Atom text -> text
    HilbertShort idx -> "ε" <> showHierarchalIdxAsSubscript idx
    Tuple as -> "(" <> Data.Text.concat (intersperse "," $ Prelude.map showSubexpParseTree as ) <> ")"
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
   


objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx =
    case obj of
        Integ num -> False
        Constant const -> False
        Hilbert p -> propDeBrBoundVarInside p idx
        Bound i -> idx == i
        V i -> False
        Pair a b -> objDeBrBoundVarInside a idx || objDeBrBoundVarInside b idx



objDeBrX0Inside :: ObjDeBr -> Bool
objDeBrX0Inside obj =
    case obj of
        Integ num -> False
        Constant const -> False
        Hilbert p -> propDeBrX0Inside p
        Bound i -> False
        V i -> False
        X idx | idx == 0 -> True
              | otherwise -> False
        Pair a b -> objDeBrX0Inside a|| objDeBrX0Inside b


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

propDeBrX0Inside :: PropDeBr -> Bool
propDeBrX0Inside prop = case prop of
    Neg p -> propDeBrX0Inside p
    (:&&:) p1 p2 -> propDeBrX0Inside p1 || propDeBrX0Inside p2
    (:||:) p1 p2 -> propDeBrX0Inside p1 || propDeBrX0Inside p2
    (:->:) p1 p2 -> propDeBrX0Inside p1 || propDeBrX0Inside p2
    (:<->:) p1 p2 -> propDeBrX0Inside p1 || propDeBrX0Inside p2
    (:==:) o1 o2 -> objDeBrX0Inside o1  || objDeBrX0Inside o2
    In o1 o2 -> objDeBrX0Inside o1 || objDeBrX0Inside o2
    Forall p -> propDeBrX0Inside p
    Exists p -> propDeBrX0Inside p
    (:>=:) o1 o2 -> objDeBrX0Inside o1 || objDeBrX0Inside o2
    false -> False




objDeBrSubX0 :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubX0 boundvarOffsetThreshold obj t = case obj of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert (propDeBrSubX0 (calcBVOThreshold p) p t)                            
    Bound idx
                | idx >= boundvarOffsetThreshold -> Bound (idx + termDepth)
                | otherwise -> Bound idx
           --      | idx==boundVarIdx -> t
           --      | idx >= boundvarOffsetThreshold -> Bound (idx + termDepth)
           --      | idx < boundVarIdx -> Bound idx

    V idx -> V idx
    X idx 
        | idx == 0 -> t
        | otherwise -> X idx
    Pair o1 o2 -> Pair (objDeBrSubX0 boundvarOffsetThreshold o1 t) (objDeBrSubX0 boundvarOffsetThreshold o2 t)
  where
        termDepth = boundDepthObjDeBr t
        calcBVOThreshold p = if propDeBrX0Inside p then
                                  boundDepthPropDeBr p
                             else boundvarOffsetThreshold






propDeBrSubX0 :: Int -> PropDeBr -> ObjDeBr -> PropDeBr
propDeBrSubX0 boundvarOffsetThreshold prop t = case prop of
    Neg p -> Neg (propDeBrSubX0 boundvarOffsetThreshold p t)
    (:&&:) p1 p2 ->  (:&&:) (propDeBrSubX0 boundvarOffsetThreshold p1 t) (propDeBrSubX0 boundvarOffsetThreshold p2 t) 
    (:||:) p1 p2 ->  (:||:) (propDeBrSubX0 boundvarOffsetThreshold p1 t) (propDeBrSubX0 boundvarOffsetThreshold p2 t) 
    (:->:) p1 p2 ->  (:->:) (propDeBrSubX0 boundvarOffsetThreshold p1 t) (propDeBrSubX0 boundvarOffsetThreshold p2 t)
    (:<->:) p1 p2 ->  (:<->:) (propDeBrSubX0 boundvarOffsetThreshold p1 t) (propDeBrSubX0 boundvarOffsetThreshold p2 t)
    (:==:) o1 o2 -> (:==:) (objDeBrSubX0 boundvarOffsetThreshold o1 t) (objDeBrSubX0 boundvarOffsetThreshold o2 t)   
    In o1 o2 -> In (objDeBrSubX0 boundvarOffsetThreshold o1 t) (objDeBrSubX0 boundvarOffsetThreshold o2 t)  
    Forall p -> Forall (propDeBrSubX0 (calcBVOThreshold p) p t)
    Exists p -> Exists (propDeBrSubX0 (calcBVOThreshold p) p t)
    (:>=:) o1 o2 -> (:>=:) (objDeBrSubX0 boundvarOffsetThreshold o1 t) (objDeBrSubX0 boundvarOffsetThreshold o2 t)
    F -> F
  where
          calcBVOThreshold p = if propDeBrX0Inside p then
                                      boundDepthPropDeBr p
                               else boundvarOffsetThreshold 


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
boundExpToFunc p = propDeBrSubX0 calcBVOThreshold template
           where 
                 boundDepth = boundDepthPropDeBr p
                 template = propDeBrSubBoundVarToX0 boundDepth p 
                 calcBVOThreshold = if propDeBrBoundVarInside p boundDepth then
                                      boundDepth
                                  else 
                                      boundDepth + 1


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
    substX0 p = propDeBrSubX0 (calcBVOThreshold p) p
           where boundVarIdx = boundDepthPropDeBr
                 calcBVOThreshold p = if propDeBrX0Inside p then
                                      boundDepthPropDeBr p
                                  else 
                                      boundDepthPropDeBr p + 1

    

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
                     <> (pack .show) constName
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
   
neq :: ObjDeBr -> ObjDeBr -> PropDeBr
neq a b = Neg $ a :==: b

infix 4 `neq`

nin :: ObjDeBr -> ObjDeBr -> PropDeBr
nin a b = Neg $ a `In` b

infix 4 `nin`

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

relDomain :: ObjDeBr -> ObjDeBr
relDomain s = hX 0 $ aX 1 (aX 2 $ Pair (X 1) (X 2) `In` s :->: X 1 `In` X 0) 

isFunction :: ObjDeBr -> PropDeBr
isFunction t = isRelation t :&&: 
          aX 0 ( X 0 `In` relDomain t :->: eXBang 1 $ Pair (X 0) (X 1) `In` t)

--propIsFuncOnSet :: ObjDeBr -> PropDeBr -> PropDeBr
--propIsFuncOnSet t p = 


--(isRelation (X 0) :&&: 
--                            (aX 1 $ (X 1) `In` relDomain (X 0) :->: eBangX 2 
                            


instance ZFC.LogicSent PropDeBr ObjDeBr where
    emptySetAxiom :: PropDeBr
    emptySetAxiom = eX 0 $ Neg $ aX 1 $ X 1 `In` X 0
    specAxiom :: ObjDeBr -> PropDeBr -> PropDeBr
    -- specification axiom composed from term t and predicate P(x)
    specAxiom t p = eX 0 $ aX 1 $ X 1 `In` X 0 :<->: p :&&: X 1 `In` t
    replaceAxiom:: ObjDeBr -> PropDeBr -> PropDeBr
    replaceAxiom t p = aX 0 (X 0 `In` t :->: eXBang 1 p)
                         :->: eX 2 (aX 1 (X 1 `In` X 2 :<->: eX 0 (X 0 `In` t :&&: p)))  
      
 



 





