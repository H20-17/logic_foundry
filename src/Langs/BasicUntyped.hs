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
    eX, hX, aX
) where
import Control.Monad ( unless )
import Data.List (intersperse)
import Data.Text (Text, pack, unpack,concat, lines,intercalate)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
import Data.Set(Set)
import qualified Data.Set as Set (fromList,insert,member)
import Control.Applicative ( Alternative((<|>)) )

import Control.Monad.Except ( MonadError(throwError) )

import Internal.StdPattern
    ( 
      PrfStdStep(..),
      StdPrfPrintMonad(..),
      StdPrfPrintMonadFrame(..),
      TypeableTerm(..),
      TypedSent(..) )
import Control.Exception (SomeException)
import qualified RuleSets.Internal.PropLogic as PL
import qualified RuleSets.Internal.PredLogic as PREDL
import GHC.Conc (numCapabilities)
import Distribution.TestSuite (TestInstance(name))


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
    deriving (Eq, Ord)


infixr 3 :&&:
infixr 2 :||:
infixr 0 :->:
infixr 0 :<->:
infix  4 :==:
infix  4 `In`
infix  4 :>=:

inSet :: ObjDeBr -> ObjDeBr -> PropDeBr
inSet = In

infix 4 `inSet`

data SubexpParseTree where
    BinaryOp :: Text -> SubexpParseTree -> SubexpParseTree -> SubexpParseTree
    UnaryOp :: Text -> SubexpParseTree ->SubexpParseTree
    Binding :: Text -> Int -> SubexpParseTree -> SubexpParseTree
    Atom :: Text -> SubexpParseTree



class SubexpDeBr sub where
    toSubexpParseTree :: sub -> SubexpParseTree




binaryOpInData :: [(Text,(Associativity,Int))]
binaryOpInData = [("=",(NotAssociative,5)),("→",(RightAssociative,1)),("↔",(RightAssociative,1)),("∈",(NotAssociative,5)),("∧",(RightAssociative,4)),("∨",(RightAssociative,3)),
     ("≥",(NotAssociative,5))]


--The Int is it's precedence number.
binaryOpData :: Map Text (Associativity, Int)
binaryOpData = Data.Map.fromList binaryOpInData


instance SubexpDeBr ObjDeBr where
    toSubexpParseTree :: ObjDeBr -> SubexpParseTree
    toSubexpParseTree obj = case obj of
        Integ i -> (Atom . pack . show) i
        Constant c -> Atom c
        Hilbert p -> Binding "ε" (boundDepthPropDeBr p) (toSubexpParseTree p)
        Bound i -> Atom $ "𝑥" <> showIndexAsSubscript i
        V i -> Atom $ "𝑣" <> showIndexAsSubscript i
        X i -> Atom $ "X" <> showIndexAsSubscript i     


instance SubexpDeBr PropDeBr where
  toSubexpParseTree :: PropDeBr -> SubexpParseTree
  toSubexpParseTree p = case p of
    Neg q -> UnaryOp "¬" (toSubexpParseTree q)
    (:&&:) a b -> BinaryOp "∧" (toSubexpParseTree a) (toSubexpParseTree b)
    (:||:) a b -> BinaryOp "∨" (toSubexpParseTree a) (toSubexpParseTree b)
    (:->:)  a b -> BinaryOp "→" (toSubexpParseTree a) (toSubexpParseTree b)
    (:<->:) a b -> BinaryOp "↔"(toSubexpParseTree a) (toSubexpParseTree b)
    (:==:) a b -> BinaryOp "=" (toSubexpParseTree a) (toSubexpParseTree b)
    In a b -> BinaryOp "∈" (toSubexpParseTree a) (toSubexpParseTree b)
    Forall a -> Binding "∀" (boundDepthPropDeBr a) (toSubexpParseTree a)
    Exists a -> Binding "∃" (boundDepthPropDeBr a) (toSubexpParseTree a)
    (:>=:) a b -> BinaryOp "≥" (toSubexpParseTree a) (toSubexpParseTree b)

showSubexpParseTree :: SubexpParseTree -> Text
showSubexpParseTree sub = case sub of
    UnaryOp opSymb sub1 ->
           opSymb
        <> case sub1 of
              UnaryOp _ _ -> showSubexpParseTree sub1
              BinaryOp {} -> "(" <>  showSubexpParseTree sub1 <> ")"
              Binding {} -> showSubexpParseTree sub1
              Atom _ -> showSubexpParseTree sub1
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
    Binding quant idx sub1 -> quant <> "𝑥" <> showIndexAsSubscript idx <> "(" <> showSubexpParseTree sub1 <> ")" 
    Atom text -> text       
  where
    assoc opSymb = fst $ binaryOpData!opSymb
    prec opSymb = snd $ binaryOpData!opSymb


instance Show ObjDeBr where
    show :: ObjDeBr -> String
    show = unpack . showSubexpParseTree . toSubexpParseTree                         


instance Show PropDeBr where
    show :: PropDeBr -> String
    show = unpack . showSubexpParseTree . toSubexpParseTree
           






data ObjDeBr where
      Integ :: Int -> ObjDeBr
      Constant :: Text -> ObjDeBr
      Hilbert :: PropDeBr -> ObjDeBr
      Bound :: Int -> ObjDeBr
      V :: Int ->ObjDeBr
      X :: Int -> ObjDeBr
   deriving (Eq, Ord)








data DeBrSe where
    ObjDeBrSeConstNotDefd :: Text -> DeBrSe
    ObjDeBrBoundVarIdx :: Int -> DeBrSe
    ObjDeBrFreeVarIdx :: Int -> DeBrSe
    ObjDeBrUnconsumedX :: Int -> DeBrSe
   deriving Show


boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     Integ num -> 0
     Constant name -> 0
     Hilbert prop -> boundDepthPropDeBr prop + 1
     Bound idx -> 0
     V idx -> 0
     X idx -> 0



checkSanityObjDeBr :: ObjDeBr -> Int -> Set Text -> Set Int -> Maybe DeBrSe

checkSanityObjDeBr obj varStackHeight constSet boundSet = case obj of
     Integ num -> Nothing
     Constant name -> if name `Set.member` constSet then
                           Nothing
                       else
                           (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> checkSanityPropDeBr prop varStackHeight constSet 
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
     X idx -> return $ ObjDeBrUnconsumedX idx   
 


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

checkSanityPropDeBr :: PropDeBr -> Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityPropDeBr prop freevarStackHeight consts boundVars = 
      case prop of
        Neg p -> checkSanityPropDeBr p freevarStackHeight consts boundVars
        (:&&:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:||:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:->:)  p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        (:<->:) p1 p2 -> checkSanityPropDeBr p1 freevarStackHeight consts boundVars
                         <|> checkSanityPropDeBr p2 freevarStackHeight consts boundVars
        In o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars
        (:==:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars
        Forall prop -> checkSanityPropDeBr prop freevarStackHeight consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        Exists prop -> checkSanityPropDeBr prop freevarStackHeight consts
                            (Set.insert (boundDepthPropDeBr prop) boundVars )
        (:>=:) o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight consts boundVars
                         <|> checkSanityObjDeBr o2 freevarStackHeight consts boundVars




instance TypeableTerm ObjDeBr Text () DeBrSe where
 
     getTypeTerm :: ObjDeBr -> [()] -> Map Text () -> Either DeBrSe ()
     getTypeTerm term vs constDict = 
         maybe (return ()) throwError (checkSanityObjDeBr term (Prelude.length vs) (keysSet constDict) mempty)
     const2Term :: Text -> ObjDeBr
     const2Term = Constant
     free2Term :: Int -> ObjDeBr
     free2Term = V


instance TypedSent  Text () DeBrSe PropDeBr where
    checkSanity :: [()] -> PropDeBr -> Map Text () -> Maybe DeBrSe
    checkSanity freeVarStack prop constDict = checkSanityPropDeBr
        prop (Prelude.length freeVarStack) (keysSet constDict) mempty



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
  parseDis :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
  parseDis p = case p of
                 (:||:) p1 p2 -> Just(p1,p2)
                 _ -> Nothing

objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx =
    case obj of
        Integ num -> False
        Constant const -> False
        Hilbert p -> propDeBrBoundVarInside p idx
        Bound i -> idx == i
        V i -> False



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


objDeBrSub :: Int -> Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSub boundVarIdx boundvarOffsetThreshold obj t = case obj of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)                            
    Bound idx 
                 | idx==boundVarIdx -> t
                 | idx >= boundvarOffsetThreshold -> Bound (idx + termDepth)
                 | idx < boundVarIdx -> Bound idx

    V idx -> V idx
  where
        termDepth = boundDepthObjDeBr t
        calcBVOThreshold p = if propDeBrBoundVarInside p boundVarIdx then
                                  boundDepthPropDeBr p
                             else boundvarOffsetThreshold

propDeBrSub :: Int -> Int -> PropDeBr -> ObjDeBr -> PropDeBr
propDeBrSub boundVarIdx boundvarOffsetThreshold prop t = case prop of
    Neg p -> Neg (propDeBrSub boundVarIdx boundvarOffsetThreshold p t)
    (:&&:) p1 p2 ->  (:&&:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t) 
    (:||:) p1 p2 ->  (:||:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t) 
    (:->:) p1 p2 ->  (:->:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t)
    (:<->:) p1 p2 ->  (:<->:) (propDeBrSub boundVarIdx boundvarOffsetThreshold p1 t) (propDeBrSub boundVarIdx boundvarOffsetThreshold p2 t)
    (:==:) o1 o2 -> (:==:) (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)   
    In o1 o2 -> In (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)  
    Forall p -> Forall (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)
    Exists p -> Exists (propDeBrSub boundVarIdx (calcBVOThreshold p) p t)
    (:>=:) o1 o2 -> (:>=:) (objDeBrSub boundVarIdx boundvarOffsetThreshold o1 t) (objDeBrSub boundVarIdx boundvarOffsetThreshold o2 t)
  where
          calcBVOThreshold p = if propDeBrBoundVarInside p boundVarIdx then
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


boundExpToFunc :: PropDeBr -> ObjDeBr -> PropDeBr
boundExpToFunc p = propDeBrSub (boundVarIdx p) (calcBVOThreshold p) p
           where boundVarIdx = boundDepthPropDeBr
                 calcBVOThreshold p = if propDeBrBoundVarInside p (boundVarIdx p) then
                                      boundDepthPropDeBr p
                                  else 
                                      boundDepthPropDeBr p + 1


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




showPropDeBrStep :: [Bool] -> [Int] ->Int -> Bool -> Bool -> PrfStdStepPredDeBr -> Text
showPropDeBrStep contextFrames index lineNum notFromMonad isLastLine step =
        contextFramesShown
          <> showIndex index
                <> (if (not . Prelude.null) index then "." else "")
                <> (pack . show) lineNum
                <> ": "
          <> showStepInfo
      where
        contextFramesShown = Data.Text.concat (Prelude.map mapBool contextFrames)
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
        showStepInfo = 
          case step of
             PrfStdStepStep prop justification depends -> 
                  (pack . show) prop
                <> "    "
                <> justification
                <> showIndices depends
                <> qed
             PrfStdStepLemma prop mayWhereProven ->
                   (pack . show) prop
                <> "    LEMMA"
                <> maybe "" (("[⬅ " <>) . (<> "]"). showIndexDepend) mayWhereProven
                <> qed
             PrfStdStepConst constName _ mayWhereDefined ->
                   "Const "
                <> (pack .show) constName
                <> "    CONSTDEF"
                <> maybe "" (("[⬅ " <>) . (<> "]"). showIndexDepend) mayWhereDefined
             PrfStdStepTheorem prop steps ->
                   (pack . show) prop
                <> "    THEOREM"
                <> qed
                <> showSubproofF steps True
             PrfStdStepSubproof prop subproofName steps ->
                   (pack . show) prop
                <> "    "
                <> subproofName
                <> qed
                <> showSubproofF steps False
             PrfStdStepTheoremM prop  ->
                   (pack . show) prop
                <> "    ALGORITHMIC_THEOREM"
                <> qed
             PrfStdStepFreevar index _ ->
                   "FreeVar 𝑣"
                <> showIndexAsSubscript index
                <> "    VARDEF"  
             PrfStdStepFakeConst constName _ ->
                "Const "
                     <> (pack .show) constName
                <> "    FAKE_CONST"
             PrfStdStepRemark text ->   "REMARK"
                                      <> qed
                                      <> (if text == "" then "" else "\n" <> contextFramesShown <> "║") 
                                      <> intercalate ("\n" <> contextFramesShown <> "║") (Data.Text.lines text)
                                      <> "\n"
                                      <> contextFramesShown
                                      <> "╚"
             where
 
                showSubproofF steps isTheorem = 
                    if notFromMonad then
                          "\n"
                       <> showPropDeBrSteps (contextFrames <> [isTheorem]) newIndex 0 notFromMonad steps
--                       <> " ◻"
                       <> "\n"
                       <> Data.Text.concat (Prelude.map mapBool contextFrames) 
                               <> cornerFrame
                      else ""
                     where
                        newIndex = if isTheorem then [] else index <> [lineNum]
                        cornerFrame = if isTheorem then
                                 "┗"
                              else
                                  "└"
                qed = if notFromMonad && isLastLine && (not . null) contextFrames then " ◻" else ""


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
  printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep PropDeBr Text ()] -> IO ()
  printSteps contextFrames idx stepStart steps = do
    let outputTxt = showPropDeBrSteps contextFrames idx stepStart False steps
    (putStrLn . unpack) outputTxt



instance StdPrfPrintMonad PropDeBr Text () (Either SomeException) where
  printSteps :: [Bool] -> [Int] -> Int -> [PrfStdStep PropDeBr Text ()] -> Either SomeException ()
  printSteps _ _ _ _ = return ()



showPropDeBrSteps :: [Bool] -> [Int] -> Int -> Bool -> [PrfStdStepPredDeBr] -> Text
showPropDeBrSteps contextFrames index stepStart notFromMonad steps = fst foldResult
    where 
        foldResult = Prelude.foldl f ("", stepStart) steps
           where
             f (accumText,stepNum) step = (accumText 
                                             <> showPropDeBrStep contextFrames index stepNum notFromMonad isLastLine step <> eol,
                                           stepNum+1)
                  where
                    isLastLine = stepNum == stepStart + length steps - 1
                    eol = if isLastLine then "" else "\n"



showPropDeBrStepsBase :: [PrfStdStepPredDeBr] -> Text
showPropDeBrStepsBase = showPropDeBrSteps [] [] 0 True


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




eX :: Int -> PropDeBr -> PropDeBr
eX idx p = Exists $ xsubPropDeBr p idx (boundDepthPropDeBr p)

aX :: Int -> PropDeBr -> PropDeBr
aX idx p = Forall $ xsubPropDeBr p idx (boundDepthPropDeBr p)

hX :: Int -> PropDeBr -> ObjDeBr
hX idx p = Hilbert (xsubPropDeBr p idx (boundDepthPropDeBr p))



 





