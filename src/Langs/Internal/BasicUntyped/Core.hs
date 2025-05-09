module Langs.Internal.BasicUntyped.Core (
    ObjDeBr(..),
    PropDeBr(..),
    DeBrSe(..),
    PrfStdStepPredDeBr,
    PropErrDeBr,
    PropRuleDeBr,
    PredErrDeBr,
    PredRuleDeBr,
    eX, hX, aX,
    eXBang,
    (./=.),
    nIn,
    boundDepthObjDeBr,
    boundDepthPropDeBr,
    objDeBrSubX,
    parseHilbert,
    parseIn,
    parseBound,
    objDeBrBoundVarInside,
    parseForall2,
    parseBiconditional,
    parseConjunction,
    propDeBrBoundVarInside,
    parseEqual,
    objDeBrSubXs,
    parseConst,
    parseV,
    parseX,
    parseInteg,
    parseImplication,
    parseNegation,
    parseExists,
    parseDisjunction,
    parseLTE,
    parseFalsum,
    objDeBrSubXInt,
    propDeBrSubXInt,
    hXInt,
    propDeBrSubXs,
    multiEx,
    multiAx,
    propDeBrSubX,
    parseIntPlus,
    parseIntNeg,
    parseIntMult,
    parseIntSet,
    parseEmptySet,
    eXInt,
    aXInt

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
import RuleSets.ZFC (specification,parseMemberOf,memberOf)
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS )
import Text.XHtml (sub)
import qualified Internal.StdPattern
import Data.Maybe (isJust)
import GHC.IO.BufferedIO (BufferedIO(emptyWriteBuffer))


data ObjDeBr where
    Integ :: Int -> ObjDeBr
    Constant :: Text -> ObjDeBr
    Hilbert :: PropDeBr -> ObjDeBr
    Bound :: Int -> ObjDeBr
    V :: Int ->ObjDeBr
    X :: Int -> ObjDeBr
    XInternal :: Int -> ObjDeBr
    (:+:) :: ObjDeBr -> ObjDeBr -> ObjDeBr
    Intneg :: ObjDeBr -> ObjDeBr
    (:*:) :: ObjDeBr -> ObjDeBr -> ObjDeBr
    IntSet :: ObjDeBr
    EmptySet :: ObjDeBr
    deriving (Eq, Ord, Show)

infixl 6 :+:
infixl 7 :*:


data PropDeBr where
      Neg :: PropDeBr -> PropDeBr
      (:&&:)  :: PropDeBr -> PropDeBr -> PropDeBr
      (:||:) :: PropDeBr -> PropDeBr -> PropDeBr
      (:->:)  :: PropDeBr -> PropDeBr -> PropDeBr
      (:<->:) :: PropDeBr -> PropDeBr -> PropDeBr
      (:==:) :: ObjDeBr -> ObjDeBr -> PropDeBr
      In :: ObjDeBr -> ObjDeBr -> PropDeBr
      Forall :: PropDeBr -> PropDeBr
      Exists :: PropDeBr -> PropDeBr
      (:<=:) :: ObjDeBr -> ObjDeBr -> PropDeBr
      F :: PropDeBr
    deriving (Show, Eq, Ord)


infixr 3 :&&:
infixr 2 :||:
infixr 0 :->:
infixr 0 :<->:
infix  4 :==:
infix  4 `In`
infix  4 :<=:



objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx = case obj of
    Integ num -> False
    Constant const -> False
    Hilbert p -> propDeBrBoundVarInside p idx
    Bound i -> idx == i
    V i -> False
    X i -> False
    (o1 :+: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    Intneg o1     -> objDeBrBoundVarInside o1 idx
    (o1 :*: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    IntSet -> False
    EmptySet -> False



swapBoundIndexProp :: Int -> Int -> PropDeBr -> PropDeBr
swapBoundIndexProp fromIdx toIdx p = case p of
    Neg q -> Neg (swapBoundIndexProp fromIdx toIdx q)
    (p1 :&&: p2) -> swapBoundIndexProp fromIdx toIdx p1 :&&: swapBoundIndexProp fromIdx toIdx p2
    (p1 :||: p2) -> swapBoundIndexProp fromIdx toIdx p1 :||: swapBoundIndexProp fromIdx toIdx p2
    (p1 :->: p2) -> swapBoundIndexProp fromIdx toIdx p1 :->: swapBoundIndexProp fromIdx toIdx p2
    (p1 :<->: p2) -> swapBoundIndexProp fromIdx toIdx p1 :<->: swapBoundIndexProp fromIdx toIdx p2
    (o1 :==: o2) -> swapBoundIndexObj fromIdx toIdx o1 :==: swapBoundIndexObj fromIdx toIdx o2
    In o1 o2 -> In (swapBoundIndexObj fromIdx toIdx o1) (swapBoundIndexObj fromIdx toIdx o2)
    Forall q -> Forall (swapBoundIndexProp fromIdx toIdx q)
    Exists q -> Exists (swapBoundIndexProp fromIdx toIdx q)
    (o1 :<=: o2) -> swapBoundIndexObj fromIdx toIdx o1 :<=: swapBoundIndexObj fromIdx toIdx o2
    F -> F



swapBoundIndexObj :: Int -> Int -> ObjDeBr -> ObjDeBr
swapBoundIndexObj fromIdx toIdx o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapBoundIndexProp fromIdx toIdx p)
    Bound i -> if i == fromIdx then Bound toIdx else Bound i
    V i -> V i
    X i -> X i
    XInternal i -> XInternal i
    (o1 :+: o2) -> swapBoundIndexObj fromIdx toIdx o1 :+: swapBoundIndexObj fromIdx toIdx o2
    Intneg o1   -> Intneg (swapBoundIndexObj fromIdx toIdx o1)
    (o1 :*: o2) -> swapBoundIndexObj fromIdx toIdx o1 :*: swapBoundIndexObj fromIdx toIdx o2
    IntSet -> IntSet
    EmptySet -> EmptySet



boundDepthObjDeBrX :: Int -> Int -> ObjDeBr -> Int
boundDepthObjDeBrX targetIdx substitutionDepth obj = case obj of
    Integ num -> 0
    Constant name -> 0
    Hilbert prop -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth prop
    Bound idx -> 0
    V idx -> 0
    X idx -> if idx == targetIdx then substitutionDepth else 0
    XInternal idx -> 0
    (o1 :+: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    Intneg o1     -> boundDepthObjDeBrX targetIdx substitutionDepth o1
    (o1 :*: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    IntSet -> 0
    EmptySet -> 0



boundDepthPropDeBrX :: Int -> Int -> PropDeBr -> Int
boundDepthPropDeBrX targetIdx substitutionDepth prop = case prop of
    Neg p -> boundDepthPropDeBrX targetIdx substitutionDepth p
    (p1 :&&: p2) -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (p1 :||: p2) -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (p1 :->: p2) -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (p1 :<->: p2) -> max (boundDepthPropDeBrX targetIdx substitutionDepth p1) (boundDepthPropDeBrX targetIdx substitutionDepth p2)
    (o1 :==: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    In o1 o2 -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    Forall p -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth p
    Exists p -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth p
    (o1 :<=: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2)
    F -> 0




boundDepthObjDeBrXInt :: Int -> Int -> ObjDeBr -> Int
boundDepthObjDeBrXInt targetIdx substitutionDepth obj = case obj of
    Integ num -> 0
    Constant name -> 0
    Hilbert prop -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth prop
    Bound idx -> 0
    V idx -> 0
    X idx -> 0
    XInternal idx -> if idx == targetIdx then substitutionDepth else 0
    (o1 :+: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    Intneg o1     -> boundDepthObjDeBrXInt targetIdx substitutionDepth o1
    (o1 :*: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    IntSet -> 0
    EmptySet -> 0


boundDepthPropDeBrXInt :: Int -> Int -> PropDeBr -> Int
boundDepthPropDeBrXInt targetIdx substitutionDepth prop = case prop of
    Neg p -> boundDepthPropDeBrXInt targetIdx substitutionDepth p
    (p1 :&&: p2) -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (p1 :||: p2) -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (p1 :->: p2) -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (p1 :<->: p2) -> max (boundDepthPropDeBrXInt targetIdx substitutionDepth p1) (boundDepthPropDeBrXInt targetIdx substitutionDepth p2)
    (o1 :==: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    In o1 o2 -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    Forall p -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth p
    Exists p -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth p
    (o1 :<=: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2)
    F -> 0


parseHilbert :: ObjDeBr -> Maybe (PropDeBr, Int)
parseHilbert subexp =
  case subexp of
     Hilbert p
                -> Just (p, pDepth)
            where
             pDepth = boundDepthPropDeBr p
     _ -> Nothing


parseForall2 :: PropDeBr -> Maybe (PropDeBr, Int)
parseForall2 subexp =
  case subexp of
     Forall p
                -> Just (p, pDepth)
            where
             pDepth = boundDepthPropDeBr p
     _ -> Nothing


parseInteg :: ObjDeBr -> Maybe Int
parseInteg subexp = case subexp of
    Integ i -> Just i
    _ -> Nothing

parseIntSet :: ObjDeBr -> Maybe ()
parseIntSet subexp = case subexp of
    IntSet -> Just ()
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




parseX :: ObjDeBr -> Maybe Int
parseX subexp = case subexp of
    X i -> Just i
    _ -> Nothing


parseEqual :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseEqual subexp = case subexp of
    (:==:) ls rs -> Just (ls,rs)
    _           -> Nothing



boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     Integ num -> 0
     Constant name -> 0
     Hilbert prop -> boundDepthPropDeBr prop + 1
     Bound idx -> 0
     V idx -> 0
     X idx -> 0
     XInternal idx -> 0
     (o1 :+: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
     Intneg o1     -> boundDepthObjDeBr o1
     (o1 :*: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
     IntSet ->  0



boundDepthPropDeBr :: PropDeBr -> Int
boundDepthPropDeBr prop = case prop of
    Neg p -> boundDepthPropDeBr p
    (p1 :&&: p2) -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (p1 :||: p2) -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (p1 :->: p2) -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    (p1 :<->: p2) -> max (boundDepthPropDeBr p1) (boundDepthPropDeBr p2)
    In o1 o2 -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    (o1 :==: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
    Forall p -> boundDepthPropDeBr p + 1
    Exists p -> boundDepthPropDeBr p + 1
    (o1 :<=: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2)
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


parseNegation :: PropDeBr -> Maybe PropDeBr
parseNegation p = case p of
    Neg q -> Just q
    _ -> Nothing


parseDisjunction :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
parseDisjunction p = case p of
    (a :||: b) -> Just (a,b)
    _ -> Nothing

parseExists :: PropDeBr -> Maybe (PropDeBr, Int)
parseExists p = case p of
    Exists inner -> Just (inner, boundDepthPropDeBr inner)
    _ -> Nothing


parseBiconditional :: PropDeBr -> Maybe (PropDeBr, PropDeBr)
parseBiconditional p = case p of
    (a :<->: b) -> Just (a,b)
    _ -> Nothing


parseLTE :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseLTE p = case p of
    (a :<=: b) -> Just (a, b)
    _ -> Nothing


parseFalsum :: PropDeBr -> Maybe ()
parseFalsum p = case p of
    F -> Just ()
    _ -> Nothing


parseIntPlus :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseIntPlus obj = case obj of
    (o1 :+: o2) -> Just (o1, o2)
    _ -> Nothing

parseIntNeg :: ObjDeBr -> Maybe ObjDeBr
parseIntNeg obj = case obj of
    Intneg o1 -> Just o1
    _ -> Nothing

parseIntMult :: ObjDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseIntMult obj = case obj of
    (o1 :*: o2) -> Just (o1, o2)
    _ -> Nothing


parseEmptySet :: ObjDeBr -> Maybe ()
parseEmptySet obj = case obj of
    EmptySet -> Just ()
    _ -> Nothing


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
     Constant name -> if name `Set.member` constSet then Nothing else (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> checkSanityPropDeBr prop varStackHeight tmpltVarIndices constSet (Set.insert (boundDepthPropDeBr prop) boundSet )
     Bound idx -> if idx `Set.member` boundSet then Nothing else (return . ObjDeBrBoundVarIdx) idx
     V idx -> if idx >= 0 && idx < varStackHeight then Nothing else (return . ObjDeBrFreeVarIdx) idx
     X idx -> if idx >= 0 && idx `Set.member` tmpltVarIndices then Nothing else (return . ObjDeBrTemplateVarIdx) idx
     (o1 :+: o2) -> checkSanityObjDeBr o1 varStackHeight tmpltVarIndices constSet boundSet <|> checkSanityObjDeBr o2 varStackHeight tmpltVarIndices constSet boundSet
     Intneg o1     -> checkSanityObjDeBr o1 varStackHeight tmpltVarIndices constSet boundSet
     (o1 :*: o2) -> checkSanityObjDeBr o1 varStackHeight tmpltVarIndices constSet boundSet <|> checkSanityObjDeBr o2 varStackHeight tmpltVarIndices constSet boundSet
     IntSet -> Nothing
     EmptySet -> Nothing



checkSanityPropDeBr :: PropDeBr -> Int -> Set Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityPropDeBr prop freevarStackHeight tmpltVarIndices consts boundVars =
      case prop of
        Neg p -> checkSanityPropDeBr p freevarStackHeight tmpltVarIndices consts boundVars
        (p1 :&&: p2) -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        (p1 :||: p2) -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        (p1 :->: p2) -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        (p1 :<->: p2) -> checkSanityPropDeBr p1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityPropDeBr p2 freevarStackHeight tmpltVarIndices consts boundVars
        In o1 o2 -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars
        (o1 :==: o2) -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars
        Forall propInner -> checkSanityPropDeBr propInner freevarStackHeight tmpltVarIndices consts (Set.insert (boundDepthPropDeBr propInner) boundVars )
        Exists propInner -> checkSanityPropDeBr propInner freevarStackHeight tmpltVarIndices consts (Set.insert (boundDepthPropDeBr propInner) boundVars )
        (o1 :<=: o2) -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars
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








propDeBrBoundVarInside :: PropDeBr -> Int -> Bool
propDeBrBoundVarInside prop idx = case prop of
    Neg p -> propDeBrBoundVarInside p idx
    (p1 :&&: p2) -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (p1 :||: p2) -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (p1 :->: p2) -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (p1 :<->: p2) -> propDeBrBoundVarInside p1 idx || propDeBrBoundVarInside p2 idx
    (o1 :==: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    In o1 o2 -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    Forall p -> propDeBrBoundVarInside p idx
    Exists p -> propDeBrBoundVarInside p idx
    (o1 :<=: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    F -> False


objDeBrSubXInt :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubXInt targetIdx substitution template = case template of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert $ propDeBrSubXInt targetIdx substitution normalisedSubexp
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
    (o1 :+: o2) -> objDeBrSubXInt targetIdx substitution o1 :+: objDeBrSubXInt targetIdx substitution o2
    Intneg o1     -> Intneg (objDeBrSubXInt targetIdx substitution o1)
    (o1 :*: o2) -> objDeBrSubXInt targetIdx substitution o1 :*: objDeBrSubXInt targetIdx substitution o2
    IntSet -> IntSet
    EmptySet -> EmptySet


propDeBrSubXInt :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubXInt targetIdx substitution template = case template of
    Neg p -> Neg $ propDeBrSubXInt targetIdx substitution p
    (p1 :&&: p2) -> propDeBrSubXInt targetIdx substitution p1 :&&: propDeBrSubXInt targetIdx substitution p2
    (p1 :||: p2) -> propDeBrSubXInt targetIdx substitution p1 :||: propDeBrSubXInt targetIdx substitution p2
    (p1 :->: p2) -> propDeBrSubXInt targetIdx substitution p1 :->: propDeBrSubXInt targetIdx substitution p2
    (p1 :<->: p2) -> propDeBrSubXInt targetIdx substitution p1 :<->: propDeBrSubXInt targetIdx substitution p2
    (o1 :==: o2) -> objDeBrSubXInt targetIdx substitution o1 :==: objDeBrSubXInt targetIdx substitution o2
    In o1 o2 -> objDeBrSubXInt targetIdx substitution o1 `In` objDeBrSubXInt targetIdx substitution o2
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
    (o1 :<=: o2) -> objDeBrSubXInt targetIdx substitution o1 :<=: objDeBrSubXInt targetIdx substitution o2
    F -> F


objDeBrSubX :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubX targetIdx substitution template = case template of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert $ propDeBrSubX targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    Bound idx -> Bound idx
    V idx -> V idx
    X idx
        | idx == targetIdx -> substitution
        | otherwise -> X idx
    XInternal idx -> XInternal idx
    (o1 :+: o2) -> objDeBrSubX targetIdx substitution o1 :+: objDeBrSubX targetIdx substitution o2
    Intneg o1     -> Intneg (objDeBrSubX targetIdx substitution o1) 
    (o1 :*: o2) -> objDeBrSubX targetIdx substitution o1 :*: objDeBrSubX targetIdx substitution o2
    IntSet -> IntSet
    EmptySet -> EmptySet


propDeBrSubX :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubX targetIdx substitution template = case template of
    Neg p -> Neg $ propDeBrSubX targetIdx substitution p
    (p1 :&&: p2) -> propDeBrSubX targetIdx substitution p1 :&&: propDeBrSubX targetIdx substitution p2
    (p1 :||: p2) -> propDeBrSubX targetIdx substitution p1 :||: propDeBrSubX targetIdx substitution p2
    (p1 :->: p2) -> propDeBrSubX targetIdx substitution p1 :->: propDeBrSubX targetIdx substitution p2
    (p1 :<->: p2) -> propDeBrSubX targetIdx substitution p1 :<->: propDeBrSubX targetIdx substitution p2
    (o1 :==: o2) -> objDeBrSubX targetIdx substitution o1 :==: objDeBrSubX targetIdx substitution o2
    In o1 o2 -> objDeBrSubX targetIdx substitution o1 `In` objDeBrSubX targetIdx substitution o2
    Forall p -> Forall $ propDeBrSubX targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    Exists p -> Exists $ propDeBrSubX targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    (o1 :<=: o2) -> objDeBrSubX targetIdx substitution o1 :<=: objDeBrSubX targetIdx substitution o2
    F -> F


swapXtoXIntProp :: PropDeBr -> PropDeBr
swapXtoXIntProp p = case p of
    Neg q -> Neg (swapXtoXIntProp q)
    (p1 :&&: p2) -> swapXtoXIntProp p1 :&&: swapXtoXIntProp p2
    (p1 :||: p2) -> swapXtoXIntProp p1 :||: swapXtoXIntProp p2
    (p1 :->: p2) -> swapXtoXIntProp p1 :->: swapXtoXIntProp p2
    (p1 :<->: p2) -> swapXtoXIntProp p1 :<->: swapXtoXIntProp p2
    (o1 :==: o2) -> swapXtoXIntObj o1 :==: swapXtoXIntObj o2
    In o1 o2 -> In (swapXtoXIntObj o1) (swapXtoXIntObj o2)
    Forall q -> Forall (swapXtoXIntProp q)
    Exists q -> Exists (swapXtoXIntProp q)
    (o1 :<=: o2) -> swapXtoXIntObj o1 :<=: swapXtoXIntObj o2
    F -> F



swapXtoXIntObj :: ObjDeBr -> ObjDeBr
swapXtoXIntObj o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapXtoXIntProp p)
    Bound i -> Bound i
    V i -> V i
    X i -> XInternal i
    XInternal i -> XInternal i
    (o1 :+: o2) -> swapXtoXIntObj o1 :+: swapXtoXIntObj o2
    Intneg o1     -> Intneg (swapXtoXIntObj o1)
    (o1 :*: o2) -> swapXtoXIntObj o1 :*: swapXtoXIntObj o2
    IntSet -> IntSet
    EmptySet -> EmptySet



swapXIntToXProp :: PropDeBr -> PropDeBr
swapXIntToXProp p = case p of
    Neg q -> Neg (swapXIntToXProp q)
    (p1 :&&: p2) -> swapXIntToXProp p1 :&&: swapXIntToXProp p2
    (p1 :||: p2) -> swapXIntToXProp p1 :||: swapXIntToXProp p2
    (p1 :->: p2) -> swapXIntToXProp p1 :->: swapXIntToXProp p2
    (p1 :<->: p2) -> swapXIntToXProp p1 :<->: swapXIntToXProp p2
    (o1 :==: o2) -> swapXIntToXObj o1 :==: swapXIntToXObj o2
    In o1 o2 -> In (swapXIntToXObj o1) (swapXIntToXObj o2)
    Forall q -> Forall (swapXIntToXProp q)
    Exists q -> Exists (swapXIntToXProp q)
    (o1 :<=: o2) -> swapXIntToXObj o1 :<=: swapXIntToXObj o2
    F -> F



swapXIntToXObj :: ObjDeBr -> ObjDeBr
swapXIntToXObj o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapXIntToXProp p)
    Bound i -> Bound i
    V i -> V i
    X i -> X i
    XInternal i -> X i
    (o1 :+: o2) -> swapXIntToXObj o1 :+: swapXIntToXObj o2
    Intneg o1     -> Intneg (swapXIntToXObj o1)
    (o1 :*: o2) -> swapXIntToXObj o1 :*: swapXIntToXObj o2
    IntSet -> IntSet
    EmptySet -> EmptySet


objDeBrSubXs :: [(Int, ObjDeBr)] -> ObjDeBr -> ObjDeBr
objDeBrSubXs subs term =
    swapXIntToXObj $
    foldl (\currentTerm (idx, substitutionTerm) ->
             objDeBrSubX idx (swapXtoXIntObj substitutionTerm) currentTerm
          ) term subs

propDeBrSubXs :: [(Int, ObjDeBr)] -> PropDeBr -> PropDeBr
propDeBrSubXs subs prop =
    swapXIntToXProp $
    foldl (\currentProp (idx, substitutionTerm) ->
             propDeBrSubX idx (swapXtoXIntObj substitutionTerm) currentProp
          ) prop subs








type PropErrDeBr = PL.LogicError PropDeBr DeBrSe Text ObjDeBr
type PropRuleDeBr = PL.LogicRule () PropDeBr DeBrSe Text

type PredErrDeBr = PREDL.LogicError PropDeBr DeBrSe Text ObjDeBr ()
type PredRuleDeBr = PREDL.LogicRule PropDeBr DeBrSe Text ObjDeBr ()

type PrfStdStepPredDeBr = PrfStdStep PropDeBr Text ()






xsubPropDeBr :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBr p idx depth = case p of
    Neg q -> Neg (xsubPropDeBr q idx depth)
    (p1 :&&: p2) -> xsubPropDeBr p1 idx depth :&&: xsubPropDeBr p2 idx depth
    (p1 :||: p2) -> xsubPropDeBr p1 idx depth :||: xsubPropDeBr p2 idx depth
    (p1 :->: p2) -> xsubPropDeBr p1 idx depth :->: xsubPropDeBr p2 idx depth
    (p1 :<->: p2) -> xsubPropDeBr p1 idx depth :<->: xsubPropDeBr p2 idx depth
    (o1 :==: o2) -> xsubObjDeBr o1 idx depth :==: xsubObjDeBr o2 idx depth
    In o1 o2 -> In (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)
    Forall q -> Forall (xsubPropDeBr q idx depth)
    Exists q -> Exists (xsubPropDeBr q idx depth)
    (o1 :<=: o2) -> xsubObjDeBr o1 idx depth :<=: xsubObjDeBr o2 idx depth
    F -> F


xsubObjDeBr :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBr o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (xsubPropDeBr p idx depth)
    Bound i -> Bound i
    V i -> V i
    X i -> if i == idx then Bound depth else X i
    XInternal i -> XInternal i
    (o1 :+: o2) -> xsubObjDeBr o1 idx depth :+: xsubObjDeBr o2 idx depth
    Intneg o1     -> Intneg (xsubObjDeBr o1 idx depth)
    (o1 :*: o2) -> xsubObjDeBr o1 idx depth :*: xsubObjDeBr o2 idx depth
    IntSet -> IntSet
    EmptySet -> EmptySet



xsubPropDeBrXInt :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBrXInt p idx depth = case p of
    Neg q -> Neg (xsubPropDeBrXInt q idx depth)
    (p1 :&&: p2) -> xsubPropDeBrXInt p1 idx depth :&&: xsubPropDeBrXInt p2 idx depth
    (p1 :||: p2) -> xsubPropDeBrXInt p1 idx depth :||: xsubPropDeBrXInt p2 idx depth
    (p1 :->: p2) -> xsubPropDeBrXInt p1 idx depth :->: xsubPropDeBrXInt p2 idx depth
    (p1 :<->: p2) -> xsubPropDeBrXInt p1 idx depth :<->: xsubPropDeBrXInt p2 idx depth
    (o1 :==: o2) -> xsubObjDeBrXInt o1 idx depth :==: xsubObjDeBrXInt o2 idx depth
    In o1 o2 -> In (xsubObjDeBrXInt o1 idx depth) (xsubObjDeBrXInt o2 idx depth)
    Forall q -> Forall (xsubPropDeBrXInt q idx depth)
    Exists q -> Exists (xsubPropDeBrXInt q idx depth)
    (o1 :<=: o2) -> xsubObjDeBrXInt o1 idx depth :<=: xsubObjDeBrXInt o2 idx depth
    F -> F


xsubObjDeBrXInt :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBrXInt o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (xsubPropDeBrXInt p idx depth)
    Bound i -> Bound i
    V i -> V i
    X i -> X i
    XInternal i -> if i == idx then Bound depth else XInternal i
    (o1 :+: o2) -> xsubObjDeBrXInt o1 idx depth :+: xsubObjDeBrXInt o2 idx depth
    Intneg o1     -> Intneg (xsubObjDeBrXInt o1 idx depth)
    (o1 :*: o2) -> xsubObjDeBrXInt o1 idx depth :*: xsubObjDeBrXInt o2 idx depth
    IntSet -> IntSet
    EmptySet -> EmptySet


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


eXInt :: Int -> PropDeBr -> PropDeBr
eXInt idx p = Exists $ xsubPropDeBrXInt p idx (boundDepthPropDeBr p)

aXInt :: Int -> PropDeBr -> PropDeBr
aXInt idx p = Forall $ xsubPropDeBrXInt p idx (boundDepthPropDeBr p)

hXInt :: Int -> PropDeBr -> ObjDeBr
hXInt idx p = Hilbert $ xsubPropDeBrXInt p idx (boundDepthPropDeBr p)


eXBang :: Int -> PropDeBr -> PropDeBr
eXBang idx p = eX idx (p :&&: aX (idx+1) (propDeBrSubX idx (X (idx+1)) p :->: Bound (boundDepthPropDeBr p) :==: X (idx+1))) -- Adjusted index for aX


aX :: Int -> PropDeBr -> PropDeBr
aX idx p = Forall $ xsubPropDeBr p idx (boundDepthPropDeBr p)

hX :: Int -> PropDeBr -> ObjDeBr
hX idx p = Hilbert (xsubPropDeBr p idx (boundDepthPropDeBr p))


multiBinder :: (Int -> PropDeBr -> PropDeBr) -> [Int] -> PropDeBr -> PropDeBr
multiBinder binder indices body =
    foldr binder body indices

multiEx :: [Int] -> PropDeBr -> PropDeBr
multiEx = multiBinder eX

multiAx :: [Int] -> PropDeBr -> PropDeBr
multiAx = multiBinder aX


