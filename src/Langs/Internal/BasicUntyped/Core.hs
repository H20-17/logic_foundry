module Langs.Internal.BasicUntyped.Core (
    ObjDeBr(..),
    PropDeBr(..),
    DeBrSe(..),
    PrfStdStepPredDeBr,
    PropErrDeBr,
    PropRuleDeBr,
    PredErrDeBr,
    PredRuleDeBr,
    ZFCRuleDeBr,
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
    aXInt,
    objDeBrSwapFreeVarsToX,
    propDeBrSwapFreeVarsToX,
    parseXInternal,
    propDeBrExtractConsts,
    extractElemsFromDisjunction,
    buildDisjunction,
    isSet,
    parseIsSet,
    roster,
    parseRoster

) where
import Control.Monad ( unless, guard,msum )
import Data.List (intersperse,findIndex, partition,sort,find,nub)
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
import Data.Tuple (swap)
import qualified Data.Set as Set
import Debug.Trace(trace, traceShow, traceShowId,traceM)



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
    deriving (Ord, Show, Eq)

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






objDeBrSwapFreeVarsToX :: ObjDeBr -> Map Int Int -> ObjDeBr
objDeBrSwapFreeVarsToX obj varMap = 

    case obj of
        Integ num -> Integ num
        Constant const -> Constant const
        Hilbert p -> objDeBrTryRosterNormalize $ Hilbert (propDeBrSwapFreeVarsToX p varMap)
        Bound i -> Bound i
        V i -> case Data.Map.lookup i varMap of
            Just newIdx -> X newIdx
            Nothing -> V i
        X i -> X i
        XInternal i -> XInternal i
        (o1 :+: o2) -> objDeBrSwapFreeVarsToX o1 varMap :+: objDeBrSwapFreeVarsToX o2 varMap
        Intneg o1     -> Intneg (objDeBrSwapFreeVarsToX o1 varMap)
        (o1 :*: o2) -> objDeBrSwapFreeVarsToX o1 varMap :*: objDeBrSwapFreeVarsToX o2 varMap
        IntSet -> IntSet
        EmptySet -> EmptySet


propDeBrSwapFreeVarsToX :: PropDeBr -> Map Int Int -> PropDeBr
propDeBrSwapFreeVarsToX prop varMap =
    case prop of
        Neg p -> Neg (propDeBrSwapFreeVarsToX p varMap)
        (p1 :&&: p2) -> propDeBrSwapFreeVarsToX p1 varMap :&&: propDeBrSwapFreeVarsToX p2 varMap
        (p1 :||: p2) -> propDeBrSwapFreeVarsToX p1 varMap :||: propDeBrSwapFreeVarsToX p2 varMap
        (p1 :->: p2) -> propDeBrSwapFreeVarsToX p1 varMap :->: propDeBrSwapFreeVarsToX p2 varMap
        (p1 :<->: p2) -> propDeBrSwapFreeVarsToX p1 varMap :<->: propDeBrSwapFreeVarsToX p2 varMap
        (o1 :==: o2) -> objDeBrSwapFreeVarsToX o1 varMap :==: objDeBrSwapFreeVarsToX o2 varMap
        In o1 o2 -> In (objDeBrSwapFreeVarsToX o1 varMap) (objDeBrSwapFreeVarsToX o2 varMap)
        Forall q -> Forall (propDeBrSwapFreeVarsToX q varMap)
        Exists q -> Exists (propDeBrSwapFreeVarsToX q varMap)
        (o1 :<=: o2) -> objDeBrSwapFreeVarsToX o1 varMap :<=: objDeBrSwapFreeVarsToX o2 varMap
        F -> F


objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx = case obj of
    Integ num -> False
    Constant const -> False
    Hilbert p -> propDeBrBoundVarInside p idx
    Bound i -> idx == i
    V i -> False
    X i -> False
    XInternal i -> False
    (o1 :+: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    Intneg o1     -> objDeBrBoundVarInside o1 idx
    (o1 :*: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx
    IntSet -> False
    EmptySet -> False



swapBoundIndexObjWorker :: Bool -> Int -> Int -> ObjDeBr -> ObjDeBr
swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> if rosterNormalize then
                    objDeBrTryRosterNormalize $ Hilbert (swapBoundIndexPropWorker True fromIdx toIdx p)
                else
                    Hilbert (swapBoundIndexPropWorker False fromIdx toIdx p)
    Bound i -> if i == fromIdx then Bound toIdx else Bound i
    V i -> V i
    X i -> X i
    XInternal i -> XInternal i
    (o1 :+: o2) -> swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o1 :+: swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o2
    Intneg o1   -> Intneg (swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o1)
    (o1 :*: o2) -> swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o1 :*: swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o2
    IntSet -> IntSet
    EmptySet -> EmptySet


swapBoundIndexObj:: Int -> Int -> ObjDeBr -> ObjDeBr
swapBoundIndexObj = swapBoundIndexObjWorker True



swapBoundIndexPropWorker :: Bool -> Int -> Int -> PropDeBr -> PropDeBr
swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p = case p of
    Neg q -> Neg (swapBoundIndexPropWorker rosterNormalize fromIdx toIdx q)
    (p1 :&&: p2) -> swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p1 :&&: swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p2
    (p1 :||: p2) -> swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p1 :||: swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p2
    (p1 :->: p2) -> swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p1 :->: swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p2
    (p1 :<->: p2) -> swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p1 :<->: swapBoundIndexPropWorker rosterNormalize fromIdx toIdx p2
    (o1 :==: o2) -> swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o1 :==: swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o2
    In o1 o2 -> In (swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o1) (swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o2)
    Forall q -> Forall (swapBoundIndexPropWorker rosterNormalize fromIdx toIdx q)
    Exists q -> Exists (swapBoundIndexPropWorker rosterNormalize fromIdx toIdx q)
    (o1 :<=: o2) -> swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o1 :<=: swapBoundIndexObjWorker rosterNormalize fromIdx toIdx o2
    F -> F


swapBoundIndexProp :: Int -> Int -> PropDeBr -> PropDeBr
swapBoundIndexProp = swapBoundIndexPropWorker True




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

parseXInternal :: ObjDeBr -> Maybe Int
parseXInternal subexp = case subexp of
    XInternal i -> Just i
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
     EmptySet -> 0



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
    ObjDeBrRosterNotNormalised :: ObjDeBr -> DeBrSe
   deriving Show



checkSanityObjDeBr :: ObjDeBr -> Int -> Set Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityObjDeBr obj varStackHeight tmpltVarIndices constSet boundSet = case obj of
     Integ num -> Nothing
     Constant name -> if name `Set.member` constSet then Nothing else (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> 
        checkSanityPropDeBr prop varStackHeight tmpltVarIndices constSet (Set.insert (boundDepthPropDeBr prop) boundSet )
        <|> case parseRoster obj of
            Just elements -> if (nub . sort) elements == elements then Nothing else (return . ObjDeBrRosterNotNormalised) obj
            Nothing -> Nothing
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
    Hilbert p -> objDeBrTryRosterNormalize $ Hilbert $ propDeBrSubXInt targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        --newBoundDepth = boundDepthPropDeBrXInt boundDepth subBoundDepth p
        newBoundDepth = boundDepthPropDeBrXInt targetIdx subBoundDepth p
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
        --newBoundDepth = boundDepthPropDeBrXInt boundDepth subBoundDepth p
        newBoundDepth = boundDepthPropDeBrXInt targetIdx subBoundDepth p
        subBoundDepth = boundDepthObjDeBr substitution
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    Exists p -> Exists $ propDeBrSubXInt targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        --newBoundDepth = boundDepthPropDeBrXInt boundDepth subBoundDepth p
        newBoundDepth = boundDepthPropDeBrXInt targetIdx subBoundDepth p
        subBoundDepth = boundDepthObjDeBr substitution
        normalisedSubexp = swapBoundIndexProp boundDepth newBoundDepth p
    (o1 :<=: o2) -> objDeBrSubXInt targetIdx substitution o1 :<=: objDeBrSubXInt targetIdx substitution o2
    F -> F


objDeBrSubXWorker :: Bool -> Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubXWorker rosterNormalize targetIdx substitution template = case template of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> 
        if rosterNormalize then 
            objDeBrTryRosterNormalize $ Hilbert $ propDeBrSubXWorker True targetIdx substitution normalisedSubexp
        else
            Hilbert $ propDeBrSubXWorker False targetIdx substitution normalisedSubexp
            -- this will only happen when the "roster" function is being called
            -- which will prevent infinite recursion
      where
        boundDepth = boundDepthPropDeBr p
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexPropWorker rosterNormalize boundDepth newBoundDepth p
    Bound idx -> Bound idx
    V idx -> V idx
    X idx
        | idx == targetIdx -> substitution
        | otherwise -> X idx
    XInternal idx -> XInternal idx
    (o1 :+: o2) -> objDeBrSubXWorker rosterNormalize targetIdx substitution o1 :+: objDeBrSubXWorker rosterNormalize targetIdx substitution o2
    Intneg o1     -> Intneg (objDeBrSubXWorker rosterNormalize targetIdx substitution o1) 
    (o1 :*: o2) -> objDeBrSubXWorker rosterNormalize targetIdx substitution o1 :*: objDeBrSubXWorker rosterNormalize targetIdx substitution o2
    IntSet -> IntSet
    EmptySet -> EmptySet


objDeBrSubX :: Int -> ObjDeBr -> ObjDeBr -> ObjDeBr
objDeBrSubX = objDeBrSubXWorker True

propDeBrSubXWorker :: Bool -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubXWorker rosterNormalize targetIdx substitution template = case template of
    Neg p -> Neg $ propDeBrSubXWorker rosterNormalize targetIdx substitution p
    (p1 :&&: p2) -> propDeBrSubXWorker rosterNormalize targetIdx substitution p1 :&&: propDeBrSubXWorker rosterNormalize targetIdx substitution p2
    (p1 :||: p2) -> propDeBrSubXWorker rosterNormalize targetIdx substitution p1 :||: propDeBrSubXWorker rosterNormalize targetIdx substitution p2
    (p1 :->: p2) -> propDeBrSubXWorker rosterNormalize targetIdx substitution p1 :->: propDeBrSubXWorker rosterNormalize targetIdx substitution p2
    (p1 :<->: p2) -> propDeBrSubXWorker rosterNormalize targetIdx substitution p1 :<->: propDeBrSubXWorker rosterNormalize targetIdx substitution p2
    (o1 :==: o2) -> objDeBrSubXWorker rosterNormalize targetIdx substitution o1 :==: objDeBrSubXWorker rosterNormalize targetIdx substitution o2
    In o1 o2 -> objDeBrSubXWorker rosterNormalize targetIdx substitution o1 `In` objDeBrSubXWorker rosterNormalize targetIdx substitution o2
    Forall p -> Forall $ propDeBrSubXWorker rosterNormalize targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexPropWorker rosterNormalize boundDepth newBoundDepth p
    Exists p -> Exists $ propDeBrSubXWorker rosterNormalize targetIdx substitution normalisedSubexp
      where
        boundDepth = boundDepthPropDeBr p
        subBoundDepth = boundDepthObjDeBr substitution
        newBoundDepth = boundDepthPropDeBrX targetIdx subBoundDepth p
        normalisedSubexp = swapBoundIndexPropWorker rosterNormalize boundDepth newBoundDepth p
    (o1 :<=: o2) -> objDeBrSubXWorker rosterNormalize targetIdx substitution o1 :<=: objDeBrSubXWorker rosterNormalize targetIdx substitution o2
    F -> F

propDeBrSubX :: Int -> ObjDeBr -> PropDeBr -> PropDeBr
propDeBrSubX = propDeBrSubXWorker True


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



swapXIntToXProp :: Bool -> PropDeBr -> PropDeBr
swapXIntToXProp rosterNormalize p = case p of
    Neg q -> Neg (swapXIntToXProp rosterNormalize q)
    (p1 :&&: p2) -> swapXIntToXProp rosterNormalize p1 :&&: swapXIntToXProp rosterNormalize p2
    (p1 :||: p2) -> swapXIntToXProp rosterNormalize p1 :||: swapXIntToXProp rosterNormalize p2
    (p1 :->: p2) -> swapXIntToXProp rosterNormalize p1 :->: swapXIntToXProp rosterNormalize p2
    (p1 :<->: p2) -> swapXIntToXProp rosterNormalize p1 :<->: swapXIntToXProp rosterNormalize p2
    (o1 :==: o2) -> swapXIntToXObj rosterNormalize o1 :==: swapXIntToXObj rosterNormalize o2
    In o1 o2 -> In (swapXIntToXObj rosterNormalize o1) (swapXIntToXObj rosterNormalize o2)
    Forall q -> Forall (swapXIntToXProp rosterNormalize q)
    Exists q -> Exists (swapXIntToXProp rosterNormalize q)
    (o1 :<=: o2) -> swapXIntToXObj rosterNormalize o1 :<=: swapXIntToXObj rosterNormalize o2
    F -> F




swapXIntToXObj :: Bool -> ObjDeBr -> ObjDeBr
swapXIntToXObj rosterNormalize o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> 
        if rosterNormalize
         then objDeBrTryRosterNormalize $ Hilbert (swapXIntToXProp True p)
         else
             --this will only happen when the "roster" function is being called
             --which will prevent infinite recursion
        Hilbert (swapXIntToXProp False p)
    Bound i -> Bound i
    V i -> V i
    X i -> X i
    XInternal i -> X i
    (o1 :+: o2) -> swapXIntToXObj rosterNormalize o1 :+: swapXIntToXObj rosterNormalize o2
    Intneg o1     -> Intneg (swapXIntToXObj rosterNormalize o1)
    (o1 :*: o2) -> swapXIntToXObj rosterNormalize o1 :*: swapXIntToXObj rosterNormalize o2
    IntSet -> IntSet
    EmptySet -> EmptySet


objDeBrSubXsWorker :: Bool -> [(Int, ObjDeBr)] -> ObjDeBr -> ObjDeBr
objDeBrSubXsWorker rosterNormalize subs term =
    swapXIntToXObj rosterNormalize $
    foldl (\currentTerm (idx, substitutionTerm) ->
             objDeBrSubXWorker False idx (swapXtoXIntObj substitutionTerm) currentTerm
          ) term subs
          
objDeBrSubXs :: [(Int, ObjDeBr)] -> ObjDeBr -> ObjDeBr
objDeBrSubXs = objDeBrSubXsWorker True



-- | This function is used to substitute a list of substitutions into an PropDeBr expression.
-- | The substitutions are given as a list of pairs (index, substitution term)
-- | For each substitution (idx, t), The function will replace all occurrences of the 'X index' in the expression with t.
-- | The function begins by recursing through the list of substitutions.
-- | For each substition term, the function first swaps X template variables within the term to matching XInternal template 
-- | variables, and 
-- | then it applies the substitution to the PropDeBre expression.
-- | Once all substitutions have been applied, it swaps all of the XInternal template variables in the
-- | thusly generated expression
-- | back to X template variables.
-- | The swapping of X template variables to XInternal template variables and back, is done to ensure that the
-- | substitutions do not interfere with each other.
propDeBrSubXs :: [(Int, ObjDeBr)] -> PropDeBr -> PropDeBr
propDeBrSubXs subs prop =
    swapXIntToXProp True $
    foldl (\currentProp (idx, substitutionTerm) ->
             propDeBrSubX idx (swapXtoXIntObj substitutionTerm) currentProp
          ) prop subs








type PropErrDeBr = PL.LogicError PropDeBr DeBrSe Text ObjDeBr
type PropRuleDeBr = PL.LogicRule () PropDeBr DeBrSe Text

type PredErrDeBr = PREDL.LogicError PropDeBr DeBrSe Text ObjDeBr ()
type PredRuleDeBr = PREDL.LogicRule PropDeBr DeBrSe Text ObjDeBr ()

type ZFCRuleDeBr = ZFC.LogicRule PropDeBr DeBrSe ObjDeBr

type PrfStdStepPredDeBr = PrfStdStep PropDeBr Text ()




xsubObjDeBrWorker :: Bool -> ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBrWorker rosterNormalize o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p ->if rosterNormalize
        then objDeBrTryRosterNormalize $ Hilbert (xsubPropDeBrWorker True p idx depth)
        else
            Hilbert (xsubPropDeBrWorker False p idx depth)
            -- this will only happen when the "roster" function is being called
            -- THis is to stop infinite recursion
    Bound i -> Bound i
    V i -> V i
    X i -> if i == idx then Bound depth else X i
    XInternal i -> XInternal i
    (o1 :+: o2) -> xsubObjDeBrWorker rosterNormalize o1 idx depth :+: xsubObjDeBrWorker rosterNormalize o2 idx depth
    Intneg o1     -> Intneg (xsubObjDeBrWorker rosterNormalize o1 idx depth)
    (o1 :*: o2) -> xsubObjDeBrWorker rosterNormalize o1 idx depth :*: xsubObjDeBrWorker rosterNormalize o2 idx depth
    IntSet -> IntSet
    EmptySet -> EmptySet

xsubObjDeBr :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBr = xsubObjDeBrWorker True

xsubPropDeBrWorker :: Bool -> PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBrWorker rosterNormalize p idx depth = case p of
    Neg q -> Neg (xsubPropDeBrWorker rosterNormalize q idx depth)
    (p1 :&&: p2) -> xsubPropDeBrWorker rosterNormalize p1 idx depth :&&: xsubPropDeBrWorker rosterNormalize p2 idx depth
    (p1 :||: p2) -> xsubPropDeBrWorker rosterNormalize p1 idx depth :||: xsubPropDeBrWorker rosterNormalize p2 idx depth
    (p1 :->: p2) -> xsubPropDeBrWorker rosterNormalize p1 idx depth :->: xsubPropDeBrWorker rosterNormalize p2 idx depth
    (p1 :<->: p2) -> xsubPropDeBrWorker rosterNormalize p1 idx depth :<->: xsubPropDeBrWorker rosterNormalize p2 idx depth
    (o1 :==: o2) -> xsubObjDeBrWorker rosterNormalize o1 idx depth :==: xsubObjDeBrWorker rosterNormalize o2 idx depth
    In o1 o2 -> In (xsubObjDeBrWorker rosterNormalize o1 idx depth) (xsubObjDeBrWorker rosterNormalize o2 idx depth)
    Forall q -> Forall (xsubPropDeBrWorker rosterNormalize q idx depth)
    Exists q -> Exists (xsubPropDeBrWorker rosterNormalize q idx depth)
    (o1 :<=: o2) -> xsubObjDeBrWorker rosterNormalize o1 idx depth :<=: xsubObjDeBrWorker rosterNormalize o2 idx depth
    F -> F

xsubPropDeBr :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBr = xsubPropDeBrWorker True




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
    Hilbert p -> objDeBrTryRosterNormalize $ Hilbert (xsubPropDeBrXInt p idx depth)
    Bound i -> Bound i
    V i -> V i
    X i -> X i
    XInternal i -> if i == idx then Bound depth else XInternal i
    (o1 :+: o2) -> xsubObjDeBrXInt o1 idx depth :+: xsubObjDeBrXInt o2 idx depth
    Intneg o1     -> Intneg (xsubObjDeBrXInt o1 idx depth)
    (o1 :*: o2) -> xsubObjDeBrXInt o1 idx depth :*: xsubObjDeBrXInt o2 idx depth
    IntSet -> IntSet
    EmptySet -> EmptySet

objDeBrExtractConsts :: ObjDeBr -> Set Text

objDeBrExtractConsts obj = case obj of
    Integ _ -> Set.empty
    Constant name -> Set.singleton name
    Hilbert p -> propDeBrExtractConsts p
    Bound _ -> Set.empty
    V _ -> Set.empty
    X _ -> Set.empty
    XInternal _ -> Set.empty
    (o1 :+: o2) -> objDeBrExtractConsts o1 `Set.union` objDeBrExtractConsts o2
    Intneg o1     -> objDeBrExtractConsts o1
    (o1 :*: o2) -> objDeBrExtractConsts o1 `Set.union` objDeBrExtractConsts o2
    IntSet -> Set.empty
    EmptySet -> Set.empty


propDeBrExtractConsts :: PropDeBr -> Set Text
propDeBrExtractConsts prop = case prop of
    Neg p -> propDeBrExtractConsts p
    (p1 :&&: p2) -> propDeBrExtractConsts p1 `Set.union` propDeBrExtractConsts p2
    (p1 :||: p2) -> propDeBrExtractConsts p1 `Set.union` propDeBrExtractConsts p2
    (p1 :->: p2) -> propDeBrExtractConsts p1 `Set.union` propDeBrExtractConsts p2
    (p1 :<->: p2) -> propDeBrExtractConsts p1 `Set.union` propDeBrExtractConsts p2
    In o1 o2 -> objDeBrExtractConsts o1 `Set.union` objDeBrExtractConsts o2
    (o1 :==: o2) -> objDeBrExtractConsts o1 `Set.union` objDeBrExtractConsts o2
    Forall p -> propDeBrExtractConsts p
    Exists p -> propDeBrExtractConsts p
    (o1 :<=: o2) -> objDeBrExtractConsts o1 `Set.union` objDeBrExtractConsts o2
    F -> Set.empty




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
eXBang idx p = eX idx 
           (p 
              :&&: 
            aXInt 0 
                   (
                      propDeBrSubX idx (XInternal 0) p 
                           :->: 
                      XInternal 0 :==: X idx
                )
            )
 

aXWorker :: Bool -> Int -> PropDeBr -> PropDeBr
aXWorker rosterNormalize idx p = Forall $ xsubPropDeBrWorker rosterNormalize p idx (boundDepthPropDeBr p)


aX :: Int -> PropDeBr -> PropDeBr
aX = aXWorker True


hXWorker :: Bool -> Int -> PropDeBr -> ObjDeBr
hXWorker rosterNormalize idx p = Hilbert (xsubPropDeBrWorker rosterNormalize p idx (boundDepthPropDeBr p))

hX :: Int -> PropDeBr -> ObjDeBr
hX = hXWorker True


multiBinder :: (Int -> PropDeBr -> PropDeBr) -> [Int] -> PropDeBr -> PropDeBr
multiBinder binder indices body =
    foldr binder body indices

multiEx :: [Int] -> PropDeBr -> PropDeBr
multiEx = multiBinder eX

multiAx :: [Int] -> PropDeBr -> PropDeBr
multiAx = multiBinder aX


-- Helper to recursively extract element terms from the disjunction:
-- (var == e1) || (var == e2) || ... || (var == en)
-- Expects var to be the specific Bound variable used (e.g., Bound idx_x)
extractElemsFromDisjunction :: ObjDeBr -> PropDeBr -> Maybe [ObjDeBr]
extractElemsFromDisjunction var prop = case prop of
    -- Base case: single equality
    (lhs :==: elemTerm) -> do
        guard (lhs == var) -- Check the variable matches
        -- Sanity check: Ensure the extracted element doesn't contain the var itself
        -- This check might be too strict if var represents a template X before binding,
        -- but essential if var is already Bound idx. Let's assume var is Bound idx.
        varIdx <- parseBound var
        guard (not (objDeBrBoundVarInside elemTerm varIdx))
        Just [elemTerm]
    -- Recursive case: disjunction
    (eqTerm :||: restOfDisjunction) -> do
        (lhs, elemTerm) <- parseEqual eqTerm -- Parse the equality on the left
        guard (lhs == var) -- Check variable
        varIdx <- parseBound var
        guard (not (objDeBrBoundVarInside elemTerm varIdx))
        elemsRest <- extractElemsFromDisjunction var restOfDisjunction -- Recurse
        Just (elemTerm : elemsRest) -- Prepend current element
    -- Base case: Falsum (corresponds to empty roster, handled separately)
    F -> Just []
    -- Anything else is not the expected structure
    _ -> Nothing






-- Helper function to build a disjunction of equalities:
-- (var == e1) || (var == e2) || ... || (var == en)
buildDisjunction :: ObjDeBr -> [ObjDeBr] -> PropDeBr
buildDisjunction _ [] = F -- Disjunction of zero items is Falsum
buildDisjunction var [e] = var :==: e
buildDisjunction var (e:es) = (var :==: e) :||: buildDisjunction var es



-- | Helper to find the maximum of two 'Maybe Int' values.
-- | If both are Just, it returns Just the greater value.
-- | If one is Just, it returns that one.
-- | If both are Nothing, it returns Nothing.
maxMaybe :: Maybe Int -> Maybe Int -> Maybe Int
maxMaybe mx my = case (mx, my) of
    (Just x, Just y) -> Just (max x y)
    (Just x, Nothing)  -> Just x
    (Nothing, Just y)  -> Just y
    (Nothing, Nothing) -> Nothing
-- An alternative, more concise definition using Alternative typeclass for Maybe:
-- maxMaybe mx my = fmap (uncurry max) (liftA2 (,) mx my) <|> mx <|> my

-- | Finds the maximum index `k` of any user-facing template variable (X k)
-- | within a proposition. Returns Nothing if no such template variables are found.
-- | It ignores internal template variables (XInternal k).
-- | This function is mutually recursive with objMaxXIdx.
propMaxXIdx :: PropDeBr -> Maybe Int
propMaxXIdx prop = case prop of
    Neg p       -> propMaxXIdx p
    p :&&: q    -> maxMaybe (propMaxXIdx p) (propMaxXIdx q)
    p :||: q    -> maxMaybe (propMaxXIdx p) (propMaxXIdx q)
    p :->: q    -> maxMaybe (propMaxXIdx p) (propMaxXIdx q)
    p :<->: q   -> maxMaybe (propMaxXIdx p) (propMaxXIdx q)
    a :==: b    -> maxMaybe (objMaxXIdx a) (objMaxXIdx b)
    In a b      -> maxMaybe (objMaxXIdx a) (objMaxXIdx b)
    Forall p    -> propMaxXIdx p
    Exists p    -> propMaxXIdx p
    a :<=: b    -> maxMaybe (objMaxXIdx a) (objMaxXIdx b)
    F           -> Nothing -- Base case: Falsum has no variables.

-- | Finds the maximum index `k` of any user-facing template variable (X k)
-- | within an object/term. Returns Nothing if no such template variables are found.
-- | It ignores internal template variables (XInternal k).
-- | This function is mutually recursive with propMaxXIdx.
objMaxXIdx :: ObjDeBr -> Maybe Int
objMaxXIdx obj = case obj of
    Hilbert p   -> propMaxXIdx p
    a :+: b     -> maxMaybe (objMaxXIdx a) (objMaxXIdx b)
    Intneg o    -> objMaxXIdx o
    a :*: b     -> maxMaybe (objMaxXIdx a) (objMaxXIdx b)
    X i         -> Just i

    -- Base cases: These constructors do not contain any sub-terms with template variables,
    -- or they contain template variables we want to ignore (XInternal).
    XInternal _ -> Nothing -- Ignore internal template variables
    Integ _     -> Nothing
    Constant _  -> Nothing
    Bound _     -> Nothing
    V _         -> Nothing
    IntSet      -> Nothing
    EmptySet    -> Nothing

-- | Finds the maximum index `k` of any user-facing template variable (X k)
-- | within a list of objects/terms. Returns Nothing if no template variables are found.
objsMaxXIdx :: [ObjDeBr] -> Maybe Int
objsMaxXIdx objs =
    -- Map objMaxXIdx over the list to get a list of Maybe Ints.
    let maybeIdxs = Prelude.map objMaxXIdx objs in
    -- Fold over the list of Maybe Ints using maxMaybe to find the overall maximum.
    -- The starting value for the fold is Nothing.
    foldr maxMaybe Nothing maybeIdxs
-- A simpler implementation using catMaybes:
-- objsMaxXIdx objs =
--     let justIdxs = catMaybes (map objMaxXIdx objs)
--     in if null justIdxs then Nothing else Just (maximum justIdxs)

-- | Constructs the ObjDeBr term representing a set defined by listing its elements {e₁, e₂, ..., eₙ}.
--   Now asserts that the roster itself is a set.
roster :: [ObjDeBr] -> ObjDeBr
roster [] = EmptySet -- EmptySet is axiomatically a set.
roster elems =
    let
        uniqueSortedElems = nub (sort elems)
        idx_base = maybe 0 (+1) (objsMaxXIdx uniqueSortedElems)
        s_idx = 0; x_idx = 1
        elem_indices = [2 .. length uniqueSortedElems + 1]
        elemPlaceholders = Prelude.map X elem_indices
        disjunction = buildDisjunction (X x_idx) elemPlaceholders
        
        element_membership_prop = (X x_idx `In` X s_idx) :<->: disjunction
        quantified_prop = aXWorker False x_idx element_membership_prop
        
        condition_S_isSet = isSet (X s_idx)
        full_prop_for_S = condition_S_isSet :&&: quantified_prop
        
        hilbertTemplate = hXWorker False s_idx full_prop_for_S
        elemSubs = zip elem_indices uniqueSortedElems
    in objDeBrSubXsWorker False elemSubs hilbertTemplate

-- | Parses an ObjDeBr term to see if it matches the structure generated by 'roster'.
--   Now expects isSet(S) as part of the definition.
parseRoster :: ObjDeBr -> Maybe [ObjDeBr]
parseRoster obj
    | obj == EmptySet = Just [] -- Handle empty set case directly
    | otherwise = do
        (p_conj, idx_S) <- parseHilbert obj
        (isSet_S_prop, forall_x_prop) <- parseConjunction p_conj

        s_object_from_isSet <- parseIsSet isSet_S_prop
        s_bound_from_isSet <- parseBound s_object_from_isSet
        guard (s_bound_from_isSet == idx_S)

        (bicond_prop, idx_x) <- parseForall2 forall_x_prop
        (x_in_S_prop, disjunction_part) <- parseBiconditional bicond_prop

        (bound_x_lhs, bound_S_lhs) <- parseIn x_in_S_prop
        parsed_idx_x_lhs <- parseBound bound_x_lhs
        parsed_idx_S_lhs <- parseBound bound_S_lhs
        guard (parsed_idx_x_lhs == idx_x)
        guard (parsed_idx_S_lhs == idx_S)

        elems <- extractElemsFromDisjunction (Bound idx_x) disjunction_part
        guard (all (not . (`objDeBrBoundVarInside` idx_S)) elems)
        Just $ elems

-- Definition for isSet
-- isSet x  translates to  x ∉ ℤ  which is  ¬(x ∈ ℤ)
-- This signifies that x is a set (either empty or non-empty).
isSet :: ObjDeBr -> PropDeBr
isSet x = Neg (x `In` IntSet)

-- Parser for isSet
-- parseIsSet p  returns Just x  if p is of the form ¬(x ∈ ℤ)
parseIsSet :: PropDeBr -> Maybe ObjDeBr
parseIsSet (Neg (x `In` IntSet)) = Just x
parseIsSet _ = Nothing




objDeBrTryRosterNormalize :: ObjDeBr -> ObjDeBr
objDeBrTryRosterNormalize obj =
    let x = trace "objDeBrTryRosterNormalize" (show obj)
        y = x
    in
        -- Attempt to parse the object as a roster.
        -- If it matches the expected structure, normalize it.
        -- Otherwise, return the original object.
    case parseRoster obj of
        Just elements -> roster elements
        Nothing -> obj

-- | Recursively traverses an object/term and normalizes any 'roster' set representations within it.
-- | This function is mutually recursive with 'propDeBrRosterNormalize'.
-- | The core logic resides here: when a Hilbert term is encountered, it is checked
-- | to see if it's a roster. If so, its elements are normalized, and the roster
-- | is rebuilt into its canonical form (sorted, unique elements).
objDeBrRosterNormalize :: ObjDeBr -> ObjDeBr
objDeBrRosterNormalize obj =
    case obj of
        Hilbert p ->
            let 
                 p_normalized = propDeBrRosterNormalize p
            in
                 objDeBrTryRosterNormalize (Hilbert p_normalized)
                
            -- For a Hilbert term, first normalize the proposition inside it.


        -- Recursive cases for other compound object types:
        a :+: b  -> objDeBrRosterNormalize a :+: objDeBrRosterNormalize b
        Intneg o -> Intneg (objDeBrRosterNormalize o)
        a :*: b  -> objDeBrRosterNormalize a :*: objDeBrRosterNormalize b

        -- Base cases: these terms have no sub-components to normalize.
        Integ _     -> obj
        Constant _  -> obj
        Bound _     -> obj
        V _         -> obj
        X _         -> obj
        XInternal _ -> obj
        IntSet      -> obj
        EmptySet    -> obj


-- | Recursively traverses a proposition and normalizes any 'roster' set representations within it.
-- | This function is mutually recursive with 'objDeBrRosterNormalize'.
-- | Normalization ensures that sets with the same elements have identical term representations,
-- | regardless of initial ordering or duplicates.
propDeBrRosterNormalize :: PropDeBr -> PropDeBr
propDeBrRosterNormalize prop = case prop of
    Neg p       -> Neg (propDeBrRosterNormalize p)
    p :&&: q    -> propDeBrRosterNormalize p :&&: propDeBrRosterNormalize q
    p :||: q    -> propDeBrRosterNormalize p :||: propDeBrRosterNormalize q
    p :->: q    -> propDeBrRosterNormalize p :->: propDeBrRosterNormalize q
    p :<->: q   -> propDeBrRosterNormalize p :<->: propDeBrRosterNormalize q
    a :==: b    -> objDeBrRosterNormalize a :==: objDeBrRosterNormalize b
    In a b      -> In (objDeBrRosterNormalize a) (objDeBrRosterNormalize b)
    Forall p    -> Forall (propDeBrRosterNormalize p)
    Exists p    -> Exists (propDeBrRosterNormalize p)
    a :<=: b    -> objDeBrRosterNormalize a :<=: objDeBrRosterNormalize b
    F           -> prop -- Base case, no recursion