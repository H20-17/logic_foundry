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
    parseTupl,
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
    -- parseGTE, -- Removed
    parseLTE, -- Added
    parseFalsum,
    objDeBrSubXInt,
    propDeBrSubXInt,
    hXInt,
    propDeBrSubXs,
    multiEx,
    multiAx,
    propDeBrSubX,
    -- Added parsers for new ObjDeBr operators
    parseIntPlus,
    parseIntNeg,
    parseIntMult,
    parseIntSet

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


-- Update ObjDeBr constructors
data ObjDeBr where
    Integ :: Int -> ObjDeBr
    Constant :: Text -> ObjDeBr
    Hilbert :: PropDeBr -> ObjDeBr
    Bound :: Int -> ObjDeBr
    V :: Int ->ObjDeBr
    X :: Int -> ObjDeBr
    XInternal :: Int -> ObjDeBr
    Tupl :: [ObjDeBr] -> ObjDeBr
    (:+:) :: ObjDeBr -> ObjDeBr -> ObjDeBr -- Changed to infix +
    Intneg :: ObjDeBr -> ObjDeBr            -- Kept prefix unary -
    (:*:) :: ObjDeBr -> ObjDeBr -> ObjDeBr -- Changed to infix *
    IntSet :: ObjDeBr
    deriving (Eq, Ord, Show)

-- Define Infix properties (optional, but good practice for clarity)
infixl 6 :+:
infixl 7 :*:

-- Update PropDeBr constructors
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
      -- (:>=:) :: ObjDeBr -> ObjDeBr -> PropDeBr -- Removed >=
      (:<=:) :: ObjDeBr -> ObjDeBr -> PropDeBr -- Added <=
      F :: PropDeBr
    deriving (Show, Eq, Ord)


infixr 3 :&&:
infixr 2 :||:
infixr 0 :->:
infixr 0 :<->:
infix  4 :==:
infix  4 `In`
-- infix  4 :>=: -- Removed >=
infix  4 :<=: -- Added <=


-- Update objDeBrBoundVarInside
objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx = case obj of
    Integ num -> False
    Constant const -> False
    Hilbert p -> propDeBrBoundVarInside p idx
    Bound i -> idx == i
    V i -> False
    X i -> False
    Tupl as -> any (`objDeBrBoundVarInside` idx) as
    (o1 :+: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx -- Updated
    Intneg o1     -> objDeBrBoundVarInside o1 idx                            -- Updated
    (o1 :*: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx -- Updated
    IntSet -> False


-- Update swapBoundIndexProp (No changes needed here, already updated)
swapBoundIndexProp :: Int -> Int -> PropDeBr -> PropDeBr
swapBoundIndexProp fromIdx toIdx p = case p of
    Neg q -> Neg (swapBoundIndexProp fromIdx toIdx q)
    (p1 :&&: p2) -> (swapBoundIndexProp fromIdx toIdx p1) :&&: (swapBoundIndexProp fromIdx toIdx p2)
    (p1 :||: p2) -> (swapBoundIndexProp fromIdx toIdx p1) :||: (swapBoundIndexProp fromIdx toIdx p2)
    (p1 :->: p2) -> (swapBoundIndexProp fromIdx toIdx p1) :->: (swapBoundIndexProp fromIdx toIdx p2)
    (p1 :<->: p2) -> (swapBoundIndexProp fromIdx toIdx p1) :<->: (swapBoundIndexProp fromIdx toIdx p2)
    (o1 :==: o2) -> (swapBoundIndexObj fromIdx toIdx o1) :==: (swapBoundIndexObj fromIdx toIdx o2)
    In o1 o2 -> In (swapBoundIndexObj fromIdx toIdx o1) (swapBoundIndexObj fromIdx toIdx o2)
    Forall q -> Forall (swapBoundIndexProp fromIdx toIdx q)
    Exists q -> Exists (swapBoundIndexProp fromIdx toIdx q)
    (o1 :<=: o2) -> (swapBoundIndexObj fromIdx toIdx o1) :<=: (swapBoundIndexObj fromIdx toIdx o2) -- Updated
    F -> F


-- Update swapBoundIndexObj
swapBoundIndexObj :: Int -> Int -> ObjDeBr -> ObjDeBr
swapBoundIndexObj fromIdx toIdx o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapBoundIndexProp fromIdx toIdx p)
    Bound i -> if i == fromIdx then Bound toIdx else Bound i
    V i -> V i
    X i -> X i
    XInternal i -> XInternal i
    Tupl os -> Tupl $ Prelude.map (swapBoundIndexObj fromIdx toIdx) os
    (o1 :+: o2) -> (swapBoundIndexObj fromIdx toIdx o1) :+: (swapBoundIndexObj fromIdx toIdx o2) -- Updated
    Intneg o1     -> Intneg (swapBoundIndexObj fromIdx toIdx o1)                                  -- Updated
    (o1 :*: o2) -> (swapBoundIndexObj fromIdx toIdx o1) :*: (swapBoundIndexObj fromIdx toIdx o2) -- Updated
    IntSet -> IntSet


-- Update boundDepthObjDeBrX
boundDepthObjDeBrX :: Int -> Int -> ObjDeBr -> Int
boundDepthObjDeBrX targetIdx substitutionDepth obj = case obj of
    Integ num -> 0
    Constant name -> 0
    Hilbert prop -> 1 + boundDepthPropDeBrX targetIdx substitutionDepth prop
    Bound idx -> 0
    V idx -> 0
    X idx -> if idx == targetIdx then substitutionDepth else 0
    XInternal idx -> 0
    Tupl xs -> if null xs then 0 else maximum $ Prelude.map (boundDepthObjDeBrX targetIdx substitutionDepth) xs
    (o1 :+: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2) -- Updated
    Intneg o1     -> boundDepthObjDeBrX targetIdx substitutionDepth o1                                                     -- Updated
    (o1 :*: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2) -- Updated
    IntSet -> 0


-- Update boundDepthPropDeBrX (No changes needed here, already updated)
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
    (o1 :<=: o2) -> max (boundDepthObjDeBrX targetIdx substitutionDepth o1) (boundDepthObjDeBrX targetIdx substitutionDepth o2) -- Updated
    F -> 0


-- Update boundDepthObjDeBrXInt
boundDepthObjDeBrXInt :: Int -> Int -> ObjDeBr -> Int
boundDepthObjDeBrXInt targetIdx substitutionDepth obj = case obj of
    Integ num -> 0
    Constant name -> 0
    Hilbert prop -> 1 + boundDepthPropDeBrXInt targetIdx substitutionDepth prop
    Bound idx -> 0
    V idx -> 0
    X idx -> 0
    XInternal idx -> if idx == targetIdx then substitutionDepth else 0
    Tupl xs -> if null xs then 0 else maximum $ Prelude.map (boundDepthObjDeBrXInt targetIdx substitutionDepth) xs
    (o1 :+: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2) -- Updated
    Intneg o1     -> boundDepthObjDeBrXInt targetIdx substitutionDepth o1                                                     -- Updated
    (o1 :*: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2) -- Updated
    IntSet -> 0

-- Update boundDepthPropDeBrXInt (No changes needed here, already updated)
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
    (o1 :<=: o2) -> max (boundDepthObjDeBrXInt targetIdx substitutionDepth o1) (boundDepthObjDeBrXInt targetIdx substitutionDepth o2) -- Updated
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

parseTupl :: ObjDeBr ->  Maybe [ObjDeBr]
parseTupl subexp = case subexp of
    Tupl xs -> Just xs
    _ -> Nothing


parseX :: ObjDeBr -> Maybe Int
parseX subexp = case subexp of
    X i -> Just i
    _ -> Nothing


parseEqual :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseEqual subexp = case subexp of
    (:==:) ls rs -> Just (ls,rs)
    _           -> Nothing


-- Update boundDepthObjDeBr
boundDepthObjDeBr :: ObjDeBr -> Int
boundDepthObjDeBr obj = case obj of
     Integ num -> 0
     Constant name -> 0
     Hilbert prop -> boundDepthPropDeBr prop + 1
     Bound idx -> 0
     V idx -> 0
     X idx -> 0
     XInternal idx -> 0
     Tupl xs -> if null xs then 0 else maximum $ Prelude.map boundDepthObjDeBr xs
     (o1 :+: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2) -- Updated
     Intneg o1     -> boundDepthObjDeBr o1                            -- Updated
     (o1 :*: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2) -- Updated
     IntSet ->  0


-- Update boundDepthPropDeBr (No changes needed here, already updated)
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
    (o1 :<=: o2) -> max (boundDepthObjDeBr o1) (boundDepthObjDeBr o2) -- Updated
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

-- Remove parseGTE
-- Add parseLTE (already added in previous response)
parseLTE :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseLTE p = case p of
    (a :<=: b) -> Just (a, b)
    _ -> Nothing


parseFalsum :: PropDeBr -> Maybe ()
parseFalsum p = case p of
    F -> Just ()
    _ -> Nothing

-- Add parsers for new ObjDeBr operators
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


data DeBrSe where
    ObjDeBrSeConstNotDefd :: Text -> DeBrSe
    ObjDeBrBoundVarIdx :: Int -> DeBrSe
    ObjDeBrFreeVarIdx :: Int -> DeBrSe
    ObjDeBrTemplateVarIdx :: Int -> DeBrSe
    ObjDeBrUnconsumedX :: Int -> DeBrSe
   deriving Show


-- Update checkSanityObjDeBr
checkSanityObjDeBr :: ObjDeBr -> Int -> Set Int -> Set Text -> Set Int -> Maybe DeBrSe
checkSanityObjDeBr obj varStackHeight tmpltVarIndices constSet boundSet = case obj of
     Integ num -> Nothing
     Constant name -> if name `Set.member` constSet then Nothing else (return . ObjDeBrSeConstNotDefd) name
     Hilbert prop -> checkSanityPropDeBr prop varStackHeight tmpltVarIndices constSet (Set.insert (boundDepthPropDeBr prop) boundSet )
     Bound idx -> if idx `Set.member` boundSet then Nothing else (return . ObjDeBrBoundVarIdx) idx
     V idx -> if idx >= 0 && idx < varStackHeight then Nothing else (return . ObjDeBrFreeVarIdx) idx
     X idx -> if idx >= 0 && idx `Set.member` tmpltVarIndices then Nothing else (return . ObjDeBrTemplateVarIdx) idx
     Tupl xs -> msum $ Prelude.map (\x -> checkSanityObjDeBr x varStackHeight tmpltVarIndices constSet boundSet) xs
     -- Check sanity for new ObjDeBr constructors recursively
     (o1 :+: o2) -> checkSanityObjDeBr o1 varStackHeight tmpltVarIndices constSet boundSet <|> checkSanityObjDeBr o2 varStackHeight tmpltVarIndices constSet boundSet -- Updated
     Intneg o1     -> checkSanityObjDeBr o1 varStackHeight tmpltVarIndices constSet boundSet -- Updated
     (o1 :*: o2) -> checkSanityObjDeBr o1 varStackHeight tmpltVarIndices constSet boundSet <|> checkSanityObjDeBr o2 varStackHeight tmpltVarIndices constSet boundSet -- Updated
     IntSet -> Nothing


-- Update checkSanityPropDeBr (No changes needed here, already updated)
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
        (o1 :<=: o2) -> checkSanityObjDeBr o1 freevarStackHeight tmpltVarIndices consts boundVars <|> checkSanityObjDeBr o2 freevarStackHeight tmpltVarIndices consts boundVars -- Updated
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



-- Update propDeBrBoundVarInside (No changes needed here, already updated)
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
    (o1 :<=: o2) -> objDeBrBoundVarInside o1 idx || objDeBrBoundVarInside o2 idx -- Updated
    F -> False


-- Update objDeBrSubXInt
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
    Tupl xs -> Tupl $ Prelude.map (objDeBrSubXInt targetIdx substitution) xs
    (o1 :+: o2) -> (objDeBrSubXInt targetIdx substitution o1) :+: (objDeBrSubXInt targetIdx substitution o2) -- Updated
    Intneg o1     -> Intneg (objDeBrSubXInt targetIdx substitution o1)                                     -- Updated
    (o1 :*: o2) -> (objDeBrSubXInt targetIdx substitution o1) :*: (objDeBrSubXInt targetIdx substitution o2) -- Updated
    IntSet -> IntSet


-- Update propDeBrSubXInt (No changes needed here, already updated)
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
    (o1 :<=: o2) -> objDeBrSubXInt targetIdx substitution o1 :<=: objDeBrSubXInt targetIdx substitution o2 -- Updated
    F -> F


-- Update objDeBrSubX
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
    Tupl xs -> Tupl $ Prelude.map (objDeBrSubX targetIdx substitution) xs
    (o1 :+: o2) -> (objDeBrSubX targetIdx substitution o1) :+: (objDeBrSubX targetIdx substitution o2) -- Updated
    Intneg o1     -> Intneg (objDeBrSubX targetIdx substitution o1)                                     -- Updated
    (o1 :*: o2) -> (objDeBrSubX targetIdx substitution o1) :*: (objDeBrSubX targetIdx substitution o2) -- Updated
    IntSet -> IntSet


-- Update propDeBrSubX (No changes needed here, already updated)
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
    (o1 :<=: o2) -> objDeBrSubX targetIdx substitution o1 :<=: objDeBrSubX targetIdx substitution o2 -- Updated
    F -> F


-- Update swapXtoXIntProp (No changes needed here, already updated)
swapXtoXIntProp :: PropDeBr -> PropDeBr
swapXtoXIntProp p = case p of
    Neg q -> Neg (swapXtoXIntProp q)
    (p1 :&&: p2) -> (swapXtoXIntProp p1) :&&: (swapXtoXIntProp p2)
    (p1 :||: p2) -> (swapXtoXIntProp p1) :||: (swapXtoXIntProp p2)
    (p1 :->: p2) -> (swapXtoXIntProp p1) :->: (swapXtoXIntProp p2)
    (p1 :<->: p2) -> (swapXtoXIntProp p1) :<->: (swapXtoXIntProp p2)
    (o1 :==: o2) -> (swapXtoXIntObj o1) :==: (swapXtoXIntObj o2)
    In o1 o2 -> In (swapXtoXIntObj o1) (swapXtoXIntObj o2)
    Forall q -> Forall (swapXtoXIntProp q)
    Exists q -> Exists (swapXtoXIntProp q)
    (o1 :<=: o2) -> (swapXtoXIntObj o1) :<=: (swapXtoXIntObj o2) -- Updated
    F -> F


-- Update swapXtoXIntObj
swapXtoXIntObj :: ObjDeBr -> ObjDeBr
swapXtoXIntObj o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapXtoXIntProp p)
    Bound i -> Bound i
    V i -> V i
    X i -> XInternal i
    XInternal i -> XInternal i
    Tupl xs -> Tupl $ Prelude.map swapXtoXIntObj xs
    (o1 :+: o2) -> (swapXtoXIntObj o1) :+: (swapXtoXIntObj o2) -- Updated
    Intneg o1     -> Intneg (swapXtoXIntObj o1)               -- Updated
    (o1 :*: o2) -> (swapXtoXIntObj o1) :*: (swapXtoXIntObj o2) -- Updated
    IntSet -> IntSet


-- Update swapXIntToXProp (No changes needed here, already updated)
swapXIntToXProp :: PropDeBr -> PropDeBr
swapXIntToXProp p = case p of
    Neg q -> Neg (swapXIntToXProp q)
    (p1 :&&: p2) -> (swapXIntToXProp p1) :&&: (swapXIntToXProp p2)
    (p1 :||: p2) -> (swapXIntToXProp p1) :||: (swapXIntToXProp p2)
    (p1 :->: p2) -> (swapXIntToXProp p1) :->: (swapXIntToXProp p2)
    (p1 :<->: p2) -> (swapXIntToXProp p1) :<->: (swapXIntToXProp p2)
    (o1 :==: o2) -> (swapXIntToXObj o1) :==: (swapXIntToXObj o2)
    In o1 o2 -> In (swapXIntToXObj o1) (swapXIntToXObj o2)
    Forall q -> Forall (swapXIntToXProp q)
    Exists q -> Exists (swapXIntToXProp q)
    (o1 :<=: o2) -> (swapXIntToXObj o1) :<=: (swapXIntToXObj o2) -- Updated
    F -> F


-- Update swapXIntToXObj
swapXIntToXObj :: ObjDeBr -> ObjDeBr
swapXIntToXObj o = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (swapXIntToXProp p)
    Bound i -> Bound i
    V i -> V i
    X i -> X i
    XInternal i -> X i
    Tupl xs -> Tupl $ Prelude.map swapXIntToXObj xs
    (o1 :+: o2) -> (swapXIntToXObj o1) :+: (swapXIntToXObj o2) -- Updated
    Intneg o1     -> Intneg (swapXIntToXObj o1)               -- Updated
    (o1 :*: o2) -> (swapXIntToXObj o1) :*: (swapXIntToXObj o2) -- Updated
    IntSet -> IntSet


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


-- Update objDeBrApplyUG
objDeBrApplyUG :: ObjDeBr -> Int -> Int -> ObjDeBr
objDeBrApplyUG obj freevarIdx boundvarIdx =
    case obj of
        Integ num -> Integ num
        Constant name -> Constant name
        Hilbert p1 -> Hilbert (propDeBrApplyUG p1 freevarIdx boundvarIdx)
        Bound idx -> Bound idx
        V idx -> if idx == freevarIdx then Bound boundvarIdx else V idx
        Tupl xs -> Tupl $ Prelude.map (\x -> objDeBrApplyUG x freevarIdx boundvarIdx) xs
        (o1 :+: o2) -> (objDeBrApplyUG o1 freevarIdx boundvarIdx) :+: (objDeBrApplyUG o2 freevarIdx boundvarIdx) -- Updated
        Intneg o1     -> Intneg (objDeBrApplyUG o1 freevarIdx boundvarIdx)                                      -- Updated
        (o1 :*: o2) -> (objDeBrApplyUG o1 freevarIdx boundvarIdx) :*: (objDeBrApplyUG o2 freevarIdx boundvarIdx) -- Updated
        IntSet -> IntSet


-- Update propDeBrApplyUG (No changes needed here, already updated)
propDeBrApplyUG :: PropDeBr -> Int -> Int -> PropDeBr
propDeBrApplyUG prop freevarIdx boundvarIdx =
    case prop of
        Neg p -> Neg (propDeBrApplyUG p freevarIdx boundvarIdx)
        (p1 :&&: p2) -> (propDeBrApplyUG p1 freevarIdx boundvarIdx) :&&: (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (p1 :||: p2) -> (propDeBrApplyUG p1 freevarIdx boundvarIdx) :||: (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (p1 :->: p2) -> (propDeBrApplyUG p1 freevarIdx boundvarIdx) :->: (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (p1 :<->: p2) -> (propDeBrApplyUG p1 freevarIdx boundvarIdx) :<->: (propDeBrApplyUG p2 freevarIdx boundvarIdx)
        (o1 :==: o2) -> (objDeBrApplyUG o1 freevarIdx boundvarIdx) :==: (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        In o1 o2 -> In (objDeBrApplyUG o1 freevarIdx boundvarIdx) (objDeBrApplyUG o2 freevarIdx boundvarIdx)
        Forall p -> Forall (propDeBrApplyUG p freevarIdx boundvarIdx)
        Exists p -> Exists (propDeBrApplyUG p freevarIdx boundvarIdx)
        (o1 :<=: o2) -> (objDeBrApplyUG o1 freevarIdx boundvarIdx) :<=: (objDeBrApplyUG o2 freevarIdx boundvarIdx) -- Added
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


-- Update objDeBrSubBoundVarToX0
objDeBrSubBoundVarToX0 :: Int -> ObjDeBr -> ObjDeBr
objDeBrSubBoundVarToX0 boundVarIdx obj = case obj of
    Integ num -> Integ num
    Constant const -> Constant const
    Hilbert p -> Hilbert (propDeBrSubBoundVarToX0 boundVarIdx p)
    Bound idx -> if idx == boundVarIdx then X 0 else Bound idx
    V idx -> V idx
    Tupl xs -> Tupl $ Prelude.map (objDeBrSubBoundVarToX0 boundVarIdx) xs
    (o1 :+: o2) -> (objDeBrSubBoundVarToX0 boundVarIdx o1) :+: (objDeBrSubBoundVarToX0 boundVarIdx o2) -- Updated
    Intneg o1     -> Intneg (objDeBrSubBoundVarToX0 boundVarIdx o1)                                  -- Updated
    (o1 :*: o2) -> (objDeBrSubBoundVarToX0 boundVarIdx o1) :*: (objDeBrSubBoundVarToX0 boundVarIdx o2) -- Updated
    IntSet -> IntSet


-- Update propDeBrSubBoundVarToX0 (No changes needed here, already updated)
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
    (a :<=: b) -> objDeBrSubBoundVarToX0 boundVarIdx a :<=: objDeBrSubBoundVarToX0 boundVarIdx b -- Added
    F -> F


-- Update xsubPropDeBr (No changes needed here, already updated)
xsubPropDeBr :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBr p idx depth = case p of
    Neg q -> Neg (xsubPropDeBr q idx depth)
    (p1 :&&: p2) -> (xsubPropDeBr p1 idx depth) :&&: (xsubPropDeBr p2 idx depth)
    (p1 :||: p2) -> (xsubPropDeBr p1 idx depth) :||: (xsubPropDeBr p2 idx depth)
    (p1 :->: p2) -> (xsubPropDeBr p1 idx depth) :->: (xsubPropDeBr p2 idx depth)
    (p1 :<->: p2) -> (xsubPropDeBr p1 idx depth) :<->: (xsubPropDeBr p2 idx depth)
    (o1 :==: o2) -> (xsubObjDeBr o1 idx depth) :==: (xsubObjDeBr o2 idx depth)
    In o1 o2 -> In (xsubObjDeBr o1 idx depth) (xsubObjDeBr o2 idx depth)
    Forall q -> Forall (xsubPropDeBr q idx depth)
    Exists q -> Exists (xsubPropDeBr q idx depth)
    (o1 :<=: o2) -> (xsubObjDeBr o1 idx depth) :<=: (xsubObjDeBr o2 idx depth) -- Added
    F -> F

-- Update xsubObjDeBr
xsubObjDeBr :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBr o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (xsubPropDeBr p idx depth)
    Bound i -> Bound i
    V i -> V i
    X i -> if i == idx then Bound depth else X i
    XInternal i -> XInternal i
    Tupl xs -> Tupl $ Prelude.map (\x -> xsubObjDeBr x idx depth) xs
    (o1 :+: o2) -> (xsubObjDeBr o1 idx depth) :+: (xsubObjDeBr o2 idx depth) -- Updated
    Intneg o1     -> Intneg (xsubObjDeBr o1 idx depth)                      -- Updated
    (o1 :*: o2) -> (xsubObjDeBr o1 idx depth) :*: (xsubObjDeBr o2 idx depth) -- Updated
    IntSet -> IntSet


-- Update xsubPropDeBrXInt (No changes needed here, already updated)
xsubPropDeBrXInt :: PropDeBr -> Int -> Int -> PropDeBr
xsubPropDeBrXInt p idx depth = case p of
    Neg q -> Neg (xsubPropDeBrXInt q idx depth)
    (p1 :&&: p2) -> (xsubPropDeBrXInt p1 idx depth) :&&: (xsubPropDeBrXInt p2 idx depth)
    (p1 :||: p2) -> (xsubPropDeBrXInt p1 idx depth) :||: (xsubPropDeBrXInt p2 idx depth)
    (p1 :->: p2) -> (xsubPropDeBrXInt p1 idx depth) :->: (xsubPropDeBrXInt p2 idx depth)
    (p1 :<->: p2) -> (xsubPropDeBrXInt p1 idx depth) :<->: (xsubPropDeBrXInt p2 idx depth)
    (o1 :==: o2) -> (xsubObjDeBrXInt o1 idx depth) :==: (xsubObjDeBrXInt o2 idx depth)
    In o1 o2 -> In (xsubObjDeBrXInt o1 idx depth) (xsubObjDeBrXInt o2 idx depth)
    Forall q -> Forall (xsubPropDeBrXInt q idx depth)
    Exists q -> Exists (xsubPropDeBrXInt q idx depth)
    (o1 :<=: o2) -> (xsubObjDeBrXInt o1 idx depth) :<=: (xsubObjDeBrXInt o2 idx depth) -- Added
    F -> F

-- Update xsubObjDeBrXInt
xsubObjDeBrXInt :: ObjDeBr -> Int -> Int -> ObjDeBr
xsubObjDeBrXInt o idx depth = case o of
    Integ num -> Integ num
    Constant name -> Constant name
    Hilbert p -> Hilbert (xsubPropDeBrXInt p idx depth)
    Bound i -> Bound i
    V i -> V i
    X i -> X i
    XInternal i -> if i == idx then Bound depth else XInternal i
    Tupl xs -> Tupl $ Prelude.map (\x -> xsubObjDeBrXInt x idx depth) xs
    (o1 :+: o2) -> (xsubObjDeBrXInt o1 idx depth) :+: (xsubObjDeBrXInt o2 idx depth) -- Updated
    Intneg o1     -> Intneg (xsubObjDeBrXInt o1 idx depth)                      -- Updated
    (o1 :*: o2) -> (xsubObjDeBrXInt o1 idx depth) :*: (xsubObjDeBrXInt o2 idx depth) -- Updated
    IntSet -> IntSet


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


instance ZFC.LogicTerm ObjDeBr where
    parseTuple :: ObjDeBr -> Maybe [ObjDeBr]
    parseTuple = parseTupl
    buildTuple :: [ObjDeBr] -> ObjDeBr
    buildTuple = Tupl


instance ZFC.LogicSent PropDeBr ObjDeBr where
    emptySetAxiom :: PropDeBr
    emptySetAxiom = eX 0 $ Neg $ aX 1 $ X 1 `In` X 0


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
