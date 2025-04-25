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
    parseGTE,
    parseFalsum,
    objDeBrSubXInt,
    propDeBrSubXInt,
    hXInt,
    propDeBrSubXs,
    multiEx,
    multiAx,
    propDeBrSubX


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









objDeBrBoundVarInside :: ObjDeBr -> Int -> Bool
objDeBrBoundVarInside obj idx = case obj of
    Integ num -> False
    Constant const -> False
    Hilbert p -> propDeBrBoundVarInside p idx
    Bound i -> idx == i
    V i -> False
    X i -> False
    Tupl as -> any (`objDeBrBoundVarInside` idx) as




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


parseGTE :: PropDeBr -> Maybe (ObjDeBr, ObjDeBr)
parseGTE p = case p of
    (a :>=: b) -> Just (a, b)
    _ -> Nothing

parseFalsum :: PropDeBr -> Maybe ()
parseFalsum p = case p of
    F -> Just ()
    _ -> Nothing




--instance Show ObjDeBr where
--    show :: ObjDeBr -> String
--    show obj = unpack $ showSubexpParseTree $ toSubexpParseTree obj mempty                         


--instance Show PropDeBr where
--    show :: PropDeBr -> String
--    show obj = unpack $ showSubexpParseTree $ toSubexpParseTree obj mempty




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







-- Helper function to apply a binder function (like eX or aX) for a list of indices.
-- Relies on the binder function itself (e.g., eX, aX) correctly calculating the
-- necessary depth and substituting X idx with the appropriate Bound depth index
-- at each step of the fold.
-- Binds indices from right-to-left (innermost binder corresponds to last index in list).
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
            -- Use fixed internal indices for placeholders.
            internalTIdx = 1 -- Placeholder index for the source set 't' (XInternal 1)
            internalBIdx = 2 -- Placeholder index for the resulting set 'B' (XInternal 2)

            -- Core axiom structure template:
            -- x ∈ B ↔ ( P(x) ∧ x ∈ t_placeholder )
            -- Using X idx for 'x', XInternal internalBIdx for 'B', XInternal internalTIdx for 't'.
            core_prop_template :: PropDeBr
            core_prop_template = (X idx `In` XInternal internalBIdx)
                             :<->:
                             (p_template :&&: (X idx `In` XInternal internalTIdx))

            -- Universally quantify over 'x' (represented by X idx)
            quantified_over_x :: PropDeBr
            quantified_over_x = aX idx core_prop_template

            -- Existentially quantify over the resulting set 'B' (represented by XInternal internalBIdx)
            quantified_over_B :: PropDeBr
            quantified_over_B = eXInt internalBIdx quantified_over_x

            -- **Step 1 (Corrected Order):** Substitute the actual source set term 't'
            -- for the internal placeholder XInternal internalTIdx using propDeBrSubXInt.
            -- The result 'axiom_body_with_t' now contains the actual term 't',
            -- potentially including X i variables from outerIdxs originating from both p_template and t.
            axiom_body_with_t :: PropDeBr
            axiom_body_with_t = propDeBrSubXInt internalTIdx t quantified_over_B

            -- **Step 2 (Corrected Order):** Universally quantify over all outer parameter indices (outerIdxs).
            -- multiAx applies aX i for each i in outerIdxs to 'axiom_body_with_t'.
            -- This binds all remaining X i variables (from p_template and the substituted t).
            closed_axiom :: PropDeBr
            closed_axiom = multiAx outerIdxs axiom_body_with_t

        in
            closed_axiom

    replaceAxiom :: [Int] -> Int -> Int -> ObjDeBr -> PropDeBr -> PropDeBr
    replaceAxiom outerIdxs idx1 idx2 t p_template =
        -- outerIdxs: Indices of template variables (X i) acting as parameters.
        -- idx1: Index for variable 'a' in P(a, b).
        -- idx2: Index for variable 'b' in P(a, b).
        -- t: The source set term (may contain X i for i in outerIdxs).
        -- p_template: The predicate template P(a,b) (may contain X idx1, X idx2, and X i).

        let
            -- Use fixed internal indices for placeholders.
            internalTIdx = 1 -- Placeholder index for the source set 't' (XInternal 1)
            internalBIdx = 2 -- Placeholder index for the resulting set 'B' (XInternal 2)

            -- === Build Premise Template ===
            -- Template for: ∃!b P(a, b)
            -- Uses X idx1 for 'a', X idx2 for 'b', p_template for P.
            exists_unique_b = eXBang idx2 p_template

            -- Template for: a ∈ t → ∃!b P(a, b)
            -- Uses X idx1 for 'a', XInternal internalTIdx for 't'.
            implication_in_premise = (X idx1 `In` XInternal internalTIdx) :->: exists_unique_b

            -- Template for Premise: ∀a (a ∈ t → ∃!b P(a, b))
            -- Uses aX to bind X idx1. Contains XInternal internalTIdx and outer X i's.
            premise_template :: PropDeBr
            premise_template = aX idx1 implication_in_premise


            -- === Build Conclusion Template ===
            -- Template for: b ∈ t ∧ P(a, b)
            -- Uses X idx1 for 'a', X idx2 for 'b', XInternal internalTIdx for 't'.
            conjunction_in_conclusion = (X idx2 `In` XInternal internalTIdx) :&&: p_template

            -- Template for: ∃b (b ∈ t ∧ P(a, b))
            -- Uses eX to bind X idx2. Contains X idx1, XInternal internalTIdx, and outer X i's.
            exists_b_in_conclusion = eX idx2 conjunction_in_conclusion

            -- Template for: a ∈ B ↔ ∃b (b ∈ t ∧ P(a, b))
            -- Uses X idx1 for 'a', XInternal internalBIdx for 'B'.
            bicond_in_conclusion = (X idx1 `In` XInternal internalBIdx) :<->: exists_b_in_conclusion

            -- Template for: ∀a (a ∈ B ↔ ∃b (b ∈ t ∧ P(a, b)))
            -- Uses aX to bind X idx1. Contains XInternal internalBIdx, XInternal internalTIdx, and outer X i's.
            forall_a_in_conclusion = aX idx1 bicond_in_conclusion

            -- Template for Conclusion: ∃B ∀a (a ∈ B ↔ ∃b (b ∈ t ∧ P(a, b)))
            -- Uses eXInt to bind XInternal internalBIdx. Contains XInternal internalTIdx and outer X i's.
            conclusion_template :: PropDeBr
            conclusion_template = eXInt internalBIdx forall_a_in_conclusion


            -- === Assemble and Finalize ===
            -- Template for the full axiom: Premise → Conclusion
            -- Contains XInternal internalTIdx and outer X i's.
            axiom_template_pre_subst :: PropDeBr
            axiom_template_pre_subst = premise_template :->: conclusion_template

            -- **Step 1:** Substitute the actual source set term 't' for the internal placeholder XInternal internalTIdx.
            -- The result 'axiom_body_with_t' now contains 't' (potentially with outer X i's)
            -- and any outer X i's from the original p_template.
            axiom_body_with_t :: PropDeBr
            axiom_body_with_t = propDeBrSubXInt internalTIdx t axiom_template_pre_subst

            -- **Step 2:** Universally quantify over all outer parameter indices (outerIdxs).
            -- multiAx binds all remaining X i variables.
            closed_axiom :: PropDeBr
            closed_axiom = multiAx outerIdxs axiom_body_with_t

        in
            closed_axiom
     
                              
            
                           
      
 



 





