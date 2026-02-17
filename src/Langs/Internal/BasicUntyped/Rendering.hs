{-# LANGUAGE StandaloneDeriving #-}
module Langs.Internal.BasicUntyped.Rendering (
    printPropDeBrStepsBase,
    showProp,
    showObj,
    showPropM,
    showObjM
) where

import Langs.Internal.BasicUntyped.Core
import Langs.Internal.BasicUntyped.Shorthands
import Control.Monad ( unless, guard,msum, zipWithM, when )
import Data.List (intersperse,findIndex, partition,sort,find)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Data.Set(Set, notMember)
import qualified Data.Set as Set (fromList,insert,member)
import Control.Applicative ( Alternative((<|>)) )

import Control.Monad.Except ( MonadError(throwError) )
import Kernel

import Internal.StdPattern

import Control.Exception (SomeException)
import qualified RuleSets.PropLogic.Core as PL
import qualified RuleSets.PredLogic.Core as PREDL
import qualified RuleSets.ZFC.Core as ZFC
import RuleSets.PropLogic.Core (LogicSent(parseIff))
import RuleSets.ZFC.Core (specification,parseMemberOf,memberOf)
import Control.Monad.State
import Control.Monad.RWS
    ( MonadReader(ask), runRWS, MonadWriter(tell), RWS , RWST, runRWST)
import Text.XHtml (sub)
import qualified Internal.StdPattern
import Data.Maybe (isJust)

import Data.Text (Text, pack, unpack,concat, lines,intercalate,breakOn)
import qualified Data.Text as T
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
import qualified Data.Text.Read as TR
import Data.Char (isDigit)
import Internal.StdPattern (PrfStdContext(mayParentState))
import Text.ParserCombinators.ReadPrec (step)
import Data.Data (Typeable)
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import Text.Regex.TDFA

data SubexpParseTree where
    BinaryOp :: Text -> SubexpParseTree -> SubexpParseTree -> SubexpParseTree
    UnaryOp :: Text -> SubexpParseTree ->SubexpParseTree
    Binding :: Text -> SubexpParseTree -> SubexpParseTree
    HilbertShort :: [Int] -> SubexpParseTree
    ParseTreeConst :: Text -> SubexpParseTree
    ParseTreeFreeVar :: Int -> SubexpParseTree
    ParseTreeBoundVar :: Int -> SubexpParseTree
    ParseTreeX :: Int -> SubexpParseTree
    ParseTreeXInternal :: Int -> SubexpParseTree
    Tuple :: [SubexpParseTree] -> SubexpParseTree
    Roster :: [SubexpParseTree] -> SubexpParseTree
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
    ParseTreeXInternal idx -> 0
    Tuple as -> maximum $ Prelude.map subexpParseTreeBoundDepth as
    Roster as -> maximum $ Prelude.map subexpParseTreeBoundDepth as
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
            Roster as -> Roster $ Prelude.map (sbParseTreeNormalize' depth) as
            ParseTreeX idx -> ParseTreeX idx
            ParseTreeXInternal idx -> ParseTreeXInternal idx
            ParseTreeF -> ParseTreeF
            ParseTreeInt i -> ParseTreeInt i
            Builder sub1 sub2 -> Builder (sbParseTreeNormalize' depth sub1) (sbParseTreeNormalize' depth sub2)
            FuncApp sub1 sub2 -> FuncApp (sbParseTreeNormalize' depth sub1) (sbParseTreeNormalize' depth sub2)
            TupleProject n obj -> TupleProject n (sbParseTreeNormalize' depth obj)
  

class SubexpDeBr sub where
    toSubexpParseTree :: sub -> Map PropDeBr [Int] -> SubexpParseTree


binaryOpInData :: [(Text,(Associativity,Int))]
binaryOpInData = [
    -- Logical Operators
    ("→", (RightAssociative, 1)), -- Implication: Right assoc, lowest precedence (standard)
    --
    ("↔", (RightAssociative, 1)), -- Biconditional: Right assoc (common), same low precedence as →
    --
    ("∨", (RightAssociative, 3)), -- Logical OR: Right assoc (common), precedence higher than →/↔
    --
    ("∧", (RightAssociative, 4)), -- Logical AND: Right assoc (common), precedence higher than ∨ (standard)
    --

    -- Relational Operators (Equality, Membership, Ordering, Subsets)
    ("=", (NotAssociative, 5)),   -- Equality: Non-associative (standard), precedence higher than logical
    --
    ("≠", (NotAssociative, 5)),   -- Inequality: Non-associative, same precedence as =
    --
    ("∈", (NotAssociative, 5)),   -- Set Membership: Non-associative, same precedence as =
    --
    ("∉", (NotAssociative, 5)),   -- Not Set Membership: Non-associative, same precedence as =
    --
    ("≤", (NotAssociative, 5)),   -- Less/Equal: Non-associative, same precedence as =
    --
    ("⊆", (NotAssociative, 5)),   -- Subset/Equal: Non-associative, same precedence as =
    --
    ("⊂", (NotAssociative, 5)),   -- Proper Subset: Non-associative, same precedence as =
    --
    ("⊈", (NotAssociative, 5)),   -- Not Subset/Equal: Non-associative, same precedence as =
    ("<", (NotAssociative, 5)),   -- Less than: Non-associative, same precedence as =
    -- Note: Other relations like <, >, ≥, ⊇, ⊃, etc., would also typically go here (NotAssociative, 5)

    -- Set Operators
    ("∪", (RightAssociative, 3)), -- Set Union: Right assoc (common convention), precedence same as ∨
    --
    ("∩", (RightAssociative, 4)), -- Set Intersection: Right assoc (common convention), precedence same as ∧
    --
    ("∖", (LeftAssociative, 6)),  -- Set Difference: Changed to Left assoc (more intuitive like subtraction), precedence raised to level 6 (like +)
    --


    -- Arithmetic / Algebraic Operators
    ("+", (LeftAssociative, 6)),   -- Addition: Left associative (standard), precedence higher than relations
    ("×", (LeftAssociative, 7)),   -- Multiplication: Left associative (standard), precedence higher than +
    ("⨯", (LeftAssociative, 7)),   -- Cartesian Product: Left associative, same precedence as ×

    -- Function/Relation Composition
    ("∘", (RightAssociative, 9))  -- Composition: Right associative (standard), highest precedence
  ]



     --The Int is it's precedence number.
binaryOpData :: Map Text (Associativity, Int)
binaryOpData = Data.Map.fromList binaryOpInData


instance SubexpDeBr ObjDeBr where
    toSubexpParseTree :: ObjDeBr -> Map PropDeBr [Int] -> SubexpParseTree
    



    toSubexpParseTree obj dict =
         maybe (error $ "Unable to parse term " <> show obj <> ". This shouldn't have happened.")
             id fullParse 
      where fullParse =
                  parseNatSet'
              <|> parseIntSet'
              <|> parseInteg'
              <|> parseConst'
              <|> parseBound'
              <|> parseV'
              <|> parseX'
              <|> parseXInternal'
              <|> parseEmptySet'
              <|> parseTuple'
              <|> parseIntMult'
              <|> parseIntPlus'
              <|> parseIntNeg'
              <|> parseRoster'
              <|> parsePowerSet'
              <|> parseBigUnion'
              <|> parseBigIntersection'
              <|> parseFuncsSet'
              <|> parseProject'
              <|> parseFuncApplication'
              <|> parseCrossProduct'
              <|> parseComposition'
              <|> parseBinaryUnion'
              <|> parseIntersectionOp'
              <|> parseSetDifference'
              <|> parseSetBuilder'
              <|> parseHilbertShort'
              <|> parseHilbert'
            parseNatSet' =
                do
                    parseNatSet obj
                    return $ ParseTreeConst "ℕ"

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
            parseXInternal' = do
                i <- parseXInternal obj
                return $ ParseTreeXInternal i
            parseInteg' = do
                i <- parseInteg obj
                return $ ParseTreeInt i

            parseTuple' = do
               tuple <- parseTupleMax obj
               return $ Tuple $ Prelude.map  (`toSubexpParseTree` dict) tuple
            parseRoster' = do
               roster <- parseRoster obj
               return $ Roster $ Prelude.map  (`toSubexpParseTree` dict) roster



            parseComposition' = do
                (f,g) <- parseComposition obj
                return $ BinaryOp "∘" (toSubexpParseTree f dict) (toSubexpParseTree g dict)
            parseProject' = do
                (i, o) <- parseProjectHilbert obj
                let pTree = toSubexpParseTree o dict
                return $ TupleProject i pTree
            parseCrossProduct' = do
                (a,b) <- parseCrossProduct obj
                return $ BinaryOp "⨯" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
            parseFuncsSet'= do
                (a,b) <- parseFuncsSet obj
                let treeA = toSubexpParseTree a dict
                let treeB = toSubexpParseTree b dict
                return $ FuncApp (ParseTreeConst "𝗙𝗨𝗡𝗖𝗦") (Tuple [treeA, treeB])
            parseBinaryUnion' = do
                (a,b) <- parseBinaryUnion obj
                return $ BinaryOp "∪" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
            parseIntersectionOp' = do
                            (a,b) <- parseIntersectionOp obj
                            return $ BinaryOp "∩" (toSubexpParseTree a dict) (toSubexpParseTree b dict) 
            parseBigUnion' = do
                setS <- parseBigUnion obj
                return $ UnaryOp "∪" (toSubexpParseTree setS dict)

            parseBigIntersection' = do
                setS <- parseBigIntersection obj
                return $ UnaryOp "∩" (toSubexpParseTree setS dict)
            parseSetDifference' = do
                (a, b) <- parseSetDifference obj
                return $ BinaryOp "∖" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
            parsePowerSet' = do
                setA <- parsePowerSet obj
                return $ FuncApp (ParseTreeConst "𝒫") (toSubexpParseTree setA dict)
            parseEmptySet' = do
                parseEmptySet obj
                return $ ParseTreeConst "∅"
            parseIntNeg' = do
                subexp <- parseIntNeg obj
                return $ UnaryOp "-" (toSubexpParseTree subexp dict)
            parseIntMult' = do
                (o1,o2) <- parseIntMult obj
                return $ BinaryOp "×" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)
            parseIntPlus' = do
                (o1,o2) <- parseIntPlus obj
                return $ BinaryOp "+" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)
            parseIntSet' = do
                () <- parseIntSet obj
                return $ ParseTreeConst "ℤ"



            


instance SubexpDeBr PropDeBr where
  toSubexpParseTree :: PropDeBr -> Map PropDeBr [Int] -> SubexpParseTree
  toSubexpParseTree prop dict =
      maybe (error $ "Unable to parse proposition " <> show prop <> ". This shouldn't have happened.")
          id fullParse
    where
      fullParse =
            parseLessThan'      -- Less than shorthand first
        <|> parseNotEqual'      -- Negation shorthands first
        <|> parseNotIn'
        <|> parseNotSubset'
        <|> parseNegation'      -- Default negation
        <|> parseStrictSubset'  -- Conjunction shorthand first
        <|> parseSubset'        -- Forall shorthand first
        <|> parseForall2'       -- Default forall

        <|> parseExistsUnique'  -- Exists shorthand first
        <|> parseExists'        -- Default exists

        <|> parseConjunction'   -- Default conjunction
        <|> parseDisjunction'   -- Other standard operators
        <|> parseImplication'
        <|> parseBiconditional'
        <|> parseEqual'
        <|> parseIn'
        <|> parseLTE'
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
      parseLTE' = do
          (a, b) <- parseLTE prop
          return $ BinaryOp "≤" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
      parseFalsum' = do
          () <- parseFalsum prop
          return ParseTreeF
      parseLessThan' = do
          (o1, o2) <- parseLessThan prop
          return $ BinaryOp "<" (toSubexpParseTree o1 dict) (toSubexpParseTree o2 dict)



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
              Roster as -> showSubexpParseTree sub1
              ParseTreeF -> showSubexpParseTree sub1
              ParseTreeX idx -> showSubexpParseTree sub1
              ParseTreeXInternal idx -> showSubexpParseTree sub1
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
              Roster as -> showSubexpParseTree sub1
              ParseTreeF -> showSubexpParseTree sub1
              ParseTreeX idx -> showSubexpParseTree sub1
              ParseTreeXInternal idx -> showSubexpParseTree sub1
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
               Roster as -> showSubexpParseTree sub2
               ParseTreeF -> showSubexpParseTree sub2
               ParseTreeX idx -> showSubexpParseTree sub2
               ParseTreeXInternal idx -> showSubexpParseTree sub2
               ParseTreeInt i -> showSubexpParseTree sub2
               Builder {} -> showSubexpParseTree sub2
               FuncApp {} -> showSubexpParseTree sub2
               TupleProject {} -> showSubexpParseTree sub2


    Binding quant sub1 -> quant <> "𝑥" <> showIndexAsSubscript idx <> "(" <> showSubexpParseTree sub1 <> ")"
        where
            idx = subexpParseTreeBoundDepth sub1 
    ParseTreeConst const -> const
    ParseTreeX idx -> "X" <> showIndexAsSubscript idx
    ParseTreeXInternal idx -> "XInternal" <> showIndexAsSubscript idx
    ParseTreeFreeVar idx -> "𝑣" <> showIndexAsSubscript idx
    ParseTreeBoundVar idx -> "𝑥" <> showIndexAsSubscript idx


    HilbertShort idx -> "ε" <> showHierarchalIdxAsSubscript idx
    Tuple as -> "(" <> Data.Text.concat (intersperse "," $ Prelude.map showSubexpParseTree as ) <> ")"
    Roster as -> "{" <> Data.Text.concat (intersperse "," $ Prelude.map showSubexpParseTree as ) <> "}"
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
    FuncApp f x -> fDisplay <> funcArgDisplay x
        where
            fDisplay = case f of
                FuncApp _ _ -> "(" <> showSubexpParseTree f <> ")"
                _ -> showSubexpParseTree f
    TupleProject idx obj ->  "𝛑" <> showIndexAsSubscript idx <> funcArgDisplay obj
  where 
    showHierarchalIdxAsSubscript :: [Int] -> Text
    showHierarchalIdxAsSubscript idxs = Data.Text.concat (intersperse "." (Prelude.map showIndexAsSubscript idxs))
    -- showHierarchalIdxAsSubscript idxs = "{%i" <> Data.Text.concat (intersperse "." (Prelude.map (pack . show) idxs)) <> "%}"
    assoc opSymb = fst $ binaryOpData!opSymb
    prec opSymb = snd $ binaryOpData!opSymb
    funcArgDisplay x = case x of
        Tuple _ -> showSubexpParseTree x
        _ -> "(" <> showSubexpParseTree x <> ")"




showObj :: Map PropDeBr [Int] -> ObjDeBr -> Text
showObj dict obj = showSubexpParseTree $ toSubexpParseTree obj dict



showObjM :: (Monad m, Monoid r, 
             Proof eL r (PrfStdState PropDeBr Text () ObjDeBr) 
                (PrfStdContext () PropDeBr Text () ObjDeBr) [PrfStdStep PropDeBr Text () ObjDeBr] PropDeBr) 
                     => ObjDeBr -> ProofGenTStd () r PropDeBr Text () ObjDeBr m Text
showObjM obj = 
    do
      state <- getProofState
      let dict = provenSents state
      return $ showObj dict obj
           

showProp :: Map PropDeBr [Int] -> PropDeBr -> Text
showProp dict prop = showSubexpParseTree $ toSubexpParseTree prop dict

showPropM :: (Monad m, Monoid r, 
             Proof eL r (PrfStdState PropDeBr Text () ObjDeBr) 
                 (PrfStdContext () PropDeBr Text () ObjDeBr) [PrfStdStep PropDeBr Text () ObjDeBr] PropDeBr) 
                     => PropDeBr -> ProofGenTStd () r PropDeBr Text () ObjDeBr m Text
showPropM obj = 
    do
      state <- getProofState
      let dict = provenSents state
      return $ showProp dict obj


subscriptCharTable :: [Text]
subscriptCharTable = ["₀","₁","₂","₃","₄","₅","₆","₇","₈","₉"]

showIndexAsSubscript :: Int -> Text
showIndexAsSubscript n = 
    let
         absConvertFunc n = Data.Text.concat (Prelude.map f (show n))
            where
                 f char = subscriptCharTable!!read [char]
    in 
        if n < 0 then
            "₋" <> absConvertFunc (abs n)
        else
            absConvertFunc n

-- data PropDeBrStepContext where
--  PropDeBrStepContext :: {stepContextFrames :: [Bool],
--                            lineIndex :: [Int],
--                            -- notFromMonad :: Bool,
--                            lastLineNum :: Int,
--                            mayParentState :: Maybe PropDeBrStepState } ->
--                           PropDeBrStepContext

-- data PropDeBrStepState where
--    PropDeBrStepState :: {sentMap :: Map PropDeBr [Int],
--                          constMap :: Map Text [Int],
--                          stpCount :: Int} -> PropDeBrStepState

-- prfStdStateToPropDeBrStepState :: PrfStdState PropDeBr Text () -> PropDeBrStepState
-- prfStdStateToPropDeBrStepState prfState =
--    let dictMap = provenSents prfState
--        cnstMap = fmap snd (consts prfState)
--    in PropDeBrStepState {
--        sentMap = dictMap,
--        constMap = cnstMap,
--        stpCount = 1
--    }

-- propDeBrStepStateToPrfStdState :: PropDeBrStepState -> PrfStdState PropDeBr Text () 
-- propDeBrStepStateToPrfStdState stepState =
--    let dictMap = sentMap stepState
--        cnstMap = constMap stepState
--        prfSents = dictMap
--        prfConsts = fmap (\idx -> ((), idx)) cnstMap
--    in PrfStdState {
--        provenSents = prfSents,
--        consts = prfConsts,
--        stepCount = stpCount stepState
--    }


data TagRenderError where
    TagNotDefined :: Text -> Text -> TagRenderError
    TaggedPropNotIndexed :: Text -> Text -> PropDeBr -> TagRenderError
    TaggedTermNotIndexed :: Text -> Text -> ObjDeBr -> TagRenderError
    RemarkTagsNotXlateable :: Text -> Text -> TagRenderError
    RawTextTagNotIndexable :: Text -> Text -> TagRenderError
     deriving (Typeable, Show)

instance Exception TagRenderError


convertRemText ::
                  Map PropDeBr [Int] 
               -> Map Text [Int]
               -> Map Text (TagData PropDeBr ObjDeBr) 
               -> Map Text [Int]
               -> Text 
               -> Either TagRenderError Text
convertRemText sentIdxs constIdxs tagDict remarkTagIdxs input = go input
  where
    go :: Text -> Either TagRenderError Text
    go text 
      | T.null text = Right ""
      | otherwise = 
          let (prefix, rest) = T.breakOn "{" text
          in if T.null rest 
             then Right prefix -- No more tags found
             else 
               let afterOpen = T.drop 1 rest
               in if T.null afterOpen 
                  then Right (prefix <> "{") -- dangling "{"
                  else case T.head afterOpen of
                     '%' -> handlePattern "%}" handleTagContent (T.drop 1 afterOpen) prefix
                     '@' -> handlePattern "@}" handleIndexContent (T.drop 1 afterOpen) prefix
                     _   -> do 
                         restConv <- go afterOpen
                         Right (prefix <> "{" <> restConv)

    handlePattern closer handler content prefix =
        let (tagBlock, remainder) = T.breakOn closer content
        in if T.null remainder
           then Right (prefix <> "{" <> (if closer == "%}" then "%" else "@") <> content)
           else do
               let tagName = tagBlock
               replacement <- handler tagName
               restConverted <- go (T.drop (T.length closer) remainder)
               Right (prefix <> replacement <> restConverted)

    handleTagContent tagName =
        case tagName of 
             "[%" -> Right "{%"
             "%]" -> Right "%}"
             "[@" -> Right "{@"
             "@]" -> Right "@}" 
             _ ->
                case Data.Map.lookup tagName tagDict of
                   Nothing -> Left (TagNotDefined tagName input)
                   Just (TagDataTerm term) -> Right (showTerm sentIdxs term)
                   Just (TagDataSent sent) -> Right (showSent sentIdxs sent)
                   Just TagDataRemark -> Left (RemarkTagsNotXlateable tagName input)
                   Just (TagDataRawText raw) -> Right raw
    handleIndexContent tagName =
        case Data.Map.lookup tagName tagDict of
            Nothing -> Left (TagNotDefined tagName input)
            Just (TagDataSent sent) -> 
                case Data.Map.lookup sent sentIdxs of
                    Just idxs -> Right (showIndex idxs)
                    Nothing -> Left (TaggedPropNotIndexed tagName input sent)
            Just (TagDataTerm term) ->        
                case term of
                   Constant c -> 
                        case Data.Map.lookup c constIdxs of
                             Just idxs -> Right (showIndex idxs)
                             Nothing -> Left (TaggedTermNotIndexed tagName input term) -- LogicTerm mismatch error type?
                   _ -> Left (TaggedTermNotIndexed tagName input term)
            Just TagDataRemark -> case Data.Map.lookup tagName remarkTagIdxs of
                    Just idxs -> Right (showIndex idxs)
                    Nothing -> error "Remark tag index lookup failed. This shouldn't happen since remark tags should be defined in the tag dictionary if they are being indexed."
            Just (TagDataRawText raw) -> Left (RawTextTagNotIndexable tagName input)
      where             
        showIndex i = if Prelude.null i then "" else Data.Text.concat (intersperse "." (Prelude.map (pack . show) i))

printPropDeBrStep :: (MonadIO m,MonadThrow m) => 
       Int -> Bool -> PrfStdStep PropDeBr Text () ObjDeBr
          -> RWST (PrfStdContext () PropDeBr Text () ObjDeBr) Text 
                (PrfStdState PropDeBr Text () ObjDeBr) m ()
printPropDeBrStep lastLineN notMonadic step = do
        context <- ask
        let cf = contextFrames context
        let lIndex = stepIdxPrefix context
        state <- get
        let dictMap = provenSents state
        let cnstMap = fmap snd (consts state)
        let lineNum = stepCount state
        let mayPrntState = mayParentState context
        let oldTagData = tagData state
        let oldTagIdxs = remarkTagIdxs state
        case step of
            PrfStdStepTagObject tagName obj ->
              unless notMonadic $ do
                    liftIO $ putStr $ unpack $ contextFramesShown cf
                    liftIO $ putStr $ unpack $ "[" <> tagName <> "]: "
                -- tag lines are not indexed since they are not proof steps, but organizational markers. 
                -- If we indexed them, it would be confusing since they don't represent propositions or constants that can be referenced in justifications.
            PrfStdStepRemark remarkText (Just tagName) -> do
                liftIO $ putStr $ unpack $ contextFramesShown cf
                liftIO $ putStr $ unpack $ showIndex lIndex
                      <> (if (not . Prelude.null) lIndex then "." else "")
                      <> (pack . show) lineNum
                unless notMonadic $ do
                        liftIO $ putStr $ unpack $ "[" <> tagName <> "]"
                liftIO  $ putStr ": "
            _ -> 
                liftIO $ do
                    liftIO $ putStr $ unpack $ contextFramesShown cf
                    putStr $ unpack $ showIndex lIndex
                      <> (if (not . Prelude.null) lIndex then "." else "")
                      <> (pack . show) lineNum
                      <> ": "
        let newIndex = lIndex <> [lineNum]
        let qed = if notMonadic && lineNum == lastLineN && (not . null) cf then " ◻" else ""
        case step of
            PrfStdStepStep prop justification mayConst depends -> do
                let newDictMap = insert prop newIndex dictMap
                let newConstMap = maybe cnstMap (\const -> insert const newIndex cnstMap) mayConst
                let newConstMapFull = fmap (\const -> ((),const)) newConstMap
                -- put $ PrfStdState newDictMap newConstMap (lineNum + 1)
                put $ PrfStdState {
                    provenSents = newDictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData = oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                liftIO $ putStr $ unpack $ showProp newDictMap prop
                       <> "    "
                       <> justification
                       <> showIndices depends dictMap
                       <> qed
            PrfStdStepLemma prop -> do
                let idxTxt = case mayPrntState of
                      Just parentState ->
                         let 
                            sMap = provenSents parentState
                            mayIdx = Data.Map.lookup prop sMap
                         in
                            case mayIdx of
                                Just idx -> (("[⬅ " <>) . (<> "]") . showIndex) idx
                                Nothing -> error $ "Parent context state index map does not contain proposition: " <> show prop
                      Nothing -> ""
                let newDictMap = insert prop newIndex dictMap
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                -- put $ PropDeBrStepState newDictMap cnstMap (lineNum + 1)
                put $ PrfStdState {
                    provenSents = newDictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }

                liftIO $ putStr $ unpack $ showProp newDictMap prop
                       <> "    LEMMA"
                       <> idxTxt
                       <> qed
            PrfStdStepConst constName _ -> do
                let idxTxt = case mayPrntState of
                      Just parentState ->
                         let 
                            cMap = consts parentState
                            mayIdx = Data.Map.lookup constName cMap
                         in
                            case mayIdx of
                                Just (_,idx) -> (("[⬅ " <>) . (<> "]") . showIndex) idx
                                Nothing -> error $ "Parent context state index map does not contain const: " <> unpack constName <> " " <> show cMap
                      Nothing -> ""
                let newConstMap = insert constName newIndex cnstMap
                let newConstMapFull = fmap (\const -> ((),const)) newConstMap
                put $ PrfStdState {
                    provenSents = dictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData = oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                
                liftIO $ putStr $ unpack $ "Const "
                     <> (pack .show) constName
                     <> "    CONSTDEF"
                     <> idxTxt
            PrfStdStepTheorem prop steps -> do
                let newDictMap = insert prop newIndex dictMap
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                put $ PrfStdState {
                    provenSents = newDictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                liftIO $ putStr $ unpack $ showProp newDictMap prop
                       <> "    THEOREM"
                       <> qed
                
                printSubproofF steps True notMonadic mempty mempty cf [] state oldTagData oldTagIdxs
                
            PrfStdStepSubproof prop subproofName steps -> do
                let newDictMap = insert prop newIndex dictMap
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                put $ PrfStdState {
                    provenSents = newDictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=oldTagData,
                    remarkTagIdxs = oldTagIdxs
                    
                }
                liftIO $ putStr $ unpack $ showProp newDictMap prop
                       <> "    "
                       <> subproofName
                       <> qed
                printSubproofF steps False notMonadic newDictMap cnstMap cf newIndex state oldTagData oldTagIdxs
            PrfStdStepTheoremM prop -> do
                let newDictMap = insert prop newIndex dictMap
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                put $ PrfStdState {
                    provenSents = newDictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                liftIO $ putStr $ unpack $ showProp newDictMap prop
                       <> "    ALGORITHMIC_THEOREM"
                       <> qed
            PrfStdStepFreevar index _ -> do
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                put $ PrfStdState {
                    provenSents = dictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                liftIO $ putStr $ unpack $ "FreeVar 𝑣"
                     <> showIndexAsSubscript index
                     <> "    VARDEF"
            PrfStdStepFakeConst constName _ -> do
                let newConstMap = insert constName newIndex cnstMap
                let newConstMapFull = fmap (\const -> ((),const)) newConstMap
                put $ PrfStdState {
                    provenSents = dictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                liftIO $ putStr $ unpack $ "Const "
                     <> constName
                     <> "    FAKE_CONST"
            PrfStdStepRemark text mayTag -> do
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                put $ PrfStdState {
                    provenSents = dictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum + 1,
                    tagData=maybe oldTagData (\tag -> Data.Map.insert tag TagDataRemark oldTagData) mayTag,
                    remarkTagIdxs = maybe oldTagIdxs (\tag -> insert tag newIndex oldTagIdxs) mayTag
                }
                convertedRem <- either throwM return (convertRemText dictMap cnstMap oldTagData oldTagIdxs text)
                --convertedRem = text
                liftIO $ putStr $ unpack $ "REMARK"
                     <> qed
                     <> (if text == "" then "" else "\n" <> contextFramesShown cf <> "║") 
                     <> intercalate ("\n" <> contextFramesShown cf <> "║") (Data.Text.lines convertedRem)
                     <> "\n"
                     <> contextFramesShown cf
                     <> "╚"
            PrfStdStepTagObject tagName tagObj -> do
                let newConstMapFull = fmap (\const -> ((),const)) cnstMap
                put $ PrfStdState {
                    provenSents = dictMap,
                    consts = newConstMapFull,
                    stepCount = lineNum,
                    tagData=Data.Map.insert tagName tagObj oldTagData,
                    remarkTagIdxs = oldTagIdxs
                }
                unless notMonadic $ liftIO $ putStr $ unpack $ tagText
                   where
                      tagText = case tagObj of
                        TagDataTerm obj -> showObj dictMap obj
                        TagDataSent prop -> showProp dictMap prop
                        TagDataRawText raw -> "<raw text>"
        -- let eol = if lineNum < lastLineN then "\n" else ""
        when (lineNum < lastLineN && not (isTagStep step)) (liftIO $ putStrLn "")
           
        -- liftIO $ putStrLn $ unpack  eol
        -- return ()
      where
        isTagStep step = case step of
            PrfStdStepTagObject _ _ -> True
            _ -> False
        contextFramesShown cf = Data.Text.concat (Prelude.map mapBool cf)
        mapBool frameBool =  if frameBool
                                then
                                    "┃"
                                else
                                    "│"
        showIndices deps sentIndexMap = if Prelude.null deps then "" else "[" 
                            <> Data.Text.concat (intersperse "," (Prelude.map (showIndexDepend sentIndexMap) deps))
                            <> "]"
        showIndexDepend sentIndexMap s = maybe "?" showIndex (Data.Map.lookup s sentIndexMap)
        showIndex i = if Prelude.null i then "" else Data.Text.concat (intersperse "." (Prelude.map (pack . show) i))
        printSubproofF steps isTheorem notMonadic dictMap constMap cf newIndex state tagData remarkTagIdxs = liftIO $ 
                    when notMonadic $ do
                              putStr "\n"
                              let newContext = PrfStdContext {
                                 freeVarTypeStack = [], -- this may not be correct but we don't need free var types for printing so it should be fine
                                 stepIdxPrefix = newIndex,
                                 contextFrames = cf <> [isTheorem],
                                 mayParentState = Just state
                              }
                              let newState = PrfStdState{
                                    provenSents = newDictMap,
                                    consts = fmap (\const -> ((),const)) newConstMap,
                                    stepCount = 0,
                                    tagData = newTagData,
                                    remarkTagIdxs = newTagIdxs
                              }
                              printPropDeBrSteps newContext newState notMonadic steps
                              putStr "\n"
                              putStr $ unpack (Data.Text.concat (Prelude.map mapBool cf)) <>  cornerFrame
                     where
                        newDictMap = if isTheorem then
                                        mempty
                                        else
                                        dictMap
                        newConstMap = if isTheorem then
                                        mempty
                                      else
                                        constMap
                        newTagData = if isTheorem then
                                        mempty
                                     else
                                        tagData
                        newTagIdxs = if isTheorem then
                                        mempty
                                     else
                                        remarkTagIdxs
                        cornerFrame = if isTheorem then
                                 "┗"
                              else
                                  "└"




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

instance StdPrfPrintMonad () PropDeBr Text () ObjDeBr IO where
  

  printSteps :: PrfStdContext () PropDeBr Text () ObjDeBr
    -> PrfStdState PropDeBr Text () ObjDeBr
    -> Bool
    -> [PrfStdStep PropDeBr Text () ObjDeBr]
    -> IO ()
  printSteps context state printSubsteps steps = do
    printPropDeBrSteps context state printSubsteps steps
    putStrLn ""



instance StdPrfPrintMonad () PropDeBr Text () ObjDeBr (Either SomeException) where
         
  
  printSteps :: 
       PrfStdContext () PropDeBr Text () ObjDeBr
    -> PrfStdState PropDeBr Text () ObjDeBr
    -> Bool
    -> [PrfStdStep PropDeBr Text () ObjDeBr]
    -> Either SomeException ()
  printSteps _ _ _ _ = return ()



printPropDeBrSteps ::
         PrfStdContext () PropDeBr Text () ObjDeBr  -- context 
      -> PrfStdState PropDeBr Text () ObjDeBr     -- state
      -> Bool                     -- notFromMonad
      -> [PrfStdStepPredDeBr]     -- steps
      -> IO ()
printPropDeBrSteps context state notFromMonad steps = do

    runRWST (mapM_ (printPropDeBrStep lastLineN notFromMonad) steps) context state
    return ()
        where
            stepsToCount = Prelude.filter (not . isTagStep) steps

            isTagStep step = case step of
                PrfStdStepTagObject _ _ -> True
                _ -> False 
            lastLineN = 
                                stepCount state + length stepsToCount - 1
            --state = PropDeBrStepState dictMap constMap startLine



--showPropDeBrSteps :: [Bool] -> [Int] -> Int -> Bool -> Map PropDeBr [Int] -> Map Text [Int] -> [PrfStdStepPredDeBr] -> Maybe PropDeBrStepState -> Text
--showPropDeBrSteps contextFrames index startLine notFromMonad dictMap constMap steps mayPrentState = 

--    resultText runResult
--    where
--       lastLineN = startLine + length steps - 1
--       runResult = runRWS (mapM_ (showPropDeBrStep notFromMonad) steps) context state
--       resultText (a,b,c) = c
--       context = PropDeBrStepContext contextFrames index lastLineN mayPrentState
--       state = PropDeBrStepState dictMap constMap startLine


-- showPropDeBrStepsBase :: [PrfStdStepPredDeBr] -> Text
-- showPropDeBrStepsBase steps = showPropDeBrSteps [] [] 0 True mempty mempty steps Nothing

printPropDeBrStepsBase :: [PrfStdStepPredDeBr] -> IO ()
printPropDeBrStepsBase steps = do
    printPropDeBrSteps mempty mempty True steps
    putStrLn ""


--showPropDeBrStepsBaseM :: (Monad m, Monoid r, 
--             Proof eL r (PrfStdState PropDeBr Text ()) (PrfStdContext () PropDeBr Text ()) [PrfStdStep PropDeBr Text ()] PropDeBr) 
--                     => [PrfStdStepPredDeBr] -> ProofGenTStd () r PropDeBr Text () m Text
--showPropDeBrStepsBaseM steps = do 
--      state <- getProofState
--      let dict = provenSents state
--      return $ showPropDeBrStepsBase steps


instance ShowableSent PropDeBr where
    showSent :: Map PropDeBr [Int] -> PropDeBr -> Text
    showSent = showProp

instance ShowableTerm PropDeBr ObjDeBr where
    showTerm :: Map PropDeBr [Int] -> ObjDeBr -> Text
    showTerm = showObj

instance Show PropDeBr where
    show :: PropDeBr -> String
    show p = unpack (showProp mempty p)

instance Show ObjDeBr where
    show :: ObjDeBr -> String
    show o = unpack (showObj mempty o)

deriving instance Show DeBrSe