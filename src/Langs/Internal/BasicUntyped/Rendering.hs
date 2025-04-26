module Langs.Internal.BasicUntyped.Rendering (
    PrfStdStepPredDeBr,
    showPropDeBrStepsBase,
    showPropDeBrStepsBaseM,
    showProp,
    showObj,
    showPropM,
    showObjM,
) where

import Langs.Internal.BasicUntyped.Core
import Langs.Internal.BasicUntyped.Shorthands
import Control.Monad ( unless, guard,msum, zipWithM )
import Data.List (intersperse,findIndex, partition,sort,find)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
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

import Data.Text (Text, pack, unpack,concat, lines,intercalate)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )


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
     ("×",(NotAssociative,7)),
     ("∪",(NotAssociative,6)),("∩",(NotAssociative,7))
     ]


     --The Int is it's precedence number.
binaryOpData :: Map Text (Associativity, Int)
binaryOpData = Data.Map.fromList binaryOpInData


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
              <|> parseBinaryUnion'
              <|> parseIntersectionOp'
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
               return $ Tuple $ Prelude.map  (`toSubexpParseTree` dict) tuple
            parseComposition' = do
                (f,g) <- parseComposition obj
                return $ BinaryOp "∘" (toSubexpParseTree f dict) (toSubexpParseTree g dict)
            parseProject' = do
                (i, o) <- parseProjectHilbert obj
                let pTree = toSubexpParseTree o dict
                return $ TupleProject i pTree
            parseCrossProduct' = do
                (a,b) <- parseCrossProduct obj
                return $ BinaryOp "×" (toSubexpParseTree a dict) (toSubexpParseTree b dict)
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
          return ParseTreeF


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


showPropDeBrStepsBase :: [PrfStdStepPredDeBr] -> Text
showPropDeBrStepsBase = showPropDeBrSteps [] [] 0 True mempty


showPropDeBrStepsBaseM :: (Monad m, Monoid r, 
             Proof eL r (PrfStdState PropDeBr Text ()) (PrfStdContext ()) [PrfStdStep PropDeBr Text ()] PropDeBr) 
                     => [PrfStdStepPredDeBr] -> ProofGenTStd () r PropDeBr Text m Text
showPropDeBrStepsBaseM steps = do 
      state <- getProofState
      let dict = provenSents state
      return $ showPropDeBrStepsBase steps