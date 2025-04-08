{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Data.Monoid ( Last(..) )
import Control.Monad ( foldM, unless )
import Control.Monad.RWS
    ( MonadTrans(..),
      MonadReader(ask, local),
      MonadState(put, get),
      MonadWriter(tell),
      RWST(..) )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
import Data.Maybe ( isNothing )
import Control.Applicative ( Alternative((<|>)) )
import Control.Arrow ( ArrowChoice(left) )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadCatch(..), MonadThrow(..), Exception )
import GHC.Stack.Types ( HasCallStack )
import Data.Data (Typeable)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import StdPattern
import RuleSets.BaseLogic hiding
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..))
import qualified RuleSets.BaseLogic as BASE
import RuleSets.PropLogic hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..))
import qualified RuleSets.PropLogic as PL
import RuleSets.PredLogic hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..))
import qualified RuleSets.PredLogic as PRED
import Langs.BasicUntyped

testTheoremMSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => TheoremSchemaMT () [PredRuleDeBr] PropDeBr Text m ()
testTheoremMSchema = TheoremSchemaMT  [("N",())] [z1,z2] theoremProg 
  where
    z1 = aX 99 ((X 99 `In` Constant "N") :&&: (X 99 :>=: Integ 10) :->: (X 99 :>=: Integ 0))
    z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 0) :->: (X 0 :==: Integ 0))


testEqualityRules :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testEqualityRules = do
    remarkM "--- Testing Equality Rules ---"

    -- Test eqReflM
    remarkM "Testing eqReflM (0 == 0):"
    let term0 = Integ 0
    (reflSent, reflIdx) <- eqReflM term0
    reflShow <- showPropM reflSent
    remarkM $ "Proved: " <> reflShow <> " at index " <> pack (show reflIdx)

    -- Test eqSymM
    remarkM "Testing eqSymM (given fake 1 == 2):"
    let term1 = Integ 1
    let term2 = Integ 2
    let eq12 = term1 :==: term2
    (eq12Sent, eq12Idx) <- fakePropM eq12 -- Assume 1==2 is proven for the test
    eq12Show <- showPropM eq12Sent
    remarkM $ "Assuming: " <> eq12Show <> " at index " <> pack (show eq12Idx)
    (symSent, symIdx) <- eqSymM eq12Sent
    symShow <- showPropM symSent
    remarkM $ "Proved: " <> symShow <> " at index " <> pack (show symIdx)

    -- Test eqTransM
    remarkM "Testing eqTransM (given fake 1 == 2 and 2 == 3):"
    let term3 = Integ 3
    let eq23 = term2 :==: term3
    (eq23Sent, eq23Idx) <- fakePropM eq23 -- Assume 2==3 is proven
    eq23Show <- showPropM eq23Sent
    remarkM $ "Assuming: " <> eq23Show <> " at index " <> pack (show eq23Idx)
    (transSent, transIdx) <- eqTransM eq12Sent eq23Sent -- Use eq12Sent from previous step
    transShow <- showPropM transSent
    remarkM $ "Proved: " <> transShow <> " at index " <> pack (show transIdx)

    -- Test eqSubstM
    remarkM "Testing eqSubstM (template X0 == X0, given fake 5 == 6):"
    let template = X 0 :==: X 0
    let term5 = Integ 5
    let term6 = Integ 6
    let eq56 = term5 :==: term6
    -- Prove the source sentence P(a), which is 5 == 5
    (sourceSent, sourceIdx) <- eqReflM term5 -- Use eqReflM to prove 5==5
    sourceShow <- showPropM sourceSent
    remarkM $ "Proved source: " <> sourceShow <> " at index " <> pack (show sourceIdx)
    -- Assume the equality a == b, which is 5 == 6
    (eqSent, eqIdx) <- fakePropM eq56
    eqShow <- showPropM eqSent
    remarkM $ "Assuming equality: " <> eqShow <> " at index " <> pack (show eqIdx)
    -- Perform substitution
    (substSent, substIdx) <- eqSubstM template eqSent -- Use the template, not the source sentence here
    substShow <- showPropM substSent
    remarkM $ "Proved subst: " <> substShow <> " at index " <> pack (show substIdx)

    remarkM "--- Equality Rule Tests Complete ---"
    return ()

testNormalization :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testNormalization = do
    remarkM "--- Testing Normalization ---"
    let term2 = Integ 1
    let s1 = aX 1 (eXBang 0 (X 1 :==: X 0))


    fakeConstM "N" ()
    fakePropM s1
    s1Show <- showPropM s1
    remarkM $ "Proved: " <> s1Show   
    return ()
 
testMoreComplexNesting :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testMoreComplexNesting = do
    remarkM "--- Testing More Complex Nesting (A > E > E!) ---"
    
    -- Represents ∀𝑥₂ ( ∃𝑥₁ ( ∃!𝑥₀ ( (𝑥₂ = 𝑥₁) ∧ (𝑥₁ = 𝑥₀) ) ) )
    let s3 = aX 2 ( eX 1 ( eXBang 0 ( (X 2 :==: X 1) :&&: (X 1 :==: X 0) ) ) )

    -- Add as fake prop and print
    fakePropM s3
    s3Show <- showPropM s3
    remarkM $ "Input: aX 2 ( eX 1 ( eXBang 0 ( (X 2 :==: X 1) :&&: (X 1 :==: X 0) ) ) )"
    remarkM $ "Printed: " <> s3Show   
    
    remarkM "--- More Complex Nesting Test Complete ---"
    return ()

testNonSequentialIndices :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testNonSequentialIndices = do
    remarkM "--- Testing Non-Sequential Indices (A5 > E!2 > A7) ---"

    -- Represents ∀𝑥₅ ( ∃!𝑥₂ ( ∀𝑥₇ ( (𝑥₅ = 𝑥₂) ∨ (𝑥₂ = 𝑥₇) ) ) )
    let s4 = aX 5 ( eXBang 2 ( aX 7 ( (X 5 :==: X 2) :||: (X 2 :==: X 7) ) ) )

    -- Add as fake prop and print
    fakePropM s4
    s4Show <- showPropM s4
    remarkM $ "Input: aX 5 ( eXBang 2 ( aX 7 ( (X 5 :==: X 2) :||: (X 2 :==: X 7) ) ) )"
    remarkM $ "Printed: " <> s4Show

    remarkM "--- Non-Sequential Indices Test Complete ---"
    return ()





testSetBuilder :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testSetBuilder = do
    remarkM "--- Testing Set Builder Notation ---"

    -- Define the source set N
    let setN = Constant "N"
    -- Define the property P(x) as x = x.
    let propertyP = (X 0 :==: X 0)

    -- Construct the term representing { x ∈ N | x = x }
    let setBuilt = builderX 0 setN propertyP

    -- Add N as a fake constant for context
    fakeConstM "N" ()
    -- Add the constructed set as a fake proposition/term to see it printed
    -- (We need a way to print ObjDeBr - using fakePropM on an equality
    -- with the set might work, or if you have a dedicated Obj print)
    -- Let's just create an equality for printing purposes:
    setBuiltShow <- showObjM setBuilt
    remarkM $ "Set Builder: " <> setBuiltShow
    remarkM "--- Set Builder Notation Test Complete ---"
    return ()

testComplexSetBuilder :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testComplexSetBuilder = do
    remarkM "--- Testing Complex Set Builder Notation ---"

    -- Define set names
    let setN = Constant "N"
    let setM = Constant "M"
    let setP = Constant "P"

    -- Define the property P(x), where x corresponds to X 1 (chosen index for builderX)
    -- The property is: ∀y (y ∈ M → ∃z (z ∈ P ∧ <x, y> = z))
    -- Let y be X 0 (bound by aX 0)
    -- Let z be X 2 (bound by eX 2)
    -- x is X 1 (the variable bound by builderX 1)
    let propertyP =
          aX 0 -- Binds y as X 0
             ( (X 0 `In` setM) -- y in M
               :->:            -- implies
               (eX 2          -- exists z as X 2
                  ( (X 2 `In` setP) -- z in P
                    :&&:            -- and
                    (Pair (X 1) (X 0) :==: X 2) -- <x, y> = z
                  )
               )
             )

    -- Construct the term representing the set using index 1 for 'x'
    let setBuiltComplex = builderX 1 setN propertyP

    -- Add constants for context
    fakeConstM "N" ()
    fakeConstM "M" ()
    fakeConstM "P" ()

    -- Print the constructed term (e.g., via an equality)
    (eqProp, _) <- fakePropM (setBuiltComplex :==: setBuiltComplex)
    setBuiltShow <- showObjM setBuiltComplex -- Use showObjM

    -- Use actual Unicode characters in the remark strings
    remarkM $ "Input Term (Conceptual): { x ∈ N | ∀y (y ∈ M → ∃z (z ∈ P ∧ <x, y> = z)) }"
    remarkM $ "Constructed Term (via builderX): " <> setBuiltShow
    remarkM $ "----> Expected future output: {𝑥₁ ∈ N | ∀𝑥₀((𝑥₀ ∈ M) → ∃𝑥₂( (𝑥₂ ∈ P) ∧ (<𝑥₁, 𝑥₀> = 𝑥₂)))}"
    remarkM "--- Complex Set Builder Test Complete ---"
    return ()

testComplexSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testComplexSubsetNotation = do
    remarkM "--- Testing More Complex Subset Notation (⊆) ---"

    -- 1. Define constants to represent sets
    let setN = Constant "N"
    let setA = Constant "A" -- Placeholder for Test 1 & 2
    let setB = Constant "B"
    let setC = Constant "C"

    -- 2. Add constants to the proof state
    fakeConstM "N" () -- Needed for Test 3
    fakeConstM "A" () -- Assume these are defined/exist for the test
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- 3. Test 1: Basic subset A B
    remarkM "Test 1: Basic subset A B"
    let subPropAB = subset setA setB
    (addedProp1, _) <- fakePropM subPropAB
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM $ "(Should be A ⊆ B)"

    -- 4. Test 2: Subset notation within a conjunction: (A ⊆ B) ∧ (B ⊆ C)
    remarkM "Test 2: Subset notation within conjunction (A ⊆ B) ∧ (B ⊆ C)"
    let subPropBC = subset setB setC
    -- Construct the conjunction using the PropDeBr operator :&&:
    let conjProp = subPropAB :&&: subPropBC
    (addedConjProp, _) <- fakePropM conjProp
    printedOutputConj <- showPropM addedConjProp
    remarkM $ "Actual printed output (Test 2): " <> printedOutputConj
    -- Note: Depending on operator precedence for ∧ and ⊆, parentheses might appear
    remarkM $ "(Should look like (A ⊆ B) ∧ (B ⊆ C) or similar)"

    -- 5. Test 3: Using a set builder expression {x ∈ N | x ≥ 5} ⊆ N
    remarkM "Test 3: Checking print for {x ∈ N | x ≥ 5} ⊆ N"
    -- Ensure N constant is added (done above)
    let five = Integ 5
    -- Define the property P(x) as x >= 5, using X 0 for the bound variable 'x'
    let propertyP = (X 0 :>=: five)
    -- Construct the set {x ∈ N | x ≥ 5} using builderX with index 0
    let setBuilderA = builderX 0 setN propertyP -- Defined in Langs/BasicUntyped.hs
    -- Create the subset proposition: {x ∈ N | x ≥ 5} ⊆ N
    let subPropBuilder = subset setBuilderA setN
    -- Add, print, and check the output
    (addedPropBuilder, _) <- fakePropM subPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 3): " <> printedOutputBuilder
    remarkM $ "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊆ N or similar)"

    remarkM "--- Complex Subset Notation Test Complete ---"
    return ()


testStrictSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testStrictSubsetNotation = do
    remarkM "--- Testing Strict Subset Notation (⊂) ---"

    -- Define set constants
    let setA = Constant "A"
    let setB = Constant "B"

    -- Add constants to proof state
    fakeConstM "A" ()
    fakeConstM "B" ()

    -- Test 1: Basic strict subset A ⊂ B (using the helper function)
    remarkM "Test 1: Basic strict subset A ⊂ B (using helper)"
    -- This helper creates: (subset setA setB) :&&: Neg (setA :==: setB)
    let strictSubProp1 = strictSubset setA setB

    (addedProp1, _) <- fakePropM strictSubProp1
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM $ "(Should be A ⊂ B)"

    -- Test 2: Test fallback for the Definition 2 pattern when precondition fails
    remarkM "Test 2: Testing fallback for Def 2 structure (should NOT use ⊂)"
    -- Create structure: (subset H H) ∧ (Exists y (y ∈ Bound 1 ∧ y ∉ H))
    -- where H = Hilbert (Bound 0 :==: C).
    -- This should fail the 'not (termB contains Bound 1)' check in 'andBuild'.
    fakeConstM "C" ()
    let setH = Hilbert (Bound 0 :==: Constant "C") -- max depth 1
    let termBound1 = Bound 1                     -- This IS Bound 1

    -- Manually construct subset H H: Forall (Bound 1 In H :->: Bound 1 In H)
    let idx_sub = max (boundDepthObjDeBr setH) (boundDepthObjDeBr setH) -- = 1
    let subPropHH = Forall ( (Bound idx_sub `In` setH) :->: (Bound idx_sub `In` setH) )

    -- Manually construct Exists part: Exists (Bound 1 In termBound1 && not (Bound 1 In setH))
    let idx_ex = max (boundDepthObjDeBr termBound1) (boundDepthObjDeBr setH) -- = 1
    let exists_inner = (Bound idx_ex `In` termBound1) :&&: Neg (Bound idx_ex `In` setH)
    let exists_part = Exists exists_inner -- Exists ( (Bound 1 In Bound 1) && Neg (Bound 1 In setH) )

    -- Combine them
    let complexConj = subPropHH :&&: exists_part

    remarkM $ "Constructed PropDeBr (Test 2): " <> (pack $ show complexConj) -- Raw view

    -- Check conditions manually via remarks for clarity
    remarkM $ "Manual check of 'andBuild' conditions for Def 2 pattern:"
    remarkM $ "  idx1=1, a1=setH, idx2=1, a2=setH"
    remarkM $ "  idx3=1, a3=termBound1, idx4=1, a4=setH"
    remarkM $ "  Checks:"
    remarkM $ "    idx1==max(d H,d H)? -> 1==1 PASS"
    remarkM $ "    idx2==idx1? -> 1==1 PASS"
    remarkM $ "    idx1==idx3? -> 1==1 PASS"
    remarkM $ "    idx1==idx4? -> 1==1 PASS"
    remarkM $ "    a2==a3? -> setH == termBound1? -> FAIL" -- Corrected term check fails here anyway
    remarkM $ "    a1==a4? -> setH == setH? -> PASS"
    remarkM $ "    not(a1 contains idx1)? -> not(setH contains 1)? -> PASS"
    remarkM $ "    not(a2 contains idx1)? -> not(setH contains 1)? -> PASS"
    remarkM $ "  (Note: Even if term checks were a2==a3 and a1==a4, the precondition check on a3=termBound1 would fail as 'termBound1 contains 1')"


    -- Add the proposition and get the printed output
    (addedProp2, _) <- fakePropM complexConj
    printedOutput2 <- showPropM addedProp2
    remarkM $ "Actual printed output (Test 2): " <> printedOutput2
    remarkM $ "(Should use default ∀, ∧, ∃ notations, NOT ⊂)"

    remarkM "--- Strict Subset Notation Test Complete ---"
    return ()

main :: IO ()
main = do
    print "TEST SET BUILDER BEGIN-------------------------------------"
    (aSB, bSB, cSB, dSB) <- runProofGeneratorT testSetBuilder
    (putStrLn . unpack . showPropDeBrStepsBase) cSB
    let y0 = (Integ 0 :==: Integ 0) :->: (Integ 99 :==: Integ 99)
    let y1 = Integ 0 :==: Integ 0
    let y2 = (Integ 99 :==: Integ 99) :->: (Integ 1001 :==: Integ 1001)
    let x0 = eX 0 (aX 0 ((Integ 0 :==: V 102) :&&: (X 0 `In` X 1)) :&&: (X 1 `In` X 1))
    let x1 = aX 3 (aX 2 (aX 1 ((X 3 :==: X 2) :&&: aX 0 (X 0 :==: X 1))))
    (print . show) (checkSanity [] [(),()] mempty x0)
    print "X1" 

    (putStrLn . show) x1
    let xv = aX 10 (aX 21 (aX 1 (X 10 :==: X 21 :&&: aX 0 (X 0 :==: X 1))))
    -- ∀𝑥₃(∀𝑥₂(∀𝑥₁(𝑥₃ = 𝑥₂ ∨ ∀𝑥₀(𝑥₀ = 𝑥₁))))
    let cxv = xv
    (putStrLn . show) cxv
    let f = parseForall x1
    case f of
        Just (f,()) -> do
            let term1 = Hilbert (Integ 0 `In` Integ 0)
            let fNew = f term1
            (print.show) fNew
        Nothing -> print "parse failed!"
       --let z = applyUG xn () 102
--    -- (print . show) z
    let proof = (   fakeProp y0
                <> fakeProp y1 
                <> fakeProp y2
                <> mp y0
                <> mp y2
                <> proofByAsm y1 (Integ 99 :==: Integ 99) (mp $ y1 .->. (Integ 99 :==: Integ 99))
                )
                  ::[PropRuleDeBr]
    let zb = runProof proof

    -- either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb
    print "OI leave me alone"
    let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 10) :->: (X 0 :>=: Integ 0))
    let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 0) :->: (X 0 :==: Integ 0))
    let generalized = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 10) :->: (X 0 :==: Integ 0))
    let asm = (V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 10)
    let mid = (V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 0)

    let proof2 =    fakeConst "N" ()
                 <> fakeProp z1
                 <> fakeProp z2
                 <> proofByUG generalized
                                        (
                                            proofByAsm asm z1 (
                                                    ui (V 0) z1
                                                <> mp ( asm .->. (V 0 :>=: Integ 0))
                                                <> simpL ((V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 10))
                                                <> adj (V 0 `In` Constant "N") (V 0 :>=: Integ 0)
                                                <> ui (V 0) z2
                                                <> mp ( mid .->. (V 0 :==: Integ 0)  )
                                            )  
                                        )
                                    ::[PredRuleDeBr]

    let proof3 = proofByUG generalized
                                     (
                                        proofByAsm asm z1 (
                                                ui (V 0) z1
                                             <> mp ( asm .->. (V 0 :>=: Integ 0))
                                      
                                            )
                                     )
                                  ::[PredRuleDeBr]
                 
    let zb2 = runProof proof2 

    let zb3 = runProof ((fakeConst "N" () <> fakeProp z1 <> fakeProp z2 <> ui (V 0) z1)::[PredRuleDeBr])
    --either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd)  zb2
    --either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb3
    (a,b,c,d) <- runProofGeneratorT testprog
    print "hi wattup 2"
    let stepTxt= showPropDeBrStepsBase c
    (putStrLn . unpack) stepTxt
    print "YOYOYOYOYOYOYOYOYOYO CHECK THEOREM"
    print "YOYOYOYOYOYOYOYOYOYO CHECK THEOREM"
    print "YOYOYOYOYOYOYOYOYOYO CHECK THEOREM3"
    (a,b,c,d) <- checkTheoremM testTheoremMSchema
--   print "yo"
    let stepTxt= showPropDeBrStepsBase d
    (putStrLn . unpack) stepTxt

    print "TEST PROG 2 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog2
    (putStrLn . unpack . showPropDeBrStepsBase) c

    return ()

    print "TEST PROG 3 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog3
    (putStrLn . unpack . showPropDeBrStepsBase) c

    print "TEST PROG 4 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog4
    (putStrLn . unpack . showPropDeBrStepsBase) c
    (putStrLn . show) b

    (putStrLn . show) c


    print "TEST PROG 5 BEGIN-------------------------------------"
    (a,b,c,d) <- runProofGeneratorT testprog5
    (putStrLn . unpack . showPropDeBrStepsBase) c
    (putStrLn . show) b

    print "TEST EQUALITY RULES BEGIN-------------------------------------"
    (aEq, bEq, cEq, dEq) <- runProofGeneratorT testEqualityRules
    (putStrLn . unpack . showPropDeBrStepsBase) cEq
    return ()

    print "TEST NORMALIZATION-------------------------------------"
    (aEq, bEq, cEq, dEq) <- runProofGeneratorT testNormalization
    (putStrLn . unpack . showPropDeBrStepsBase) cEq
    return ()

    print "TEST MORE COMPLEX NESTING BEGIN-------------------------------------"
    (aMC, bMC, cMC, dMC) <- runProofGeneratorT testMoreComplexNesting
    (putStrLn . unpack . showPropDeBrStepsBase) cMC

    print "TEST NON-SEQUENTIAL INDICES BEGIN-------------------------------------"
    (aNS, bNS, cNS, dNS) <- runProofGeneratorT testNonSequentialIndices
    (putStrLn . unpack . showPropDeBrStepsBase) cNS

    print "TEST COMPLEX SET BUILDER BEGIN-------------------------------------"
    (aCSB, bCSB, cCSB, dCSB) <- runProofGeneratorT testComplexSetBuilder
    (putStrLn . unpack . showPropDeBrStepsBase) cCSB


    print "TEST COMPLEX SUBSET NOTATION BEGIN-------------------------------------"
    (aCSub, bCSub, cCSub, dCSub) <- runProofGeneratorT testComplexSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cCSub -- Print results

    print "TEST SUBSET INTERNAL BINDING BEGIN-------------------------------------"
    (aIB, bIB, cIB, dIB) <- runProofGeneratorT testSubsetInternalBinding
    (putStrLn . unpack . showPropDeBrStepsBase) cIB -- Print results

    print "TEST STRICT SUBSET NOTATION BEGIN-------------------------------------"
    (aStrict, bStrict, cStrict, dStrict) <- runProofGeneratorT testStrictSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cStrict -- Print results

    -- ... (rest of main) ...
    return ()

    -- ... (rest of main) ...
    return ()

testSubsetInternalBinding :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testSubsetInternalBinding = do
    remarkM "--- Testing Subset Notation with Internal Binding ---"

    -- 1. Define a constant C and the term A = {y | exists x (y = C)}
    --    (Represented by Hilbert (Bound 0 :==: Constant "C"))
    fakeConstM "C" ()
    let setA = Hilbert (Bound 0 :==: Constant "C")

    -- 2. Construct the subset proposition: subset setA setA
    --    Based on your 'subset' function, this creates:
    --    Forall ( (Bound 1 `In` setA) :->: (Bound 1 `In` setA) )
    --    because max depth of setA is 1.
    let subProp = subset setA setA

    remarkM $ "Constructed PropDeBr: Forall ((Bound 1 `In` Hilbert (Bound 0 :==: Constant \"C\")) :->: (Bound 1 `In` Hilbert (Bound 0 :==: Constant \"C\")))"

    -- 3. Manually trace the conditions from your 'toSubexpParseTree'/'abuild' logic:
    remarkM $ "Checking conditions for '⊆' shorthand manually:"
    remarkM $ "  Pattern: Forall (Bound idx1 `In` a1 :->: Bound idx2 `In` a2)"
    remarkM $ "  Here: idx1=1, a1=setA, idx2=1, a2=setA."
    remarkM $ "  Condition 1: idx1 == max(depth a1, depth a2)? -> 1 == max(1, 1)? -> PASS"
    remarkM $ "  Condition 2: idx2 == idx1? -> 1 == 1? -> PASS"
    remarkM $ "  Condition 3: not (a1 contains Bound idx1)? -> not (setA contains Bound 1)? -> not (False)? -> PASS"
    remarkM $ "  Condition 4: not (a2 contains Bound idx1)? -> not (setA contains Bound 1)? -> not (False)? -> PASS"
    remarkM $ "Conclusion based on checks: All conditions PASS. Shorthand '⊆' should apply."

    -- 4. Add the proposition to the proof state using fakePropM
    (addedProp, _) <- fakePropM subProp

    -- 5. Get the actual printed output using showPropM
    printedOutput <- showPropM addedProp

    -- 6. Display the expected vs. actual output
    --    We use showObjM to print setA cleanly in the expected output remark
    setAShow <- showObjM setA
    remarkM $ "Expected output based on implemented condition check: " <> setAShow <> " ⊆ " <> setAShow
    remarkM $ "Actual printed output: " <> printedOutput

    remarkM "--- Internal Binding Subset Test Complete ---"
    return ()

testprog::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog = do
      let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 10) :->: (X 0 :>=: Integ 0))
      showZ1 <- showPropM z1
      remarkM $ showZ1 <> " Z1Z1Z1Z1" 
      let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 0) :->: (X 0 :==: Integ 0))
      let asm = (V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 10)
      let asm2 = (V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 10)
      fakeConstM "N" ()
      fakePropM z1
      fakePropM z2
      
      fux<- runProofByUGM () do
          runProofByAsmM  asm2 do
              (s5,_)<- runProofBySubArgM  do
                 newFreeVar <- getTopFreeVar
                 (s1,_) <- uiM newFreeVar z1
                 (s2,idx) <- mpM s1
                 (natAsm,_) <- simpLM asm
                 (s3,_) <- adjM natAsm s2
                 (s4,_) <- uiM newFreeVar z2
                 mpM s4
              return ()
          return ()
      runTheoremM  testTheoremMSchema
      runTmSilentM  testTheoremMSchema
      (absurdImp,_) <- runProofByAsmM z2 do
        (notZ1,_) <- fakePropM (Neg z1)
        (falseness,_) <- contraFM z1 notZ1
        showF <- showPropM falseness
        remarkM $ showF <> " is the falseness"
      showAbsurdImp <- showPropM absurdImp
      remarkM $ showAbsurdImp <> " is the absurdity"
      absurdM absurdImp
      return ()

testprog2::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog2 = do
    let p = eX 0 (X 0 `In` Constant "N")
    let q = eX 0 (X 0 :>=: Integ 10)
    let pImpQ = p :->: q
    fakeConstM "N" ()
    fakePropM pImpQ
    fakePropM $ neg q
    (s,idx) <- modusTollensM pImpQ
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


testprog3::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog3 = do
    let a = eX 0 (X 0 `nIn` Constant "N")
    fakeConstM "N" ()
    fakePropM a
    (s,idx) <- reverseANegIntroM a
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()

testprog4::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog4 = do
    let a = aX 0 (X 0 `nIn` Constant "N")
    fakeConstM "N" ()
    fakePropM a
    (s,idx) <- reverseENegIntroM a
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


testprog5::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog5 = do
    let a = eXBang 99 (Neg (X 99 `In` Constant "N"))
    fakeConstM "N" ()
    (s,idx) <- fakePropM a


    showS <- showPropM a
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


theoremProg::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => ProofGenTStd () [PredRuleDeBr] PropDeBr Text m ()
theoremProg = do
    let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 10) :->: (X 0 :>=: Integ 0))
    let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :>=: Integ 0) :->: (X 0 :==: Integ  0))
    let asm = (V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 10)
    let asm2 = (V 0 `In` Constant "N") :&&: (V 0 :>=: Integ 10)
    (generalized, _) <- runProofByUGM () do
          runProofByAsmM asm2 do
              newFreeVar <- getTopFreeVar
              (s1,_) <- uiM newFreeVar z1
              (s2,_) <- mpM s1
              remarkIdx <- remarkM "Yeah baby"
              remarkIdx2<-remarkM "" --empty remark
              --(lift . print) "Coment1"
              --(lift . print . show) s1
              remarkM $ (pack . show) remarkIdx2 <> " was the index of the remark above/"
              (natAsm,_) <- simpLM asm
              --(lift . print) "COmment 2"
              (s3,_) <- adjM natAsm s2
              (s4,line_idx) <- uiM newFreeVar z2
              showS4 <- showPropM s4
              remarkM $ showS4 <> " is the sentence. It was proven in line " <> (pack . show) line_idx
                       <> "\nThis is the next line of this remark."
              -- (lift . print . show) line_idx
              (s5,_) <- mpM s4
              simpLM asm
    return ()
--              return (s5,())

