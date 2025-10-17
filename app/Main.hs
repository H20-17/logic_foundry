{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE TupleSections #-}


module Main where

import Data.Monoid ( Last(..) )
import Control.Monad ( foldM, unless, forM, guard )
import Control.Monad.RWS
    ( MonadTrans(..),
      MonadReader(ask, local),
      MonadState(put, get),
      MonadWriter(tell),
      RWST(..) )
import Data.Set (Set, fromList,toList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map, toList )
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
import RuleSets.BaseLogic.Core hiding
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..))
import qualified RuleSets.BaseLogic.Core as BASE
import RuleSets.PropLogic.Core hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..))
import qualified RuleSets.PropLogic.Core as PL
import RuleSets.PredLogic.Core hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..),
   aX, eX, hX, eXBang, multiAx)
import qualified RuleSets.PredLogic.Core as PRED

import qualified RuleSets.PredLogic.Helpers as PRED

import RuleSets.ZFC.Core hiding
    (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicError(..),
   LogicSent,
   SubproofMException(..))


import qualified RuleSets.ZFC.Core as ZFC
import RuleSets.ZFC.Helpers
import Langs.BasicUntyped
import Distribution.Compat.Lens (set)
import RuleSets.BaseLogic.Helpers
import RuleSets.PropLogic.Helpers
import RuleSets.PredLogic.Helpers hiding
   (runProofByUGM)
import RuleSets.ZFC.Theorems

testTheoremMSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => TheoremSchemaMT () [PredRuleDeBr] PropDeBr Text () m ()
testTheoremMSchema = TheoremSchemaMT  [("N",())] [z1,z2] theoremProg [] []
  where
    z1 = aX 99 ((X 99 `In` Constant "N") :&&: (X 99 :<=: Integ 10) :->: (X 99 :<=: Integ 0))
    z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ 0))






testEqualityRules :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
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
    (eq12Sent, eq12Idx) <- fakePropM [] eq12 -- Assume 1==2 is proven for the test
    eq12Show <- showPropM eq12Sent
    remarkM $ "Assuming: " <> eq12Show <> " at index " <> pack (show eq12Idx)
    (symSent, symIdx) <- eqSymM eq12Sent
    symShow <- showPropM symSent
    remarkM $ "Proved: " <> symShow <> " at index " <> pack (show symIdx)

    -- Test eqTransM
    remarkM "Testing eqTransM (given fake 1 == 2 and 2 == 3):"
    let term3 = Integ 3
    let eq23 = term2 :==: term3
    (eq23Sent, eq23Idx) <- fakePropM []eq23 -- Assume 2==3 is proven
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
    (eqSent, eqIdx) <- fakePropM [] eq56
    eqShow <- showPropM eqSent
    remarkM $ "Assuming equality: " <> eqShow <> " at index " <> pack (show eqIdx)
    -- Perform substitution
    (substSent, substIdx) <- eqSubstM 0 template eqSent -- Use the template, not the source sentence here
    substShow <- showPropM substSent
    remarkM $ "Proved subst: " <> substShow <> " at index " <> pack (show substIdx)

    remarkM "--- Equality Rule Tests Complete ---"
    return ()

testNormalization :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testNormalization = do
    remarkM "--- Testing Normalization ---"
    let term2 = Integ 1
    let s1 = aX 1 (eXBang 0 (X 1 :==: X 0))


    fakeConstM "N" ()
    fakePropM [] s1
    s1Show <- showPropM s1
    remarkM $ "Proved: " <> s1Show   
    return ()
 
testMoreComplexNesting :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testMoreComplexNesting = do
    remarkM "--- Testing More Complex Nesting (A > E > E!) ---"
    
    -- Represents ∀𝑥₂ ( ∃𝑥₁ ( ∃!𝑥₀ ( (𝑥₂ = 𝑥₁) ∧ (𝑥₁ = 𝑥₀) ) ) )
    let s3 = aX 2 ( eX 1 ( eXBang 0 ( (X 2 :==: X 1) :&&: (X 1 :==: X 0) ) ) )

    -- Add as fake prop and print
    fakePropM []s3
    s3Show <- showPropM s3
    remarkM "Input: aX 2 ( eX 1 ( eXBang 0 ( (X 2 :==: X 1) :&&: (X 1 :==: X 0) ) ) )"
    remarkM $ "Printed: " <> s3Show   
    
    remarkM "--- More Complex Nesting Test Complete ---"
    return ()

testNonSequentialIndices :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testNonSequentialIndices = do
    remarkM "--- Testing Non-Sequential Indices (A5 > E!2 > A7) ---"

    -- Represents ∀𝑥₅ ( ∃!𝑥₂ ( ∀𝑥₇ ( (𝑥₅ = 𝑥₂) ∨ (𝑥₂ = 𝑥₇) ) ) )
    let s4 = aX 5 ( eXBang 2 ( aX 7 ( (X 5 :==: X 2) :||: (X 2 :==: X 7) ) ) )

    -- Add as fake prop and print
    fakePropM [] s4
    s4Show <- showPropM s4
    remarkM "Input: aX 5 ( eXBang 2 ( aX 7 ( (X 5 :==: X 2) :||: (X 2 :==: X 7) ) ) )"
    remarkM $ "Printed: " <> s4Show

    remarkM "--- Non-Sequential Indices Test Complete ---"
    return ()






testComplexSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
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
    (addedProp1, _) <- fakePropM [] subPropAB
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM "(Should be A ⊆ B)"

    -- 4. Test 2: Subset notation within a conjunction: (A ⊆ B) ∧ (B ⊆ C)
    remarkM "Test 2: Subset notation within conjunction (A ⊆ B) ∧ (B ⊆ C)"
    let subPropBC = subset setB setC
    -- Construct the conjunction using the PropDeBr operator :&&:
    let conjProp = subPropAB :&&: subPropBC
    (addedConjProp, _) <- fakePropM [] conjProp
    printedOutputConj <- showPropM addedConjProp
    remarkM $ "Actual printed output (Test 2): " <> printedOutputConj
    -- Note: Depending on operator precedence for ∧ and ⊆, parentheses might appear
    remarkM "(Should look like (A ⊆ B) ∧ (B ⊆ C) or similar)"

    -- 5. Test 3: Using a set builder expression {x ∈ N | x ≥ 5} ⊆ N
    remarkM "Test 3: Checking print for {x ∈ N | x ≥ 5} ⊆ N"
    -- Ensure N constant is added (done above)
    let five = Integ 5
    -- Define the property P(x) as x <= 5, using X 0 for the bound variable 'x'
    let propertyP = X 0 :<=: five
    -- Construct the set {x ∈ N | x ≥ 5} using builderX with index 0
    let setBuilderA = builderX 0 setN propertyP -- Defined in Langs/BasicUntyped.hs
    -- Create the subset proposition: {x ∈ N | x ≥ 5} ⊆ N
    let subPropBuilder = subset setBuilderA setN
    -- Add, print, and check the output
    (addedPropBuilder, _) <- fakePropM []subPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 3): " <> printedOutputBuilder
    remarkM "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊆ N or similar)"

    remarkM "--- Complex Subset Notation Test Complete ---"
    return ()

testStrictSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testStrictSubsetNotation = do
    remarkM "--- Testing Strict Subset Notation (⊂) ---"

    -- 1. Define constants
    let setA = Constant "A"
    let setB = Constant "B"
    let setN = Constant "N"

    -- 2. Add constants to proof state
    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "N" ()

    -- 3. Test 1: Basic strict subset A ⊂ B
    remarkM "Test 1: Basic strict subset A ⊂ B"
    -- This assumes strictSubset a b = subset a b :&&: Neg (a :==: b)
    let strictSubProp1 = strictSubset setA setB
    (addedProp1, _) <- fakePropM [] strictSubProp1
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM "(Should be A ⊂ B)"

    -- 4. Test 2: Strict subset with set builder {x ∈ N | x ≥ 5} ⊂ N
    remarkM "Test 2: Strict subset involving a Set Builder expression"
    let five = Integ 5
    let propertyP = X 0 :<=: five
    let setBuilderA = builderX 0 setN propertyP -- {x ∈ N | x ≥ 5}
    -- Create the strict subset proposition: {x ∈ N | x ≥ 5} ⊂ N
    let strictSubPropBuilder = strictSubset setBuilderA setN
    (addedPropBuilder, _) <- fakePropM [] strictSubPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 2): " <> printedOutputBuilder
    remarkM "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊂ N or similar)"

    -- 5. Test 3: A structure that should NOT use the ⊂ notation
    remarkM "Test 3: Structure that should NOT print as ⊂ (using A=A instead of Not(A=B))"
    -- Example: (A ⊆ B) ∧ (A = A) -- Does not match Neg(A==B)
    (eqAA, _) <- eqReflM setA -- Prove A = A using EqRefl rule
    let subPropAB = subset setA setB -- A ⊆ B part
    let nonStrictSubProp = subPropAB :&&: eqAA -- Combine with A=A
    (addedProp3, _) <- fakePropM [] nonStrictSubProp
    printedOutput3 <- showPropM addedProp3
    remarkM $ "Actual printed output (Test 3): " <> printedOutput3
    remarkM "(Should be (A ⊆ B) ∧ (A = A) or similar, *NOT* A ⊂ B)"

    remarkM "--- Strict Subset Notation Test Complete ---"
    return ()


testNotSubsetNotation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testNotSubsetNotation = do
    remarkM "--- Testing Not Subset Notation (⊈) ---"

    -- 1. Define constants
    let setA = Constant "A"
    let setB = Constant "B"
    let setN = Constant "N"

    -- 2. Add constants to proof state
    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "N" ()

    -- 3. Test 1: Basic not subset A ⊈ B
    remarkM "Test 1: Basic not subset A ⊈ B"
    -- Assumes notSubset a b = Neg (subset a b)
    let notSubProp1 = notSubset setA setB
    (addedProp1, _) <- fakePropM [] notSubProp1
    printedOutput1 <- showPropM addedProp1
    remarkM $ "Actual printed output (Test 1): " <> printedOutput1
    remarkM "(Should be A ⊈ B)"

    -- 4. Test 2: Not subset with set builder {x ∈ N | x ≥ 5} ⊈ N
    remarkM "Test 2: Not subset involving a Set Builder expression"
    let five = Integ 5
    let propertyP = X 0 :<=: five
    let setBuilderA = builderX 0 setN propertyP -- {x ∈ N | x ≥ 5}
    -- Create the not subset proposition: {x ∈ N | x ≥ 5} ⊈ N
    let notSubPropBuilder = notSubset setBuilderA setN
    (addedPropBuilder, _) <- fakePropM [] notSubPropBuilder
    printedOutputBuilder <- showPropM addedPropBuilder
    remarkM $ "Actual printed output (Test 2): " <> printedOutputBuilder
    remarkM "(Should look like {𝑥₀ ∈ N | 𝑥₀ ≥ 5} ⊈ N or similar)"

    -- 5. Test 3: A structure that should NOT use the ⊈ notation
    remarkM "Test 3: Structure that should NOT print as ⊈"
    -- Example: Neg (A ⊂ B) -- Should print as ¬(A ⊂ B), not A ⊈ B
    let strictSubProp = strictSubset setA setB -- Assuming this helper exists and works
    let negStrictSubProp = Neg strictSubProp
    (addedProp3, _) <- fakePropM []negStrictSubProp
    printedOutput3 <- showPropM addedProp3
    remarkM $ "Actual printed output (Test 3): " <> printedOutput3
    remarkM "(Should be ¬(A ⊂ B) or similar, *NOT* related to ⊈)"

    remarkM "--- Not Subset Notation Test Complete ---"
    return ()



testHelperPreconditionViolation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testHelperPreconditionViolation = do
    remarkM "--- Testing Helper Precondition Violation ---"
    let setN = Constant "N"
    let constC = Constant "C"
    let setB = Constant "B"

    fakeConstM "N" ()
    fakeConstM "C" ()
    fakeConstM "B" ()

    -- Construct A = {x ∈ N | x = C} using builderX
    -- This term 'setA' contains Bound 1 internally. Its depth is 1.
    let setA = builderX 0 setN (X 0 :==: constC)
    setAShow <- showObjM setA -- See the structure (likely involves Bound 1)
    remarkM $ "Constructed setA = " <> setAShow

    -- Construct subset A B
    -- This calculates idx = max(depth A, depth B) = max(1, 0) = 1.
    -- Precondition requires A not contain Bound 1, but it does.
    let violatingSubsetProp = subset setA setB
    remarkM "Constructed 'subset setA setB'. Precondition (A must not contain Bound 1) is VIOLATED."

    -- Add it to the proof state. It might pass checkSanity if the check isn't perfect,
    -- but it represents a violation of the helper's intended use conditions.
    (addedProp, _) <- fakePropM [] violatingSubsetProp
    printedProp <- showPropM addedProp
    remarkM $ "Resulting PropDeBr structure (printed form): " <> printedProp
    remarkM "(Check if it printed using ⊆ or fallback ∀ notation)"
    remarkM "--- Precondition Violation Test Complete ---"
    return ()


testBuilderXSuite :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testBuilderXSuite = do
    remarkM "--- Starting New builderX Test Suite ---"

    -- Prerequisite Constants
    fakeConstM "N" () -- Natural numbers (example source set)
    fakeConstM "M" () -- Another example set
    fakeConstM "C" () -- A specific constant element
    let setN = Constant "N"
    let setM = Constant "M"
    let constC = Constant "C"
    let int5 = Integ 5

    -- Test 1: Simple Predicate (x <= 5)
    remarkM "Test 1: Simple Predicate { x ∈ N | x ≥ 5 }"
    let prop1 = X 0 :<=: int5
    let builtSet1 = builderX 0 setN prop1
    builtSet1Show <- showObjM builtSet1
    remarkM $ "Constructed (idx=0): " <> builtSet1Show
    remarkM "(Expected: {𝑥₀ ∈ N | 𝑥₀ ≥ 5})"

    -- Test 2: Predicate with Equality (x == C)
    remarkM "Test 2: Predicate with Equality { x ∈ N | x == C }"
    let prop2 = X 0 :==: constC
    let builtSet2 = builderX 0 setN prop2
    builtSet2Show <- showObjM builtSet2
    remarkM $ "Constructed (idx=0): " <> builtSet2Show
    remarkM "(Expected: {𝑥₀ ∈ N | 𝑥₀ = C})"

    -- Test 3: Using a different index (idx=1)
    remarkM "Test 3: Using Different Index { x ∈ N | x ≥ 5 }"
    let prop3 = X 1 :<=: int5 -- Using X 1 now
    let builtSet3 = builderX 1 setN prop3 -- Using index 1
    builtSet3Show <- showObjM builtSet3
    remarkM $ "Constructed (idx=1): " <> builtSet3Show
    remarkM "(Expected: {𝑥₁ ∈ N | 𝑥₁ ≥ 5})"

    -- Test 4: Predicate with nested quantifiers (∀y (y ∈ M -> x = y))
    remarkM "Test 4: Nested Quantifier in Predicate { x ∈ N | ∀y (y ∈ M → x = y) }"
    -- Predicate: aX 1 ( (X 1 `In` setM) :->: (X 0 :==: X 1) )
    -- Here, x is X 0 (bound by builderX), y is X 1 (bound by aX)
    let prop4 = aX 1 ( (X 1 `In` setM) :->: (X 0 :==: X 1) )
    let builtSet4 = builderX 0 setN prop4 -- Using index 0 for x
    builtSet4Show <- showObjM builtSet4
    remarkM $ "Constructed (idx=0): " <> builtSet4Show
    remarkM "(Expected: {𝑥₀ ∈ N | ∀𝑥₁((𝑥₁ ∈ M) → (𝑥₀ = 𝑥₁))})"

    -- Test 5: Complex Predicate with Existential Quantifier
    remarkM "Test 5: Complex Predicate { x ∈ N | ∃y (y ∈ M ∧ x = <y, C>) }"
    -- Predicate: eX 1 ( (X 1 `In` setM) :&&: (X 0 :==: Pair (X 1) constC) )
    -- Here, x is X 0 (bound by builderX), y is X 1 (bound by eX)
    let prop5 = eX 1 ( (X 1 `In` setM) :&&: (X 0 :==: pair (X 1) constC) )
    let builtSet5 = builderX 0 setN prop5 -- Using index 0 for x
    builtSet5Show <- showObjM builtSet5
    remarkM $ "Constructed (idx=0): " <> builtSet5Show
    remarkM "(Expected: {𝑥₀ ∈ N | ∃𝑥₁((𝑥₁ ∈ M) ∧ (𝑥₀ = <𝑥₁, C>))})"

    -- Test 6: Using a different source set M
    remarkM "Test 6: Different Source Set { x ∈ M | x == C }"
    let prop6 = X 0 :==: constC
    let builtSet6 = builderX 0 setM prop6 -- Source set is M
    builtSet6Show <- showObjM builtSet6
    remarkM $ "Constructed (idx=0): " <> builtSet6Show
    remarkM "(Expected: {𝑥₀ ∈ M | 𝑥₀ = C})"

    -- Test 7: Predicate always true (using x == x)
    remarkM "Test 7: Predicate Always True { x ∈ N | x == x }"
    let prop7 = X 0 :==: X 0
    let builtSet7 = builderX 0 setN prop7
    builtSet7Show <- showObjM builtSet7
    remarkM $ "Constructed (idx=0): " <> builtSet7Show
    remarkM "(Expected: {𝑥₀ ∈ N | 𝑥₀ = 𝑥₀})"

    -- Test 8: Predicate involving other template variables (if needed later)
    -- remarkM "Test 8: Predicate with other X vars - Placeholder"
    -- let prop8 = (X 0 :==: X 99) -- Example, assuming X 99 is defined elsewhere
    -- let builtSet8 = builderX 0 setN prop8
    -- builtSet8Show <- showObjM builtSet8
    -- remarkM $ "Constructed (idx=0): " <> builtSet8Show
    -- remarkM "(Shows interaction with other template vars if applicable)"

    remarkM "--- builderX Test Suite Complete ---"
    return ()


testCompositionImplementation :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testCompositionImplementation = do
    remarkM "--- Testing Composition Implementation (with Tupl [dom, cod, graph] assumption) ---"

    -- Define simple functions and argument
    -- NOTE: We assume f and g are now represented as triples Tupl[dom,cod,graph]
    -- For this test, we still use Constants, assuming they represent such triples.
    let f = Constant "F"
    let g = Constant "G"
    let x = Constant "A"
    fakeConstM "F" () -- Represents function F as Tupl[DomF, CodF, GraphF]
    fakeConstM "G" () -- Represents function G as Tupl[DomG, CodG, GraphG]
    fakeConstM "A" () -- Represents argument A
    remarkM "Using f = F, g = G, x = A"

    -- 1. Calculate h = f .:. g using the definition based on compositionTemplate
    remarkM "Calculating h = f .:. g"
    let h = f .:. g -- Assumes .:. uses compositionTemplate which uses the new .@.
    hShow <- showObjM h
    remarkM $ "Constructed h: " <> hShow
    remarkM "(Note: This will be a complex Hilbert term based on compositionTemplate and the new .@.)"

    -- 2. Calculate h .@. x using the new .@. definition
    remarkM "Calculating h .@. x"
    -- This now uses: objDeBrSubXs [(0,h),(1,x)] (hX 2 ( Tupl [X 1, X 2] `In` tripletLast (X 0) ))
    let applied_h = h .@. x
    applied_h_Show <- showObjM applied_h
    remarkM $ "Result (h .@. x): " <> applied_h_Show
    remarkM "(Note: This involves substituting h and x into the .@. template containing tripletLast)"

    -- 3. Calculate f .@. (g .@. x) separately using the new .@.
    remarkM "Calculating f .@. (g .@. x) separately"
    -- Inner application: g .@. x
    let applied_g = g .@. x
    applied_g_Show <- showObjM applied_g
    remarkM $ "  Inner (g .@. x): " <> applied_g_Show
    -- Outer application: f .@. applied_g
    let expected_result = f .@. applied_g
    expected_result_Show <- showObjM expected_result
    remarkM $ "  Outer f .@. (g .@. x): " <> expected_result_Show

    -- 4. Compare (visually via remarks)
    remarkM "--- Comparison ---"
    remarkM $ "h .@. x             => " <> applied_h_Show
    remarkM $ "f .@. (g .@. x)     => " <> expected_result_Show
    remarkM "Check if the final term structures match visually."
    remarkM "WARNING: Visual comparison of these complex Hilbert terms might be difficult."
    remarkM "Consider adding a formal proof step to check equality if possible."
    remarkM "If they differ structurally, there might be an issue in how .:. or .@. interacts with the substitutions."

    remarkM "--- Composition Implementation Test Complete ---"
    return ()

testShorthandRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testShorthandRendering = do
    remarkM "--- Testing Shorthand Rendering (Post Function Triple Change) ---"

    -- Setup Constants
    let a = Constant "A"
    let b = Constant "B"
    let n = Constant "N"
    -- Assume f, g represent function triples Tupl[_, _, _]
    let f = Constant "f"
    let g = Constant "g"
    let x_arg = Constant "x_arg" -- Argument for functions

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "N" ()
    fakeConstM "f" () -- Represents function f
    fakeConstM "g" () -- Represents function g
    fakeConstM "x_arg" () -- Represents an argument

    let five = Integ 5
    let zero = Integ 0

    -- Test 1: Function Application (.@.) -> f(x_arg)
    remarkM "Test 1: f .@. x_arg"
    -- Uses the new .@. definition internally
    let app_f_x = f .@. x_arg
    app_f_x_show <- showObjM app_f_x
    remarkM "  Input Term (structure depends on new .@.): f .@. x_arg"
    remarkM $ "  Actual Rendered:   " <> app_f_x_show
    remarkM "  Expected Rendered: f(x_arg)"
    remarkM "  (Success depends on parseFuncApplication recognizing the new structure)"

    -- Test 2: Nested Function Application -> f(g(x_arg))
    remarkM "Test 2: f .@. (g .@. x_arg)"
    let app_g_x = g .@. x_arg
    let app_f_gx = f .@. app_g_x
    app_f_gx_show <- showObjM app_f_gx
    remarkM "  Input Term: f .@. (g .@. x_arg)"
    remarkM $ "  Actual Rendered:   " <> app_f_gx_show
    remarkM "  Expected Rendered: f(g(x_arg))"
    remarkM "  (Success depends on parseFuncApplication recognizing nested new structures)"

    -- Test 3: Function Composition (.:.) -> f ∘ g
    remarkM "Test 3: f .:. g"
    -- Assumes .:. uses compositionTemplate which uses the new .@.
    let comp_f_g = f .:. g
    comp_f_g_show <- showObjM comp_f_g
    remarkM "  Input Term (structure depends on new .@. via template): f .:. g"
    remarkM $ "  Actual Rendered:   " <> comp_f_g_show
    remarkM "  Expected Rendered: f ∘ g"
    remarkM "  (Success depends on parseComposition recognizing the template structure)"

    -- Test 3b: Apply composed function -> (f ∘ g)(x_arg)
    remarkM "Test 3b: (f .:. g) .@. x_arg"
    let app_comp_x = comp_f_g .@. x_arg
    app_comp_x_show <- showObjM app_comp_x
    remarkM "  Input Term: (f .:. g) .@. x_arg"
    remarkM $ "  Actual Rendered:   " <> app_comp_x_show
    remarkM "  Expected Rendered: (f ∘ g)(x_arg)"
    remarkM "  (Success depends on parseFuncApplication recognizing the composed structure)"

    -- == Other tests remain largely the same, as they don't depend on the function representation ==

    -- Test 4: Set Builder -> { x ∈ N | x ≥ 5 }
    remarkM "Test 4: builderX 0 N (X 0 :<=: 5)"
    let builder_n_ge_5 = builderX 0 n (X 0 :<=: five)
    builder_n_ge_5_show <- showObjM builder_n_ge_5
    remarkM "  Input: builderX 0 N (X 0 :<=: 5)"
    remarkM $ "  Actual:   " <> builder_n_ge_5_show
    remarkM "  Expected: {𝑥₀ ∈ N | 𝑥₀ ≥ 5}"

    -- Test 5: Hilbert Epsilon Shorthand -> ε[index]
    remarkM "Test 5: Hilbert ε shorthand (requires proven Exists)"
    let hilbert_prop = X 0 :==: a -- Example property P(x) = (x == A)
    let hilbert_term = hX 0 hilbert_prop -- εx.(x == A)
    let exists_prop = eX 0 hilbert_prop -- ∃x.(x == A)
    (fake_exists, fake_idx) <- fakePropM [] exists_prop
    exists_show <- showPropM fake_exists -- Show the prop being faked
    remarkM $ "  Faking proof of: " <> exists_show  <> " at index " <> pack (show fake_idx)
    hilbert_term_short_show <- showObjM hilbert_term
    remarkM "  Input: hX 0 (X 0 :==: A)  (after proving Exists)"
    remarkM $ "  Actual:   " <> hilbert_term_short_show
    remarkM $ "  Expected: ε" <> pack (show fake_idx) -- Adjust format if needed

    -- Test 6: Default Hilbert -> εx.(...)
    remarkM "Test 6: Default Hilbert ε binding"
    let hilbert_term_default = hX 1 (X 1 :<=: zero) -- εx.(x <= 0)
    hilbert_term_default_show <- showObjM hilbert_term_default
    remarkM "  Input: hX 1 (X 1 :<=: 0)"
    remarkM $ "  Actual:   " <> hilbert_term_default_show
    remarkM "  Expected: ε𝑥₁(𝑥₁ ≥ 0)"

    -- Test 7: Subset (⊆)
    remarkM "Test 7: subset A B"
    let subset_a_b = subset a b
    subset_a_b_show <- showPropM subset_a_b
    remarkM "  Input: subset A B"
    remarkM $ "  Actual:   " <> subset_a_b_show
    remarkM "  Expected: A ⊆ B"

    -- Test 8: Strict Subset (⊂)
    remarkM "Test 8: strictSubset A B"
    let strictsubset_a_b = strictSubset a b
    strictsubset_a_b_show <- showPropM strictsubset_a_b
    remarkM "  Input: strictSubset A B"
    remarkM $ "  Actual:   " <> strictsubset_a_b_show
    remarkM "  Expected: A ⊂ B"

    -- Test 9: Not Subset (⊈)
    remarkM "Test 9: notSubset A B"
    let notsubset_a_b = notSubset a b
    notsubset_a_b_show <- showPropM notsubset_a_b
    remarkM "  Input: notSubset A B"
    remarkM $ "  Actual:   " <> notsubset_a_b_show
    remarkM "  Expected: A ⊈ B"

    -- Test 10: Exists Unique (∃!)
    remarkM "Test 10: eXBang 0 (X 0 :==: A)"
    let existsunique_a = eXBang 0 (X 0 :==: a)
    existsunique_a_show <- showPropM existsunique_a
    remarkM "  Input: eXBang 0 (X 0 :==: A)"
    remarkM $ "  Actual:   " <> existsunique_a_show
    remarkM "  Expected: ∃!𝑥₀(𝑥₀ = A)"

    -- Test 11: Not Equal (≠)
    remarkM "Test 11: A ./=. B"
    let notequal_a_b = a ./=. b -- Or Neg (a :==: b)
    notequal_a_b_show <- showPropM notequal_a_b
    remarkM "  Input: A ./=. B"
    remarkM $ "  Actual:   " <> notequal_a_b_show
    remarkM "  Expected: A ≠ B"

    -- Test 12: Not In (∉)
    remarkM "Test 12: A `nIn` B"
    let notin_a_b = a `nIn` b -- Or Neg (a `In` b)
    notin_a_b_show <- showPropM notin_a_b
    remarkM "  Input: A `nIn` B"
    remarkM $ "  Actual:   " <> notin_a_b_show
    remarkM "  Expected: A ∉ B"

    remarkM "--- Shorthand Rendering Tests Complete ---"
    return ()





testProjectShorthandParsing :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testProjectShorthandParsing = do
    remarkM "--- Testing Project Shorthand Parsing (via Rendering) ---"

    -- Setup Constants and Variables
    let tupleA = Constant "MyTupleA"
    let tupleB = Constant "MyTupleB"
    let constA = Constant "A"
    let constB = Constant "B"
    let constC = Constant "C"

    fakeConstM "MyTupleA" ()
    fakeConstM "MyTupleB" ()
    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- == Positive Cases ==

    -- Test 1: Simple 2-tuple, project index 0
    remarkM "Test 1: Project 2 0 MyTupleA"
    let proj_2_0_A = project 2 0 tupleA -- Generate term using helper
    proj_2_0_A_show <- showObjM proj_2_0_A
    remarkM "  Input:    project 2 0 MyTupleA"
    remarkM $ "  Actual:   " <> proj_2_0_A_show
    remarkM "  Expected: π₀(MyTupleA)"

    -- Test 2: Simple 2-tuple, project index 1
    remarkM "Test 2: Project 2 1 MyTupleA"
    let proj_2_1_A = project 2 1 tupleA
    proj_2_1_A_show <- showObjM proj_2_1_A
    remarkM "  Input:    project 2 1 MyTupleA"
    remarkM $ "  Actual:   " <> proj_2_1_A_show
    remarkM "  Expected: π₁(MyTupleA)"

    -- Test 3: 3-tuple, project index 1
    remarkM "Test 3: Project 3 1 MyTupleB"
    let proj_3_1_B = project 3 1 tupleB
    proj_3_1_B_show <- showObjM proj_3_1_B
    remarkM "  Input:    project 3 1 MyTupleB"
    remarkM $ "  Actual:   " <> proj_3_1_B_show
    remarkM "  Expected: π₁(MyTupleB)"

    -- Test 4: Nested projection (term `t` is itself a projection)
    remarkM "Test 4: Project 2 0 (project 2 1 MyTupleA)"
    let inner_proj = project 2 1 tupleA
    let outer_proj = project 2 0 inner_proj
    outer_proj_show <- showObjM outer_proj
    remarkM "  Input:    project 2 0 (project 2 1 MyTupleA)"
    remarkM $ "  Actual:   " <> outer_proj_show
    remarkM "  Expected: π₀(π₁(MyTupleA))"

    -- Test 5: A standard Hilbert term that doesn't match the project structure
    remarkM "Test 5: Standard Hilbert term hX 0 (X 0 :==: Constant A)"
    let simpleHilbert = hX 0 (X 0 :==: constA)
    simpleHilbert_show <- showObjM simpleHilbert
    remarkM "  Input:    hX 0 (X 0 :==: Constant A)"
    remarkM $ "  Actual:   " <> simpleHilbert_show
    remarkM "  Expected: ε𝑥₀(𝑥₀ = A)  (or similar default Hilbert rendering, NOT π)"

    -- == Negative Cases (Should Fail Parsing) ==

    -- Test 6 (Negative Case - RHS Not a Tuple)
    remarkM "Test 6: Hilbert term where RHS of equality is not a Tuple"
    let nonTupleRHS = hX 1 ( eX 0 ( Constant "A" :==: Constant "B" ) )
    nonTupleRHS_show <- showObjM nonTupleRHS
    remarkM "  Input:    hX 1 ( eX 0 ( Constant \"A\" :==: Constant \"B\" ) )"
    remarkM $ "  Actual:   " <> nonTupleRHS_show
    remarkM "  Expected: ε𝑥₁(∃𝑥₀(A = B)) (Default Hilbert rendering, NOT π)"





    -- Test 7 (Negative Case - Body Not Equality)
    remarkM "Test 7: Hilbert term where body inside Exists is not an Equality"
    let nonEqBody = hX 1 ( eX 0 ( Neg ( Constant "A" :==: pair (X 1) (X 0) ) ) )
    nonEqBody_show <- showObjM nonEqBody
    remarkM "  Input:    hX 1 ( eX 0 ( Neg ( Constant \"A\" :==: Tupl [X 1, X 0] ) ) )"
    remarkM $ "  Actual:   " <> nonEqBody_show
    remarkM "  Expected: ε𝑥₁(∃𝑥₀(¬(A = (𝑥₁,𝑥₀)))) (Default Hilbert rendering, NOT π)"


    remarkM "--- Project Shorthand Parsing Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of Cartesian Product (A × B)
testCrossProductRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testCrossProductRendering = do
    remarkM "--- Testing Cross Product Shorthand Rendering (A × B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"
    let setC = Constant "C" -- For comparison

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- == Positive Case: Render term created by crossProd helper ==
    remarkM "Test 1: Rendering term generated by crossProd A B"
    let prodAB = crossProd setA setB -- Use the helper function
    actualOutput <- showObjM prodAB     -- Use showObjM to trigger rendering
    let expectedOutput = "A × B"      -- Define the expected string output

    remarkM "  Input Term: crossProd A B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show prodAB) -- Uncomment to see raw structure if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do 
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseCrossProduct logic within toSubexpParseTree to be correct)"
    else
        do 
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseCrossProduct logic within toSubexpParseTree and showSubexpParseTree formatting)"

    -- == Negative Case (Optional): Ensure unrelated terms don't render as cross product ==
    remarkM "Test 2: Rendering a simple Tuple (A, B)"
    let tupleTerm = pair setA setB
    tupleOutput <- showObjM tupleTerm
    let expectedTupleOutput = "(A,B)" -- Or similar based on your tuple rendering
    remarkM "  Input Term: Tupl [A, B]"
    remarkM $ "  Actual Rendered Output: " <> tupleOutput
    remarkM $ "  Expected Rendered Output (e.g.): " <> expectedTupleOutput
    if tupleOutput /= expectedOutput && tupleOutput == expectedTupleOutput then
         remarkM "  Check: Rendering is not 'A × B' and matches tuple format. PASSED."
    else
         remarkM "  Check: Rendering is incorrect. FAILED."


    remarkM "--- Cross Product Rendering Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of FUNCS(A,B)
testFuncsSetRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testFuncsSetRendering = do
    remarkM "--- Testing FUNCS(A,B) Shorthand Rendering ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by funcsSet helper ==
    remarkM "Test 1: Rendering term generated by funcsSet A B"
    let funcsAB = funcsSet setA setB -- Use the helper function

    actualOutput <- showObjM funcsAB     -- Use showObjM to trigger rendering
    -- Note: Expecting 𝗙𝗨𝗡𝗖𝗦(A,B) based on default FuncApp/Tuple rendering
    let expectedOutput = "𝗙𝗨𝗡𝗖𝗦(A,B)"

 

    remarkM "  Input Term: funcsSet A B"
    --remarkM $ "  Internal Structure (for info): " <> (pack $ show funcsAB) -- Uncomment if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    --remarkM exp3


    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
          remarkM "  Check: Rendering matches expected output. PASSED."
          remarkM "  (Requires parseFuncsSet logic within toSubexpParseTree to be correct)"
    else
        do
          remarkM "  Check: Rendering does NOT match expected output. FAILED."
          remarkM "  (Check parseFuncsSet logic and showSubexpParseTree formatting for FuncApp/Tuple)"

    remarkM "--- FUNCS(A,B) Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Binary Union (A ∪ B)
testBinaryUnionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testBinaryUnionRendering = do
    remarkM "--- Testing Binary Union Shorthand Rendering (A ∪ B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by binaryUnion helper ==
    remarkM "Test 1: Rendering term generated by binaryUnion A B"
    let unionAB = setA .\/. setB -- Use the new helper function
    actualOutput <- showObjM unionAB     -- Use showObjM to trigger rendering
    let expectedOutput = "A ∪ B"      -- Define the expected string output

    remarkM "  Input Term: A .\\/. B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show unionAB) -- Uncomment to see raw structure if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseBinaryUnion logic within toSubexpParseTree to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseBinaryUnion logic within toSubexpParseTree and showSubexpParseTree formatting)"

    remarkM "--- Binary Union Rendering Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of Binary Intersection (A ∩ B)
testIntersectionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testIntersectionRendering = do
    remarkM "--- Testing Binary Intersection Shorthand Rendering (A ∩ B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by (./\.) helper ==
    remarkM "Test 1: Rendering term generated by A ./\\. B"
    let intersectionAB = setA ./\. setB -- Use the new operator
    actualOutput <- showObjM intersectionAB   -- Use showObjM to trigger rendering
    let expectedOutput = "A ∩ B"         -- Define the expected string output

    remarkM "  Input Term: A ./\\. B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show intersectionAB) -- Uncomment if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseIntersectionOp logic within toSubexpParseTree to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseIntersectionOp logic within toSubexpParseTree and showSubexpParseTree formatting)"

    remarkM "--- Binary Intersection Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Big Union (∪S)
testBigUnionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testBigUnionRendering = do
    remarkM "--- Testing Big Union Shorthand Rendering (∪S) ---"
    let setS = Constant "S"
    fakeConstM "S" ()

    remarkM "Test 1: Rendering term generated by bigUnion S"
    let unionS = bigUnion setS -- Use the helper function
    actualOutput <- showObjM unionS     -- Use showObjM to trigger rendering
    let expectedOutput = "∪S"      -- Define the expected string output

    remarkM "  Input Term: bigUnion S"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    if actualOutput == expectedOutput then
        remarkM "  Check: Rendering matches expected output. PASSED."
    else
        remarkM "  Check: Rendering does NOT match expected output. FAILED."

    remarkM "--- Big Union Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Big Intersection (∩S)
testBigIntersectionRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testBigIntersectionRendering = do
    remarkM "--- Testing Big Intersection Shorthand Rendering (∩S) ---"
    let setS = Constant "S"
    fakeConstM "S" () -- Assume S exists and is non-empty for the test definition

    remarkM "Test 1: Rendering term generated by bigIntersection S"
    let intersectionS = bigIntersection setS -- Use the helper function
    actualOutput <- showObjM intersectionS     -- Use showObjM to trigger rendering
    let expectedOutput = "∩S"         -- Define the expected string output

    remarkM "  Input Term: bigIntersection S"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    if actualOutput == expectedOutput then
        remarkM "  Check: Rendering matches expected output. PASSED."
    else
        remarkM "  Check: Rendering does NOT match expected output. FAILED."

    remarkM "--- Big Intersection Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Roster Notation {a, b, ...}
testRosterRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testRosterRendering = do
    remarkM "--- Testing Roster Notation Shorthand Rendering {..} ---"

    -- Setup Constants
    let elemA = Constant "A"
    let elemB = Constant "B"
    let elemC = Constant "C"
    let int1 = Integ 1

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()

    -- Test 1: Empty set
    --remarkM "Test 1: Rendering roster []"
    --let rosterEmpty = roster []
    --actualOutput1 <- showObjM rosterEmpty
    --let expectedOutput1 = "{}"
    --remarkM "  Input Term: roster []"
    --remarkM $ "  Actual Rendered Output:   " <> actualOutput1
    --remarkM $ "  Expected Rendered Output: " <> expectedOutput1
    --if actualOutput1 == expectedOutput1 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 2: Singleton set {A}
    remarkM "Test 2: Rendering roster [A]"
    let rosterA = roster [elemA]
    actualOutput2 <- showObjM rosterA
    let expectedOutput2 = "{A}"
    remarkM "  Input Term: roster [A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput2
    remarkM $ "  Expected Rendered Output: " <> expectedOutput2
    if actualOutput2 == expectedOutput2 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 3: Two element set {A, 1}
    remarkM "Test 3: Rendering roster [A, 1]"
    let rosterA1 = roster [elemA, int1]
    actualOutput3 <- showObjM rosterA1
    -- Note: Expected output depends on the derived Ord instance for ObjDeBr
    -- Integ constructor usually comes before Constant constructor
    let expectedOutput3 = "{1,A}"
    remarkM "  Input Term: roster [A, 1]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput3
    remarkM $ "  Expected Rendered Output: " <> expectedOutput3
    if actualOutput3 == expectedOutput3 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 4: Three element set {C, B, A} - testing sorting
    remarkM "Test 4: Rendering roster [C, B, A] (tests sorting)"
    let rosterCBA = roster [elemC, elemB, elemA]
    actualOutput4 <- showObjM rosterCBA
    let expectedOutput4 = "{A,B,C}" -- Assumes alphabetical sort for Constants
    remarkM "  Input Term: roster [C, B, A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput4
    remarkM $ "  Expected Rendered Output: " <> expectedOutput4
    if actualOutput4 == expectedOutput4 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."

    -- Test 5: Set with duplicates {B, A, A} - testing deduplication
    remarkM "Test 5: Rendering roster [B, A, A] (tests deduplication)"
    let rosterBAA = roster [elemB, elemA, elemA]
    actualOutput5 <- showObjM rosterBAA
    let expectedOutput5 = "{A,B}" -- Sorted and deduplicated
    remarkM "  Input Term: roster [B, A, A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput5
    remarkM $ "  Expected Rendered Output: " <> expectedOutput5
    if actualOutput5 == expectedOutput5 then remarkM "  Check: PASSED." else remarkM "  Check: FAILED."


    remarkM "--- Roster Notation Rendering Tests Complete ---"
    return ()


-- Test function for the shorthand rendering of Set Difference (A \\ B)
testSetDifferenceRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testSetDifferenceRendering = do
    remarkM "--- Testing Set Difference Shorthand Rendering (A \\\\ B) ---"

    -- Setup Constants for sets
    let setA = Constant "A"
    let setB = Constant "B"

    fakeConstM "A" ()
    fakeConstM "B" ()

    -- == Positive Case: Render term created by (.\.) helper ==
    remarkM "Test 1: Rendering term generated by A .\\. B"
    let differenceAB = setA .\. setB -- Use the new operator
    actualOutput <- showObjM differenceAB   -- Use showObjM to trigger rendering
    let expectedOutput = "A ∖ B"         -- Define the expected string output (double backslash for Haskell String)

    remarkM "  Input Term: A .\\. B"
    -- remarkM $ "  Internal Structure (for info): " <> (pack $ show differenceAB) -- Uncomment if needed
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parseSetDifference logic and rendering logic in Rendering.hs to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parseSetDifference, Rendering.hs formatting, and binaryOpInData)"

    remarkM "--- Set Difference Rendering Tests Complete ---"
    return ()

-- Test function for the shorthand rendering of Power Set P(A)
testPowerSetRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testPowerSetRendering = do
    remarkM "--- Testing Power Set Shorthand Rendering (P(A)) ---"

    -- Setup Constant for set
    let setA = Constant "A"
    fakeConstM "A" ()

    -- == Positive Case: Render term created by powerSet helper ==
    remarkM "Test 1: Rendering term generated by powerSet A"
    let pSetA = powerSet setA -- Use the helper function
    actualOutput <- showObjM pSetA     -- Use showObjM to trigger rendering
    -- User specified Unicode Script P (U+1D4AB)
    let expectedOutput = "𝒫(A)"
    remarkM "  Input Term: powerSet A"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput
    remarkM $ "  Expected Rendered Output: " <> expectedOutput

    -- Check if rendering matches expectation
    if actualOutput == expectedOutput then
        do
            remarkM "  Check: Rendering matches expected output. PASSED."
            remarkM "  (Requires parsePowerSet logic and rendering logic in Rendering.hs to be correct)"
    else
        do
            remarkM "  Check: Rendering does NOT match expected output. FAILED."
            remarkM "  (Check parsePowerSet, Rendering.hs formatting and ParseTreeConst)"

    remarkM "--- Power Set Rendering Tests Complete ---"
    return ()


testPairAndTupleRendering :: ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testPairAndTupleRendering = do
    remarkM "--- Testing Pair and Tuple Rendering (Kuratowski) ---"

    -- Setup Constants for elements
    let constA = Constant "A"
    let constB = Constant "B"
    let constC = Constant "C"
    let constD = Constant "D"
    let int1 = Integ 1
    let int2 = Integ 2

    fakeConstM "A" ()
    fakeConstM "B" ()
    fakeConstM "C" ()
    fakeConstM "D" ()

    -- Test 1: Simple Pair (A, B)
    remarkM "Test 1: Rendering pair A B"
    let pairAB = pair constA constB
    actualOutput1 <- showObjM pairAB
    let expectedOutput1 = "(A,B)"
    remarkM "  Input Term: pair A B"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput1
    remarkM $ "  Expected Rendered Output: " <> expectedOutput1
    if actualOutput1 == expectedOutput1 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (Verify parsePair and Tuple rendering in Rendering.hs)"

    -- Test 2: Pair with an integer (1, C)
    remarkM "Test 2: Rendering pair (Integ 1) C"
    let pair1C = pair int1 constC
    actualOutput2 <- showObjM pair1C
    let expectedOutput2 = "(1,C)"
    remarkM "  Input Term: pair (Integ 1) C"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput2
    remarkM $ "  Expected Rendered Output: " <> expectedOutput2
    if actualOutput2 == expectedOutput2 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 3: Simple Tuple (A, B, C) - built as Pair A (Pair B C)
    remarkM "Test 3: Rendering tuple [A, B, C]"
    let tupleABC = tuple [constA, constB, constC]
    actualOutput3 <- showObjM tupleABC
    let expectedOutput3 = "(A,B,C)"
    remarkM "  Input Term: tuple [A, B, C]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput3
    remarkM $ "  Expected Rendered Output: " <> expectedOutput3
    if actualOutput3 == expectedOutput3 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (Verify parseTupleMax/parseTupleFixed and Tuple rendering)"

    -- Test 4: Tuple with mixed types (A, 1, B, 2)
    remarkM "Test 4: Rendering tuple [A, (Integ 1), B, (Integ 2)]"
    let tupleA1B2 = tuple [constA, int1, constB, int2]
    actualOutput4 <- showObjM tupleA1B2
    let expectedOutput4 = "(A,1,B,2)"
    remarkM "  Input Term: tuple [A, (Integ 1), B, (Integ 2)]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput4
    remarkM $ "  Expected Rendered Output: " <> expectedOutput4
    if actualOutput4 == expectedOutput4 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 5: Single element tuple (A) - tuple [A] should just be A
    remarkM "Test 5: Rendering tuple [A]"
    let tupleA_single = tuple [constA]
    actualOutput5 <- showObjM tupleA_single
    let expectedOutput5 = "A" -- As per tuple [x] -> x
    remarkM "  Input Term: tuple [A]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput5
    remarkM $ "  Expected Rendered Output: " <> expectedOutput5
    if actualOutput5 == expectedOutput5 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 6: Empty tuple - tuple [] should be EmptySet, rendered as ∅
    remarkM "Test 6: Rendering tuple []"
    let tupleEmpty = tuple []
    actualOutput6 <- showObjM tupleEmpty
    let expectedOutput6 = "∅" -- Assuming EmptySet renders as ∅
    remarkM "  Input Term: tuple [] (which is EmptySet)"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput6
    remarkM $ "  Expected Rendered Output: " <> expectedOutput6
    if actualOutput6 == expectedOutput6 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (Verify EmptySet rendering or tuple [] behavior)"

    -- Test 7: Nested Pairs/Tuples - Pair (Pair A B) C -> ((A,B),C)
    remarkM "Test 7: Rendering pair (pair A B) C"
    let nestedPair = pair (pair constA constB) constC
    actualOutput7 <- showObjM nestedPair
    let expectedOutput7 = "((A,B),C)"
    remarkM "  Input Term: pair (pair A B) C"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput7
    remarkM $ "  Expected Rendered Output: " <> expectedOutput7
    if actualOutput7 == expectedOutput7 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED."

    -- Test 8: A Kuratowski pair that is NOT created by pair, but by roster directly
    -- This tests if parsePair can still recognize it for tuple rendering.
    remarkM "Test 8: Rendering a direct Kuratowski pair roster [roster[A], roster[A,B]]"
    let directKuratowski = roster [roster[constA], roster[constA, constB]]
    actualOutput8 <- showObjM directKuratowski
    let expectedOutput8 = "(A,B)" -- Expecting it to be parsed as a pair
    remarkM "  Input Term: roster [roster[A], roster[A,B]]"
    remarkM $ "  Actual Rendered Output:   " <> actualOutput8
    remarkM $ "  Expected Rendered Output: " <> expectedOutput8
    if actualOutput8 == expectedOutput8 then
        remarkM "  Check: PASSED."
    else
        remarkM "  Check: FAILED. (parsePair might not be robust enough, or roster rendering interferes)"

    remarkM "--- Pair and Tuple Rendering Tests Complete ---"
    return ()


testAxiomOfChoice :: ProofGenTStd () [ZFCRuleDeBr] PropDeBr Text () IO ()
testAxiomOfChoice = do
    -- Test for Axiom of Choice
    (acAx, acAxIdx) <- axiomOfChoiceM

    showAcAx <- showPropM acAx
    remarkM $ "Axiom of Choice: " <> showAcAx <> " at index " <> pack (show acAxIdx)
    -- Due to its complexity, you might want to add a remark with its raw structure too for debugging:
    -- remarkM $ "Raw AC: " <> pack (show acAx)
    return ()






main :: IO ()
main = do



    let y0 = (Integ 0 :==: Integ 0) :->: (Integ 99 :==: Integ 99)
    let y1 = Integ 0 :==: Integ 0
    let y2 = (Integ 99 :==: Integ 99) :->: (Integ 1001 :==: Integ 1001)
    let x0 = eX 0 (aX 0 ((Integ 0 :==: V 102) :&&: (X 0 `In` X 1)) :&&: (X 1 `In` X 1))
    let x1 = aX 3 (aX 2 (aX 1 ((X 3 :==: X 2) :&&: aX 0 (X 0 :==: X 1))))
    --(print . show) (checkSanity [] [(),()] mempty x0)
    print "X1" 

    (putStrLn . show) x1
    let xv = aX 10 (aX 21 (aX 1 (X 10 :==: X 21 :&&: aX 0 (X 0 :==: X 1))))
    -- ∀𝑥₃(∀𝑥₂(∀𝑥₁(𝑥₃ = 𝑥₂ ∨ ∀𝑥₀(𝑥₀ = 𝑥₁))))
    let cxv = xv
    (putStrLn . show) cxv
    let f = parseForall x1
    case f of
        Just (f,()) -> do
            let term1 = hX 0 (Integ 0 `In` Integ 0)
            let fNew = f term1
            (print.show) fNew
        Nothing -> print "parse failed!"
       --let z = applyUG xn () 102
--    -- (print . show) z
    let proof = (   fakeProp [] y0
                <> fakeProp [] y1 
                <> fakeProp [] y2
                <> mp y0
                <> mp y2
                <> proofByAsm y1 (Integ 99 :==: Integ 99) (mp $ y1 .->. (Integ 99 :==: Integ 99))
                )
                  ::[PropRuleDeBr]
    let zb = runProof proof

    -- either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb
    print "OI leave me alone"
    let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :<=: Integ 0))
    let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ 0))
    let generalized = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :==: Integ 0))
    let asm = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
    let mid = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 0)

    let proof2 =    fakeConst "N" ()
                 <> fakeProp [] z1
                 <> fakeProp [] z2
                 <> proofByUG generalized
                                        (
                                            proofByAsm asm z1 (
                                                    ui (V 0) z1
                                                <> mp ( asm .->. (V 0 :<=: Integ 0))
                                                <> simpL ((V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10))
                                                <> adj (V 0 `In` Constant "N") (V 0 :<=: Integ 0)
                                                <> ui (V 0) z2
                                                <> mp ( mid .->. (V 0 :==: Integ 0)  )
                                            )  
                                        )
                                    ::[PredRuleDeBr]

    let proof3 = proofByUG generalized
                                     (
                                        proofByAsm asm z1 (
                                                ui (V 0) z1
                                             <> mp ( asm .->. (V 0 :<=: Integ 0))
                                      
                                            )
                                     )
                                  ::[PredRuleDeBr]
                 
    let zb2 = runProof proof2 

    let zb3 = runProof ((fakeConst "N" () <> fakeProp [] z1 <> fakeProp [] z2 <> ui (V 0) z1)::[PredRuleDeBr])
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

    print "TEST ROSTER RENDERING BEGIN-------------------------------------"
    (aRos, bRos, cRos, dRos) <- runProofGeneratorT testRosterRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cRos -- Print results


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


    print "TEST COMPLEX SUBSET NOTATION BEGIN-------------------------------------"
    (aCSub, bCSub, cCSub, dCSub) <- runProofGeneratorT testComplexSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cCSub -- Print results

    print "TEST STRICT SUBSET NOTATION BEGIN-------------------------------------"
    (aStrict, bStrict, cStrict, dStrict) <- runProofGeneratorT testStrictSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cStrict -- Print results


    print "TEST NOT SUBSET NOTATION BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testNotSubsetNotation
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results

    print "TEST builderX BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testBuilderXSuite
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results


    print "TEST AICLAIMX BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testCompositionImplementation
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results

    print "TEST SH BEGIN-------------------------------------"
    (aNSub, bNSub, cNSub, dNSub) <- runProofGeneratorT testShorthandRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cNSub -- Print results

    print "TEST PROJECT SHORTHAND PARSING BEGIN-------------------------------------"
    (aPrj, bPrj, cPrj, dPrj) <- runProofGeneratorT testProjectShorthandParsing
    (putStrLn . unpack . showPropDeBrStepsBase) cPrj -- Print results


    print "TEST CROSS PRODUCT PARSING BEGIN-------------------------------------"
    (aXP, bXP, cXP, dXP) <- runProofGeneratorT testCrossProductRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cXP -- Print results


    print "TEST BINARY UNION RENDERING BEGIN-------------------------------------"
    (aBU, bBU, cBU, dBU) <- runProofGeneratorT testBinaryUnionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBU -- Print results



    print "TEST BINARY INTERSECTION RENDERING BEGIN-------------------------------------"
    (aBI, bBI, cBI, dBI) <- runProofGeneratorT testIntersectionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBI -- Print results

    print "TEST BIG UNION RENDERING BEGIN-------------------------------------"
    (aBU, bBU, cBU, dBU) <- runProofGeneratorT testBigUnionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBU -- Print results

    print "TEST BIG INTERSECTION RENDERING BEGIN-------------------------------------"
    (aBI, bBI, cBI, dBI) <- runProofGeneratorT testBigIntersectionRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cBI -- Print results

   

    print "TEST SET DIFFERENCE RENDERING BEGIN-------------------------------------"
    (aDiff, bDiff, cDiff, dDiff) <- runProofGeneratorT testSetDifferenceRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cDiff -- Print results

    print "TEST POWER SET RENDERING BEGIN-------------------------------------"
    (aPow, bPow, cPow, dPow) <- runProofGeneratorT testPowerSetRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cPow -- Print results

    -- print "TEST EMPTY SET RENDERING BEGIN-------------------------------------"
    -- (aEmp, bEmp, cEmp, dEmp) <- runProofGeneratorT testEmptySetRendering
    -- (putStrLn . unpack . showPropDeBrStepsBase) cEmp -- Print results
    print "TEST PAIR AND TUPLE RENDERING (KURATOWSKI) BEGIN-------------------------------------"
    (aPT, bPT, cPT, dPT) <- runProofGeneratorT testPairAndTupleRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cPT -- Print results

    print "TEST AXIOM OF CHOICE BEGIN-------------------------------------"
    (aAC, bAC, cAC, dAC) <- runProofGeneratorT testAxiomOfChoice
    (putStrLn . unpack . showPropDeBrStepsBase) cAC -- Print results

    print "TEST FUNCS(A,B) RENDERING BEGIN-------------------------------------"
    (aFSR, bFSR, cFSR, dFSR) <- runProofGeneratorT testFuncsSetRendering
    (putStrLn . unpack . showPropDeBrStepsBase) cFSR -- Print results

--    print "TEST BINARY UNION EXISTS SCHEMA-------------------------------------"
--    (a,b,c,d) <- checkTheoremM (binaryUnionExistsSchema::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


    print "SPEC TO BUILDER THEOREM-------------------------------------"
    let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
    let source_set_template = X 1 .\/. X 2
    let (source_set_func,p_pred_func) = lambdaSpec (1,2) 0 source_set_template p_template
    return ()
    --(a,b,c,d) <- checkTheoremM (builderSchema source_set_func p_pred_func   ) 
     -- ::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ((ObjDeBr,ObjDeBr) -> ObjDeBr)))
    --(putStrLn . unpack . showPropDeBrStepsBase) d -- Print results



    -- error "STOPPING HERE"

    --print "SPEC TO BUILDER THEOREM 2-------------------------------------"
    --let p_template = Constant "C" :==: X 0
    --let source_set_template = Constant "S"
    --let (source_set_func,p_pred_func) = lambdaSpec [] 0 source_set_template p_template
    --(a,b,c,d) <- checkTheoremM (builderSchema source_set_func p_pred_func::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ([ObjDeBr] -> ObjDeBr)))
    --(putStrLn . unpack . showPropDeBrStepsBase) d -- Print results
    


--    print "TEST BINARY INTERSECTION EXISTS SCHEMA-------------------------------------"
--    (a,b,c,d) <- checkTheoremM (binaryIntersectionExistsSchema::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

--    print "TEST BINARY CROSSPRODDEFEQUIV SCHEMA-------------------------------------"
--    (a,b,c,d) <- checkTheoremM (crossProductDefEquivSchema::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

--    print "TEST CROSSPROD EXISTS SCHEMA ---------------------------"
--    (a,b,c,d) <- checkTheoremM (crossProductExistsSchema::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

--    print "TEST BUILDER SUBSET THEOREM-------------------------------------"
--    let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
--    let source_set_template = X 1 .\/. X 2
--    (a,b,c,d) <- checkTheoremM 
--         (builderSubsetTheoremSchema [1,2] 0 source_set_template p_template 
--              ::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

--    print "TEST BUILDER SOURCE PARTITION THEOREM--------------------"
--    let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
--    let source_set_template = X 1 .\/. X 2
--    (a,b,c,d) <- checkTheoremM (builderSrcPartitionSchema [1,2] 0 source_set_template p_template 
--            ::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results



--    print "TEST UNION WITH EMPTY SET THEOREM-------------------------------------"
--    (a,b,c,d) <- checkTheoremM (unionWithEmptySetSchema::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results

--    print "DISJOINT SUBSET IS EMPTY THEOREM-------------------------------------"
--    (a,b,c,d) <- checkTheoremM (disjointSubsetIsEmptySchema::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


--    print "SPEC REDUNDANCY THEOREM-------------------------------------"
--    let p_template = Constant "C" :+: X 0 :==: (X 1 :+: X 2)
--    let source_set_template = X 1 .\/. X 2
--    (a,b,c,d) <- checkTheoremM (specRedundancySchema [1,2] 0 source_set_template p_template
--                       ::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


--    print "SPEC REDUNDANCY THEOREM TEST 2-------------------------------------"
--    let p_template = X 0 .==. X 0
--    let source_set_template = Constant "SourceSet"
--    (a,b,c,d) <- checkTheoremM (specRedundancySchema [] 0 source_set_template p_template
--                                   ::(TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text ()IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results



--    print "SPEC ANTI-REDUNDANCY THEOREM-------------------------------------"
--    let p_template = Constant "C" .+. X 0 .==. (X 1 .+. X 2)
--    let source_set_template = X 1 .\/. X 2
--    (a,b,c,d) <- checkTheoremM (specAntiRedundancySchema [1,2] 0 source_set_template p_template
--                   :: (TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results



--    print "SPEC ANTI-REDUNDANCY THEOREM TEST 2-------------------------------------"
--    let p_template = X 0 .==. X 0
--    let source_set_template = Constant "SourceSet"
--    (a,b,c,d) <- checkTheoremM (specAntiRedundancySchema [] 0 source_set_template p_template
--                       :: (TheoremSchemaMT () [ZFCRuleDeBr] PropDeBr Text () IO ()))
--    (putStrLn . unpack . showPropDeBrStepsBase) d -- Print results


 
--    return ()



testprog::ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testprog = do
      let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :<=: Integ 0))
      showZ1 <- showPropM z1
      remarkM $ showZ1 <> " Z1Z1Z1Z1" 
      let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ 0))
      let asm = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
      let asm2 = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
      fakeConstM "N" ()
      fakePropM [] z1
      fakePropM [] z2
      
      fux<- PRED.runProofByUGM () $ do
          runProofByAsmM  asm2 do
              (s5,_,_)<- runProofBySubArgM  do
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
        (notZ1,_) <- fakePropM [](Neg z1)
        (falseness,_) <- contraFM z1
        showF <- showPropM falseness
        remarkM $ showF <> " is the falseness"
      showAbsurdImp <- showPropM absurdImp
      remarkM $ showAbsurdImp <> " is the absurdity"
      absurdM absurdImp
      return ()

testprog2::ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()IO ()
testprog2 = do
    let p = eX 0 (X 0 `In` Constant "N")
    let q = eX 0 (X 0 .<=. Integ 10)
    let pImpQ = p :->: q
    fakeConstM "N" ()
    fakePropM [] pImpQ
    fakePropM [] (neg q)
    (s,idx) <- modusTollensM pImpQ
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


testprog3::ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testprog3 = do
    let a = eX 0 (X 0 `nIn` Constant "N")
    fakeConstM "N" ()
    fakePropM [] a
    (s,idx) <- reverseANegIntroM a
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()

testprog4::ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testprog4 = do
    let a = aX 0 (X 0 `nIn` Constant "N")
    fakeConstM "N" ()
    fakePropM [] a
    (s,idx) <- reverseENegIntroM a
    showS <- showPropM s
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


testprog5::ProofGenTStd () [PredRuleDeBr] PropDeBr Text () IO ()
testprog5 = do
    let a = eXBang 99 (Neg (X 99 `In` Constant "N"))
    fakeConstM "N" ()
    (s,idx) <- fakePropM [] a


    showS <- showPropM a
    remarkM $ showS <> " is the sentence. It was proven in line " <> (pack . show) idx
    return ()


theoremProg::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => ProofGenTStd () [PredRuleDeBr] PropDeBr Text ()m ()
theoremProg = do
    let z1 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 10) :->: (X 0 :<=: Integ 0))
    let z2 = aX 0 ((X 0 `In` Constant "N") :&&: (X 0 :<=: Integ 0) :->: (X 0 :==: Integ  0))
    let asm = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
    let asm2 = (V 0 `In` Constant "N") :&&: (V 0 :<=: Integ 10)
    (generalized, _, _ ) <- PRED.runProofByUGM () $ do
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

