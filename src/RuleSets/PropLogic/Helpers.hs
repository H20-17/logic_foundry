{-# LANGUAGE ConstraintKinds #-}

module RuleSets.PropLogic.Helpers
(
    mpM, simpLM,
    simpRM, adjM, runProofByAsmM,
    contraFM, absurdM, MetaRuleError(..), disjIntroLM, disjIntroRM, disjElimM, doubleNegElimM,
    deMorganConjM, deMorganDisjM, bicondIntroM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM,
    peircesLawM, modusTollensM, imp2DisjM, negAndNotToOrM, negImpToConjViaEquivM, negBicondToPosBicondM,
    disjunctiveSyllogismM, exFalsoM, deconstructAdjM, deconstructMultiAdjM, commOrM
) where

import qualified RuleSets.PropLogic.Core as PROPL

import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless, when )
import Data.Set (Set, fromList)
import Data.List (mapAccumL,intersperse)
import qualified Data.Set as Set
import Data.Text ( pack, Text, unpack,concat)
import Data.Map
    ( (!), foldrWithKey, fromList, insert, keysSet, lookup, map, Map )
import Control.Applicative ( Alternative((<|>)) )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Catch
    ( SomeException, MonadThrow(..), Exception )
import GHC.Stack.Types ( HasCallStack )
import Data.Data (Typeable)
import GHC.Generics (Associativity (NotAssociative, RightAssociative, LeftAssociative))
import Control.Arrow ( left )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.Reader ( MonadReader(ask) )
import Control.Monad.State ( MonadState(get) )
import Control.Monad.Writer ( MonadWriter(tell) )
import StdPattern
    ( PrfStdState(..),
      PrfStdContext(..),
      Proof,
      TestSubproofErr(..),
      StdPrfPrintMonad,
      TypedSent(..),
      PrfStdStep(PrfStdStepStep,PrfStdStepSubproof),
      ProofStd,
      ProofGenTStd,
      monadifyProofStd,
      modifyPS,
      RuleInject(..),
      getProofState,
      )

import Kernel
import Internal.StdPattern

import RuleSets.BaseLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError,
   SubproofError,
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   HelperConstraints(..))
import qualified RuleSets.BaseLogic.Core as REM
import RuleSets.BaseLogic.Helpers
import RuleSets.PropLogic.Core







standardRuleM :: HelperConstraints r s o tType sE eL q t m
       => r -> ProofGenTStd tType r s o q t m s
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayProp <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayProp


mpM, exclMidM, simpLM, simpRM, absurdM, doubleNegElimM, deMorganConjM, 
       deMorganDisjM, bicondElimLM, bicondElimRM, absorpAndM, absorpOrM, distAndOverOrM, distOrOverAndM, 
       peircesLawM, contraFM ::
       HelperConstraints r s o tType sE eL q t m
          => s -> ProofGenTStd tType r s o q t m s

adjM, disjIntroLM, disjIntroRM,  bicondIntroM  ::
         HelperConstraints r s o tType sE eL q t m
          => s -> s -> ProofGenTStd tType r s o q t m s

disjElimM ::
       HelperConstraints r s o tType sE eL q t m
          => s -> s -> s -> ProofGenTStd tType r s o q t m s


-- | Proves 'B ∨ A' from a given proof of 'A ∨ B'.
-- | This demonstrates the commutativity of disjunction using proof by cases (∨-Elimination).
-- | This helper assumes 's_a_or_b' (A ∨ B) is already proven in the context.
commOrM :: HelperConstraints r1 s o tType sE eL q t m =>
            s -- ^ A proven proposition 's_a_or_b' of the form (A ∨ B).
            -> ProofGenTStd tType r1 s o q t m s -- ^ Returns the proven proposition (B ∨ A) and its proof index.
commOrM s_a_or_b = do
    -- 1. Parse the input disjunction s_a_or_b = (A ∨ B) to get terms A and B.
    (a_term, b_term) <- maybe (throwM $ MetaRuleErrNotDisj s_a_or_b) return (parseDisj s_a_or_b)

    -- Reiterate the proven premise 'A ∨ B'
    repM s_a_or_b

    -- 2. Case 1: Prove A → (B ∨ A)
    --    Start a subproof assuming 'a_term' (A).
    (a_implies_b_or_a, _) <- runProofByAsmM a_term $ do
        -- We have 'a_term' (A) proven by assumption.
        -- We want to prove 'b_term ∨ a_term' (B ∨ A).
        -- Use `disjIntroRM` (introduce on right):
        --   `disjIntroRM b_term a_term` takes term `b_term` and proven `a_term`
        --   and proves `b_term ∨ a_term`.
        disjIntroRM b_term a_term
        return ()

    -- 3. Case 2: Prove B → (B ∨ A)
    --    Start a subproof assuming 'b_term' (B).
    (b_implies_b_or_a, _) <- runProofByAsmM b_term $ do
        -- We have 'b_term' (B) proven by assumption.
        -- We want to prove 'b_term ∨ a_term' (B ∨ A).
        -- Use `disjIntroLM` (introduce on left):
        --   `disjIntroLM b_term a_term` takes proven `b_term` and term `a_term`
        --   and proves `b_term ∨ a_term`.
        disjIntroLM b_term a_term
        return ()

    -- 4. Apply Disjunction Elimination.
    --    We have:
    --      1. s_a_or_b:          A ∨ B
    --      2. a_implies_b_or_a:  A → (B ∨ A)
    --      3. b_implies_b_or_a:  B → (B ∨ A)
    --    The result will be (B ∨ A).
    disjElimM s_a_or_b a_implies_b_or_a b_implies_b_or_a








mpM s = standardRuleM (mp s)
exclMidM s = standardRuleM (exclMid s)
simpLM s = standardRuleM (simpL s)
simpRM s = standardRuleM (simpR s)
adjM a b = standardRuleM (adj a b)
contraFM s = standardRuleM (contraF s)
absurdM s = standardRuleM (absurd s)
disjIntroLM a b = standardRuleM (disjIntroL a b)
disjIntroRM a b = standardRuleM (disjIntroR a b)
disjElimM p q r = standardRuleM (disjElim p q r)
doubleNegElimM s = standardRuleM (doubleNegElim s)
deMorganConjM s = standardRuleM (deMorganConj s)
deMorganDisjM s = standardRuleM (deMorganDisj s)
bicondIntroM a b = standardRuleM (bicondIntro a b)
bicondElimLM s = standardRuleM (bicondElimL s)
bicondElimRM s = standardRuleM (bicondElimR s)
absorpAndM s = standardRuleM (absorpAnd s)
absorpOrM s = standardRuleM (absorpOr s)
distAndOverOrM s = standardRuleM (distAndOverOr s)
distOrOverAndM s = standardRuleM (distOrOverAnd s)
peircesLawM p = standardRuleM (peircesLaw p)

data MetaRuleError s sE where
    MetaRuleErrNotImp :: s -> MetaRuleError s sE
    MetaRuleErrNotModusTollens :: s -> MetaRuleError s sE
    MetaRuleErrNotAdj :: s -> MetaRuleError s sE
    MetaRuleErrNotNeg :: s -> MetaRuleError s sE
    MetaRuleErrNotDisj :: s -> MetaRuleError s sE
    MetaRuleErrNotNegBicond :: s -> MetaRuleError s sE
    MetaRuleErrNotBicond :: s -> MetaRuleError s sE
    MetaRuleErrDisjSyllNotDisj :: s -> MetaRuleError s sE
    BigExceptAsmSanity :: s -> sE -> MetaRuleError s sE
    MetaRuleErrDeconstructMultiAdjMNonNegSplits :: Int -> MetaRuleError s sE
    deriving (Show,Typeable)


instance (Show s, Typeable s, Show sE, Typeable sE) => Exception (MetaRuleError s sE)

-- | Given a proven implication 's' (of the form A → B), this function
-- | derives and proves its equivalent disjunctive form: ¬A ∨ B.
-- | This transformation is known as Material Implication.
-- |
-- | The proof strategy is as follows:
-- | 1. Given s: A → B.
-- | 2. Parse 's' to identify the antecedent A (term `a`) and consequent B (term `b`).
-- | 3. Prove A ∨ ¬A using the Law of Excluded Middle (`exclMidM`).
-- | 4. Case 1 (Subproof 1): Assume A.
-- |    a. From the assumed A and the given A → B, derive B using Modus Ponens (`mpM`).
-- |    b. From the derived B, introduce the disjunction ¬A ∨ B using `disjIntroRM`.
-- |    This subproof concludes A → (¬A ∨ B).
-- | 5. Case 2 (Subproof 2): Assume ¬A.
-- |    a. From the assumed ¬A, introduce the disjunction ¬A ∨ B using `disjIntroLM`.
-- |    This subproof concludes ¬A → (¬A ∨ B).
-- | 6. Apply Disjunction Elimination (`disjElimM`) using:
-- |    - The proven A ∨ ¬A (from step 3).
-- |    - The proven A → (¬A ∨ B) (from step 4).
-- |    - The proven ¬A → (¬A ∨ B) (from step 5).
-- |    The result is ¬A ∨ B.
-- |
-- | Note on Naming: The name 'imp2ConjM' is misleading for this function,
-- | as it transforms an implication into a disjunction.
-- | A more appropriate name would be 'impToDisjM' or 'materialImplicationM'.
imp2DisjM :: HelperConstraints r1 s o tType sE eL q t m =>
            s -- ^ A proven proposition 's' of the form (A → B).
            -> ProofGenTStd tType r1 s o q t m s -- ^ Returns the proven proposition (¬A ∨ B) and its proof index.
imp2DisjM s_imp_ab = do
    -- 1. Parse the input implication s_imp_ab = (a -> b) to extract antecedent 'a' and consequent 'b'.
    (a_term, b_term) <- maybe (throwM $ MetaRuleErrNotImp s_imp_ab) return (parse_implication s_imp_ab)

    -- The target proposition we want to prove directly.
    let target_disjunction = neg a_term .||. b_term

    -- 2. Prove A ∨ ¬A using Excluded Middle.
    a_or_not_a_proven <- exclMidM a_term

    -- 3. Case 1 Subproof: Prove A → (¬A ∨ B)
    (a_implies_target, _) <- runProofByAsmM a_term $ do
        -- 'a_term' is assumed.
        -- Use the original proven implication 's_imp_ab' (A → B) and the assumed 'a_term' (A)
        -- to derive 'b_term' (B) by Modus Ponens.
        b_derived <- mpM s_imp_ab
        -- From the derived 'b_derived' (B), introduce the disjunction (¬A ∨ B).
        disjIntroRM (neg a_term) b_derived
        return () -- Subproof concludes with (¬A ∨ B)

    -- 4. Case 2 Subproof: Prove ¬A → (¬A ∨ B)
    (not_a_implies_target, _) <- runProofByAsmM (neg a_term) $ do
        -- 'neg a_term' (¬A) is assumed.
        -- From the assumed 'neg a_term' (¬A), introduce the disjunction (¬A ∨ B).
        disjIntroLM (neg a_term) b_term
        return () -- Subproof concludes with (¬A ∨ B)

    -- 5. Apply Disjunction Elimination.
    --    We have proven:
    --      1. a_or_not_a_proven:      A ∨ ¬A
    --      2. a_implies_target:        A → (¬A ∨ B)
    --      3. not_a_implies_target:    ¬A → (¬A ∨ B)
    --    The result will be (¬A ∨ B).
    disjElimM a_or_not_a_proven a_implies_target not_a_implies_target


-- | Given a proven disjunction 's_notA_or_B' (of the form ¬A ∨ B),
-- | this function derives and proves its equivalent implicative form: A → B.
-- | This transformation is the reverse of Material Implication.
-- |
-- | The proof strategy is:
-- | 1. Given s: ¬A ∨ B.
-- | 2. To prove A → B, assume A.
-- | 3. Under the assumption of A, we need to derive B. This is done by assuming ¬B
-- |    for a proof by contradiction (RAA) to derive B.
-- |    a. Assume ¬B.
-- |    b. From the assumed A and assumed ¬B, form A ∧ ¬B using Adjunction.
-- |    c. Transform A ∧ ¬B into ¬(¬A ∨ B) using De Morgan's laws and Double Negation.
-- |       (Specifically, A ∧ ¬B  ⇔  ¬¬A ∧ ¬B  ⇔  ¬(¬(¬¬A) ∨ ¬(¬B))  ⇔  ¬(A ∨ B) - no, this is wrong.
-- |        A ∧ ¬B  ⇔  ¬(¬(A ∧ ¬B)) ⇔ ¬(¬A ∨ ¬(¬B)) ⇔ ¬(¬A ∨ B) )
-- |       The direct De Morgan for this is ¬(P → Q) ⇔ P ∧ ¬Q.
-- |       We need to show that (A ∧ ¬B) contradicts (¬A ∨ B).
-- |       (A ∧ ¬B) is true. (¬A ∨ B) is true.
-- |       If (¬A ∨ B) is true:
-- |           Case i: ¬A is true. This contradicts A (from A ∧ ¬B). So False.
-- |           Case ii: B is true. This contradicts ¬B (from A ∧ ¬B). So False.
-- |       Since both disjuncts of (¬A ∨ B) lead to a contradiction if (A ∧ ¬B) is also true,
-- |       then (A ∧ ¬B) and (¬A ∨ B) are contradictory.
-- |    d. A formal derivation of False from (A ∧ ¬B) and (¬A ∨ B):
-- |       i.   A (from A ∧ ¬B)
-- |       ii.  ¬B (from A ∧ ¬B)
-- |       iii. ¬A ∨ B (original premise)
-- |       iv.  Subproof 1: Assume ¬A. Contradiction with (i). So False. (¬A → False)
-- |       v.   Subproof 2: Assume B. Contradiction with (ii). So False. (B → False)
-- |       vi.  DisjElim on (iii), (iv), (v) yields False.
-- |    e. So, assuming ¬B (in context of A and ¬A ∨ B) led to False. (¬B → False)
-- | 4. By RAA (absurdM), from (¬B → False), derive ¬¬B.
-- | 5. By Double Negation Elimination, from ¬¬B, derive B.
-- | 6. Since assuming A led to B, conclude A → B.
disj2ImpM :: HelperConstraints r1 s o tType sE eL q t m =>
            s -- ^ A proven proposition 's' of the form (¬A ∨ B).
            -> ProofGenTStd tType r1 s o q t m s -- ^ Returns the proven proposition (A → B) and its proof index.
disj2ImpM s_notA_or_B_proven = do
    -- 1. Parse the input disjunction s_notA_or_B_proven = (¬A ∨ B)
    --    to get terms ¬A (not_a_term_parsed), B (b_term_parsed), and A (a_term_parsed).
    (not_a_term_parsed, b_term_parsed) <- maybe (throwM $ MetaRuleErrNotDisj s_notA_or_B_proven)
                                              return (parseDisj s_notA_or_B_proven)
    a_term_parsed <- maybe (throwM $ MetaRuleErrNotNeg not_a_term_parsed)
                           return (parseNeg not_a_term_parsed)

    -- 2. Goal: Prove A → B. Start a subproof assuming A ('a_term_parsed').
    (resSent,_) <- runProofByAsmM a_term_parsed $ do
        -- Current assumption in this scope: 'a_term_parsed' (A) is proven.
        -- We also have 's_notA_or_B_proven' (¬A ∨ B) from the outer scope.
        -- Goal: Derive 'b_term_parsed' (B).

        -- To derive B, we use RAA: assume ¬B ('not_b_to_assume') and derive a contradiction.
        let not_b_to_assume = neg b_term_parsed
        (not_b_implies_false,_) <- runProofByAsmM not_b_to_assume $ do
            -- Current assumptions:
            --   'a_term_parsed' (A) - from parent subproof scope
            --   'not_b_to_assume' (¬B) - current subproof assumption
            --   's_notA_or_B_proven' (¬A ∨ B) - from outermost scope

            -- We need to show that these three together lead to False.
            -- We'll use Disjunction Elimination on 's_notA_or_B_proven' (¬A ∨ B).
            -- Case 1: Assume ¬A (which is 'not_a_term_parsed')
            (case1_notA_implies_false, _) <- runProofByAsmM not_a_term_parsed $ do
                -- We have 'a_term_parsed' (A) and 'not_a_term_parsed' (¬A). Contradiction.
                contraFM a_term_parsed -- Derives False
                return ()

            -- Case 2: Assume B (which is 'b_term_parsed')
            (case2_B_implies_false, _) <- runProofByAsmM b_term_parsed $ do
                -- We have 'b_term_parsed' (B) and 'not_b_to_assume' (¬B). Contradiction.
                contraFM b_term_parsed-- Derives False
                return ()

            -- Apply DisjElim: from (¬A ∨ B), (¬A → False), (B → False), conclude False.
            falsity_derived <- disjElimM s_notA_or_B_proven case1_notA_implies_false case2_B_implies_false
            return () -- Innermost subproof (Assume ¬B) concludes False.

        -- We have now proven (¬B → False).
        not_not_b_derived <- absurdM not_b_implies_false -- Derives ¬¬B

        -- Use Double Negation Elimination to get B from ¬¬B.
        b_final_derived <- doubleNegElimM not_not_b_derived
        
        -- The middle subproof (which assumed A) now has B ('b_final_derived') as its last proven statement.
        return ()

    -- The outermost 'runProofByAsmM a_term_parsed ...' will construct and prove:
    --   a_term_parsed → b_final_derived
    -- which is A → B.
    return resSent




-- Helper to transform a proven Neg(A && Neg B) into a proven (Neg A || B)
-- Uses DeMorgan, Double Negation Elimination, and Proof by Cases (DisjElim).
negAndNotToOrM :: HelperConstraints r1 s o tType sE eL q t m
               => s -- ^ The proven proposition of the form Neg (a :&&: Neg b)
               -> ProofGenTStd tType r1 s o q t m s -- Returns (Neg a :||: b, its_index)
negAndNotToOrM provenNegAAndNotB = do
    -- 1. Parse the input to get the terms A and B.
    innerConjunction <- maybe (throwM $ MetaRuleErrNotNeg provenNegAAndNotB)
                              return (parseNeg provenNegAAndNotB)
    (a_term, not_b_term) <- maybe (throwM $ MetaRuleErrNotAdj innerConjunction)
                                 return (parseAdj innerConjunction)
    b_term <- maybe (throwM $ MetaRuleErrNotNeg not_b_term)
                    return (parseNeg not_b_term)

    -- The target proposition we want to prove is (Neg a_term :||: b_term)
    let target_disjunction = neg a_term .||. b_term

    -- 2. Apply De Morgan's Law to provenNegAAndNotB.
    --    Input: Neg (A && Neg B)
    --    Output (s_or_form_proven): (Neg A) || (Neg (Neg B))
    s_or_form_proven <- deMorganConjM provenNegAAndNotB
    -- s_or_form_proven has the structure: (neg a_term) :||: (neg not_b_term)
    -- which is equivalent to (neg a_term) :||: (neg (neg b_term))

    -- For Disjunction Elimination, we need two implications:
    --   I1: (Neg A) -> (Neg A || B)
    --   I2: (Neg (Neg B)) -> (Neg A || B)

    -- 3. Prove I1: (Neg A) -> (Neg A || B)
    (neg_a_implies_target,_) <- runProofByAsmM (neg a_term) $ do
        -- Assume (Neg A) - this is 'neg a_term', which is proven by assumption here.
        -- We want to derive 'target_disjunction' which is (Neg A || B).
        disjIntroLM (neg a_term) b_term -- Uses the assumed (Neg A) and term B
        return () -- Subproof concludes with (Neg A || B)

    -- 4. Prove I2: (Neg (Neg B)) -> (Neg A || B)
    let not_not_b_assumption_term = neg not_b_term -- This is term Neg(Neg B)
    (not_not_b_implies_target, _) <- runProofByAsmM not_not_b_assumption_term $ do
        -- Assume (Neg (Neg B)) - this is 'not_not_b_assumption_term', proven by assumption.
        -- First, derive B using Double Negation Elimination.
        b_proven_from_dne <- doubleNegElimM not_not_b_assumption_term

        -- Now we have B (b_proven_from_dne). We want to derive (Neg A || B).
        disjIntroRM (neg a_term) b_proven_from_dne -- Uses term (Neg A) and proven B
        return () -- Subproof concludes with (Neg A || B)

    -- 5. Apply Disjunction Elimination.
    --    We have:
    --      s_or_form_proven:         (Neg A) || (Neg (Neg B))
    --      neg_a_implies_target:     (Neg A) -> (Neg A || B)
    --      not_not_b_implies_target: (Neg (Neg B)) -> (Neg A || B)
    --    The result will be (Neg A || B).
    disjElimM s_or_form_proven neg_a_implies_target not_not_b_implies_target




-- Ensure all necessary imports are present, including:
-- MetaRuleErrNotImp, MetaRuleErrNotNeg, MetaRuleErrNotAdj (or similar)
-- parse_implication, parseNeg, parseAdj, neg, (.&&.), (.->.), (.||.)
-- runProofByAsmM, contraFM, absurdM, doubleNegElimM,
-- negAndNotToOrM, disj2ImpM (the helpers we discussed)
-- And all necessary type classes and ProofGenTStd etc.

-- | Derives (A ∧ ¬B) from a proven ¬(A → B).
-- | This demonstrates one direction of the equivalence ¬(A → B) ⇔ (A ∧ ¬B).
-- | It uses previously defined helpers 'negAndNotToOrM' and 'disj2ImpM'
-- | within a proof by contradiction structure.
-- |
-- | Proof Strategy:
-- | 1. Given ¬(A → B) as 's_input'.
-- | 2. To prove (A ∧ ¬B), assume its negation ¬(A ∧ ¬B) for Reductio Ad Absurdum (RAA).
-- |    a. From the assumption ¬(A ∧ ¬B), use 'negAndNotToOrM' to derive (¬A ∨ B).
-- |    b. From (¬A ∨ B), use 'disj2ImpM' to derive (A → B).
-- |    c. Now we have derived (A → B) (from step 2b) and we were given ¬(A → B) ('s_input').
-- |       This is a contradiction, so derive False using `contraFM`.
-- | 3. The subproof (assuming ¬(A ∧ ¬B)) has led to False.
-- |    Thus, by RAA (via `absurdM`), we conclude ¬(¬(A ∧ ¬B)).
-- | 4. Apply Double Negation Elimination (`doubleNegElimM`) to get (A ∧ ¬B).
negImpToConjViaEquivM :: (HelperConstraints r1 s o tType sE eL q t m) =>
            s -- ^ A proven proposition 's_input' of the form ¬(A → B).
            -> ProofGenTStd tType r1 s o q t m s -- ^ Returns the proven proposition (A ∧ ¬B) and its proof index.
negImpToConjViaEquivM s_input_neg_A_implies_B = do
    -- 1. Parse the input s_input_neg_A_implies_B = ¬(A → B) to get terms A and B.
    --    These terms are needed to construct the assumption for RAA: ¬(A ∧ ¬B).
    a_implies_b_term <- maybe (throwM $ MetaRuleErrNotNeg s_input_neg_A_implies_B)
                              return (parseNeg s_input_neg_A_implies_B)
    (a_term, b_term) <- maybe (throwM $ MetaRuleErrNotImp a_implies_b_term)
                              return (parse_implication a_implies_b_term)

    -- 2. Construct the assumption for RAA: ¬(A ∧ ¬B)
    let assumption_for_raa = neg (a_term .&&. neg b_term)

    x <- showSentM assumption_for_raa

    remarkM x

    -- 3. Start the RAA subproof: Assume ¬(A ∧ ¬B) and derive False.
    --    This will prove (¬(A ∧ ¬B) → False).
    (raa_antecedent_implies_false, _) <- runProofByAsmM assumption_for_raa $ do
        -- Inside this subproof, 'assumption_for_raa' (¬(A ∧ ¬B)) is proven by assumption.

        -- 3a. From ¬(A ∧ ¬B), derive (¬A ∨ B) using 'negAndNotToOrM'.
        not_a_or_b_derived <- negAndNotToOrM assumption_for_raa

        -- 3b. From (¬A ∨ B), derive (A → B) using 'disj2ImpM'.
        a_implies_b_derived <- disj2ImpM not_a_or_b_derived

        -- 3c. We have 'a_implies_b_derived' (A → B) and the original 's_input_neg_A_implies_B' (¬(A → B)).
        --     This is a contradiction. Derive False using `contraFM`.
        falsity <- contraFM a_implies_b_derived
        
        -- The subproof (assuming ¬(A ∧ ¬B)) concludes with 'falsity' (False).
        return ()

    -- 4. Apply AbsurdM to (¬(A ∧ ¬B) → False) to get ¬(¬(A ∧ ¬B)).
    double_negated_target <- absurdM raa_antecedent_implies_false

    -- 5. Apply Double Negation Elimination to ¬(¬(A ∧ ¬B)) to get (A ∧ ¬B).
    doubleNegElimM double_negated_target




modusTollensM :: (HelperConstraints r1 s o tType sE eL q t m)
    => s
    -> -- ProofGeneratorT s [PrfStdStep s o tType] (PrfStdContext tType) r1 (PrfStdState s o tType) m (s, [Int])
       ProofGenTStd tType r1 s o q t m s
modusTollensM s = do
    -- Parse (P → Q) and ¬Q from the input statement s
    (p,q) <- maybe (throwM $ MetaRuleErrNotModusTollens s) return (parse_implication s)
    let negQ = neg q


    repM s -- We are assuming P → Q is already proven in the context and we reiterate it for emphasis.
    -- Derive ¬P from ¬Q and P → Q (Modus Tollens)
    repM negQ -- We are assuming ¬Q is already proven in the context and we reiterate it for emphasis.
    (negPImpNegQ,_) <- runProofByAsmM negQ $ do

        (absurdity,_) <- runProofByAsmM p $ do
                q <- mpM s
                -- Use contraFM to derive False from q and negQ    
                contraFM q
                --False now derived
        absurdM absurdity
        -- proves ¬P
    mpM negPImpNegQ
    -- this will prove neg p

doubleNegIntroM :: (HelperConstraints r1 s o tType sE eL q t m) 
    => s  -- The sentence P, which must be already proven
    -> ProofGenTStd tType r1 s o q t m s -- Returns the proven ¬¬P and its index
doubleNegIntroM p = do
    -- Prove ¬P → ⊥ by assuming ¬P and deriving a contradiction with P
    (negP_imp_False, _) <- runProofByAsmM (neg p) $ do
        -- Inside this subproof, (neg p) is assumed.
        -- contraFM uses 'p' (proven outside) and 'neg p' (the assumption).
        contraFM p -- Derive False (⊥)

    -- Use the Absurd rule: (¬P → ⊥) ⊢ ¬¬P
    negNegP <- absurdM negP_imp_False
    return negNegP


-- | Proves an arbitrary proposition from a contradiction (Ex Falso Quodlibet).
-- | Theorem: False ⊢ P
-- |
-- | This helper function implements the principle of explosion. It takes a target
-- | proposition 'p' to be proven. It requires that the proposition 'false' has
-- | already been proven in the current proof context.
-- |
-- | The proof strategy is a standard Reductio Ad Absurdum (RAA):
-- | 1. Assume ¬P (the negation of the target).
-- | 2. Reiterate the proven 'false' into this subproof using 'repM false'.
-- | 3. The subproof concludes, having proven ¬P → False.
-- | 4. Apply 'absurdM' to get ¬¬P.
-- | 5. Apply 'doubleNegElimM' to get P.
exFalsoM :: HelperConstraints r1 s o tType sE eL q t m =>
    s -> -- ^ s_target: The arbitrary proposition 'p' to be proven.
    ProofGenTStd tType r1 s o q t m s
exFalsoM s_target = do
    (s_target_proven,_) <- runProofBySubArgM $ do
        -- Step 1: Start a subproof assuming the negation of our target.
        -- This will prove (¬P → False).
        (not_p_implies_false, _) <- runProofByAsmM (neg s_target) $ do
            -- Inside this subproof, ¬P is an assumption.
            -- We assume 'false' is proven in the outer context and reiterate it.
            repM false
            return () -- The subproof concludes 'false'.

        -- Step 2: From (¬P → False), derive ¬¬P using the absurd rule (RAA).
        not_not_p <- absurdM not_p_implies_false

        -- Step 3: From ¬¬P, derive P using Double Negation Elimination.
        doubleNegElimM not_not_p
        return ()
    return s_target_proven



 
-- | Takes P ∨ Q as an argument.
-- | For this function to succeed, the following must be already proven
-- | in the current context:
-- | 1. P ∨ Q
-- | 2. ¬Q
-- | If the required sentences are already proven then P will be derived.
-- | This is a fundamental tautology of classical logic.
disjunctiveSyllogismM :: (HelperConstraints r1 s o tType sE eL q t m) =>
    s -> -- ^ The proposition P ∨ Q
    ProofGenTStd tType r1 s o q t m s
disjunctiveSyllogismM pOrQ = do
    (p,q) <- maybe (throwM $ MetaRuleErrDisjSyllNotDisj pOrQ) return (parseDisj pOrQ)
    let negQ = neg q
    (result_sent, _) <- runProofBySubArgM $ do
        repM pOrQ -- Re-assert P ∨ Q to emphasize that it should already be proven
        repM negQ -- Re-Assert ¬Q to emphasize that it should already be proven.
        -- Prove the goal P by using Disjunction Elimination (Proof by Cases) on P ∨ Q.
            
        -- Case 1: Assume P. The goal is to derive P.
        (p_implies_p, _) <- runProofByAsmM p $ do
            -- We assumed P, so we can reiterate it as the conclusion of this subproof.
            repM p
            return ()

        -- Case 2: Assume Q. The goal is to derive P.
        (q_implies_p, _) <- runProofByAsmM q $ do
            -- We assumed Q, but we also have ¬Q from the parent assumption.
            -- This is a contradiction.
            falsity <- contraFM q
                
            -- From the proven 'falsity', derive the target 'p' using Ex Falso Quodlibet.
            exFalsoM p
            return ()

        -- Apply Disjunction Elimination.
        -- We have proven:
        --   1. P ∨ Q
        --   2. P → P
        --   3. Q → P
        -- Therefore, we can conclude P.
        disjElimM pOrQ p_implies_p q_implies_p
        return ()
    return result_sent






-- | From P ↔ Q, derive ¬P ↔ ¬Q 
posBicondToNegBicondM :: (HelperConstraints r1 s o tType sE eL q t m) =>
    s -> -- ^ The proposition P ↔ Q
    ProofGenTStd tType r1 s o q t m s
posBicondToNegBicondM s = do
    -- The goal is to prove the proposition (¬P ↔ ¬Q).
    -- We prove this by assuming the antecedent and deriving the consequent.
    (p,q) <- maybe (throwM $ MetaRuleErrNotBicond s) return (parseIff s)
    let negP = neg p
    let negQ = neg q

    repM s -- We are assuming P ↔ Q is already proven in the context and we reiterate it for emphasis.
    
    (target,_) <- runProofBySubArgM $ do
        (notP_implies_notQ, _) <- runProofByAsmM negP $ do
            -- Assume ¬P.
            -- From P ↔ Q, we can derive Q → P.
            q_implies_p <- bicondElimRM s
            
            -- We have the implication Q → P and the premise ¬P.
            -- This is a direct application of Modus Tollens.
            -- modusTollensM takes Q → P and uses the proven assumption ¬P`
            -- to derive ¬Q.

            modusTollensM q_implies_p
            -- Now eliminate the double negation to get ¬Q.
            
            -- The subproof concludes ¬Q.

        -- Part B: Prove Q → P (symmetric proof)
        (notQ_implies_notP, _) <- runProofByAsmM negQ $ do
            -- Assume ¬Q.
            -- From P ↔ Q, we can derive P → Q.
            p_implies_q <- bicondElimLM s
            
            -- Apply Modus Tollens to P → Q. It uses the proven assumption ¬Q
            -- to derive ¬P.
            modusTollensM p_implies_q


            -- The subproof concludes P.
        -- Combine the two implications into the biconditional P ↔ Q.
        bicondIntroM notP_implies_notQ notQ_implies_notP
        return ()
    return target



-- | From ¬P ↔ ¬Q, derive P ↔ Q.
negBicondToPosBicondM :: (HelperConstraints r1 s o tType sE eL q t m) =>
    s -> -- ^ The proposition ¬P ↔ ¬Q
    ProofGenTStd tType r1 s o q t m s
negBicondToPosBicondM s = do
    -- The goal is to derive the proposition P ↔ Q.
    -- We prove this by assuming the antecedent and deriving the consequent.
    (negP,negQ) <- maybe (throwM $ MetaRuleErrNotNegBicond s) return (parseIff s)
    p <- maybe (throwM $ MetaRuleErrNotNegBicond s) return (parseNeg negP)
    q <- maybe (throwM $ MetaRuleErrNotNegBicond s) return (parseNeg negQ)
    let negBicond = neg p .<->. neg q
    
    (target,_) <- runProofBySubArgM $ do
        posBicondPre <- posBicondToNegBicondM negBicond
        negNegP_imp_negNegQ <- bicondElimLM posBicondPre
        (p_implies_q, _) <- runProofByAsmM p $ do
            -- Assume P.

            negNegP <- doubleNegIntroM p --prove ¬(¬P).
            negNegQderived <- mpM negNegP_imp_negNegQ 
            -- Now eliminate the double negation to get Q.
            doubleNegElimM negNegQderived

            -- The subproof concludes Q.

        -- Part B: Prove Q → P (symmetric proof)
        (negNegQ_imp_negNegP) <- bicondElimRM posBicondPre
        (q_implies_p,_) <- runProofByAsmM q $ do
            -- Assume Q.
            negNegQ <- doubleNegIntroM q --prove ¬(¬Q).
            negNegPderived<- mpM negNegQ_imp_negNegP
            -- Now eliminate the double negation to get P.
            doubleNegElimM negNegPderived

            -- The subproof concludes P.
        -- Combine the two implications into the biconditional P ↔ Q.
        bicondIntroM p_implies_q q_implies_p
        return ()
    return target


-- | From P ∧ Q, derive both P and Q.
deconstructAdjM :: (HelperConstraints r1 s o tType sE eL q t m) =>
    s -> -- ^ The proposition ¬P ↔ ¬Q
    ProofGenTStd tType r1 s o q t m (s, s)
deconstructAdjM s = do
    adjunct1_data <- simpLM s
    adjunct2_data <- simpRM s
    return (adjunct1_data, adjunct2_data)

-- | From a nested conjunction P₁ ∧ P₂ ∧ ... ∧ Pₙ, and an integer `k`,
-- | this function performs `k` splits and returns a list of proofs for all
-- | `k+1` resulting propositions: [P₁, P₂, ..., Pₖ₊₁].
-- |
-- | For example, given a proof of `A ∧ (B ∧ C)` and `k=1`, it will return a
-- | list containing proofs for `A` and `B ∧ C`. Given `k=2`, it will return
-- | proofs for `A`, `B`, and `C`.
-- |
-- | Note: This helper assumes the input proposition `s` is already proven in the context.
-- | It also assumes the conjunctions are right-associative, e.g., P₁ ∧ (P₂ ∧ P₃).
deconstructMultiAdjM :: (HelperConstraints r1 s o tType sE eL q t m) =>
    s -> -- ^ The nested conjunction P₁ ∧ P₂ ∧ ...
    Int -> -- ^ The number of conjunctions ('∧') to parse/split.
    ProofGenTStd tType r1 s o q t m [s]
deconstructMultiAdjM s num_splits = do
    when (num_splits < 0) $
        throwM (MetaRuleErrDeconstructMultiAdjMNonNegSplits num_splits)
    if num_splits == 0 then
        do 
           (: []) <$> repM s
      else
          peelOff num_splits s




-- A recursive helper to perform `k` splits.
-- Returns a list of all resulting proven propositions.
peelOff :: (HelperConstraints r1 s o tType sE eL q t m) =>
    Int -> s -> ProofGenTStd tType r1 s o q t m [s]
peelOff 0 current_s = do
    -- Base case: we've performed enough splits. The remainder is the last element.
    final_proof <- repM current_s
    return [final_proof]
peelOff k current_s = do
    -- Recursive step: split the current proposition into its left and right parts.
    -- This will fail if `current_s` is not a conjunction, which is the desired behavior
    -- if `k` is greater than the number of conjunctions in the proposition.
    (left_proof, right_prop) <- deconstructAdjM current_s
    
    -- Recursively peel off the remaining `k-1` conjuncts from the right side.
    remaining_proofs <- peelOff (k - 1) right_prop

    -- Prepend the current left-hand proof to the list and return.
    return (left_proof : remaining_proofs)


runProofByAsmM :: HelperConstraints r1 s o tType sE eL1 q t m
                 =>   s -> ProofGenTStd tType r1 s o q t m x
                            -> ProofGenTStd tType r1 s o q t m (s,x )
runProofByAsmM asm prog =  do
        state <- getProofState
        context <- ask
        let frVarTypeStack = freeVarTypeStack context
        let constdict = fmap fst (consts state)
        let sc = checkSanity mempty frVarTypeStack constdict asm
        maybe (return ()) (throwM . BigExceptAsmSanity asm) sc
        let newStepIdxPrefix = stepIdxPrefix context ++ [stepCount state]
        let newSents = Data.Map.insert asm (newStepIdxPrefix ++ [0]) mempty
        let newContextFrames = contextFrames context <> [False]
        let newContext = PrfStdContext frVarTypeStack newStepIdxPrefix newContextFrames (Just state)
        let newState = PrfStdState {
            provenSents = newSents,
            consts = mempty,
            stepCount = 1,
            tagData = mempty,
            remarkTagIdxs = mempty
        }
        let preambleSteps = [PrfStdStepStep asm "ASM" Nothing []]
        let mayPreambleLastProp = (Last . Just) asm
        vIdx <- get
        (extraData,consequent,subproof,newSteps) 
                 <- lift $ runSubproofM newContext state newState preambleSteps mayPreambleLastProp prog vIdx
        mayMonadifyRes <- monadifyProofStd $ proofByAsm asm consequent subproof
        maybe (error "No theorem returned by monadifyProofStd on asm schema. This shouldn't happen") return mayMonadifyRes
        return (asm .->. consequent,extraData)





