{-# LANGUAGE TupleSections #-}
module RuleSets.ZFC 
(
    LogicError(..), LogicRule(..), 
    runProofAtomic, 
    LogicRuleClass(..),
    LogicSent(..),
    LogicTerm(..),
    specificationM,
    replacementM,
    integerMembershipM,
    integerNegationM,
    integerAdditionM,
    integerMultiplicationM,
    integerCompareM,
    integersAreUrelementsM,
    integerInequalityM,
    emptySetAxiomM,
    extensionalityAxiomM,
    emptySetNotIntM,
    regularityAxiomM,
    unionAxiomM,
    powerSetAxiomM,
    pairingAxiomM,
    axiomOfChoiceM,
    intOrderAntiSymmetryM,
    intOrderReflexivityM,
    intOrderTransitivityM,
    intOrderTotalityM,
    intAddClosureAxiomM,
    intMulClosureAxiomM,
    intNegClosureAxiomM,
    intAddAssociativityM,
    intAddCommutativityAxiomM,
    intAddIdentityAxiomM,
    intAddInverseAxiomM,
    intMulAssociativityAxiomM,
    intMulCommutativityAxiomM,
    intMulIdentityAxiomM,
    intDistributivityAxiomM,
    intOrderAddCompatibilityAxiomM,
    intOrderMulCompatibilityAxiomM,
    natWellOrderingAxiomM,
    MetaRuleError(..)
) where


import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless,when )
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
import Data.Maybe ( isNothing )

import Kernel
import Internal.StdPattern

import RuleSets.BaseLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic)
import qualified RuleSets.BaseLogic.Core as REM

import RuleSets.PropLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   LogicSent,
   SubproofMException(..),
   MetaRuleError(..))
import qualified RuleSets.PropLogic.Core as PL

import RuleSets.PredLogic.Core hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic,
   LogicSent,
   SubproofMException(..),
   MetaRuleError(..))
import qualified RuleSets.PredLogic.Core as PREDL
import GHC.Num (integerMul)







class LogicTerm t where
   integer :: Int -> t
   --parseTuple :: t -> Maybe [t]
   --buildTuple :: [t] -> t
   buildProject :: Int -> t -> t
   (.+.) :: t -> t -> t
   (.*.) :: t -> t -> t
   intNeg :: t -> t
   intSet :: t


class (PREDL.LogicSent s t () Text) => LogicSent s t | s ->t where
   specAxiom :: [Int] -> Int -> t -> s -> s
   replaceAxiom :: [Int] -> Int -> Int -> t -> s -> s
   parseMemberOf :: s -> Maybe (t, t)
   memberOf :: t -> t -> s
   intsAreUrelementsAxiom :: s   
   (.<=.) :: t -> t -> s
   emptySetAxiom :: s
   extensionalityAxiom :: s
   emptySetNotIntAxiom :: s
   regularityAxiom :: s
   unionAxiom :: s
   powerSetAxiom :: s
   pairingAxiom :: s
   axiomOfChoice :: s

   -- Integer order axioms
   intOrderAntisymmetryAxiom :: s
   intOrderReflexivityAxiom :: s
   intOrderTransitivityAxiom :: s
   intOrderTotalityAxiom :: s

   -- Integer closure axioms
   intAddClosureAxiom :: s
   intMulClosureAxiom :: s
   intNegClosureAxiom :: s

   -- Integer ring axioms
   intAddAssociativityAxiom :: s
   intAddCommutativityAxiom :: s
   intAddIdentityAxiom :: s
   intAddInverseAxiom :: s
   intMulAssociativityAxiom :: s
   intMulCommutativityAxiom :: s
   intMulIdentityAxiom :: s
   intDistributivityAxiom :: s
   intOrderAddCompatibilityAxiom :: s
   intOrderMulCompatibilityAxiom :: s

   -- Well ordering axiom
   natWellOrderingAxiom :: s

   




data LogicError s sE t where
    LogicErrPrfByAsm :: PL.SubproofError s sE (LogicError s sE t) -> LogicError s sE t
    LogicErrPrfBySubArg :: REM.SubproofError s sE (LogicError s sE t) -> LogicError s sE t
    LogicErrUG :: PREDL.SubproofError s sE  (LogicError s sE t) -> LogicError s sE t
    LogicErrTheorem :: PREDL.ChkTheoremError s sE (LogicError s sE t) Text () -> LogicError s sE t 
    LogicErrTheoremM :: SomeException -> LogicError s sE t 
    LogicErrPredL ::  PREDL.LogicError s sE Text t () -> LogicError s sE t

    LogicErrReplTermNotClosedSane :: t -> sE -> LogicError s sE t
    LogicErrSpecTermNotClosedSane :: t -> sE -> LogicError s sE t
    LogicErrSpecTmpltNotSane :: s -> sE -> LogicError s sE t
    LogicErrReplTmpltNotSane :: s -> sE -> LogicError s sE t
    LogicErrPairNotSane :: t -> Int -> LogicError s sE t
    LogicErrNotAPair :: t -> LogicError s sE t
    LogicErrIndexOutOfBounds :: Int -> Int -> t -> LogicError s sE t -- Holds index, length, tuple
    LogicErrSpecOuterIndexConflict :: Int -> [Int] -> LogicError s sE t
    LogicErrReplOuterIndexDuplicate :: Int -> [Int] -> LogicError s sE t
    LogicErrSpecOuterIndexDuplicate :: Int -> [Int] -> LogicError s sE t
    LogicErrReplIndexConflict :: Int -> Int -> [Int] -> LogicError s sE t -- For idx1 == idx2 OR idx1/idx2 in outerIdxs
    LogicErrIntCompareFalse :: Int -> Int -> LogicError s sE t
    LogicErrIntInequalitySameValues :: Int -> Int -> LogicError s sE t
   deriving (Show)

data LogicRule s sE t  where
   -- t is a term
    PredRule :: PREDL.LogicRule s sE Text t () -> LogicRule s sE t 
    ProofByAsm :: ProofByAsmSchema s [LogicRule s sE t] -> LogicRule s sE t 
    ProofBySubArg :: ProofBySubArgSchema s [LogicRule s sE t] -> LogicRule s sE t
    ProofByUG :: ProofByUGSchema s [LogicRule s sE t] -> LogicRule s sE t 
    Theorem :: TheoremSchema s [LogicRule s sE t ] Text () -> LogicRule s sE t 
    TheoremM :: TheoremAlgSchema () [LogicRule s sE t ] s Text () -> 
                             LogicRule s sE t
    --EmptySet :: LogicRule s sE t
    Specification :: [Int] -> Int -> t -> s -> LogicRule s sE t
    Replacement :: [Int] -> Int -> Int -> t -> s -> LogicRule s sE t
    IntegerMembership    :: Int -> LogicRule s sE t
    IntegerAddition      :: Int -> Int -> LogicRule s sE t
    IntegerMultiplication:: Int -> Int -> LogicRule s sE t
    IntegerNegation      :: Int -> LogicRule s sE t
    IntegerCompare :: Int -> Int -> LogicRule s sE t
    IntegersAreUrelements :: LogicRule s sE t
    IntegerInequality    :: Int -> Int -> LogicRule s sE t
    EmptySetAxiom        :: LogicRule s sE t
    ExtensionalityAxiom  :: LogicRule s sE t
    EmptySetNotIntAxiom  :: LogicRule s sE t
    RegularityAxiom      :: LogicRule s sE t
    UnionAxiom :: LogicRule s sE t
    PowerSetAxiom :: LogicRule s sE t
    PairingAxiom :: LogicRule s sE t
    AxiomOfChoice :: LogicRule s sE t
    IntOrderAntisymmetry :: LogicRule s sE t
    IntOrderReflexivity :: LogicRule s sE t
    IntOrderTransitivity :: LogicRule s sE t
    IntOrderTotality :: LogicRule s sE t

    IntAddClosure        :: LogicRule s sE t
    IntMulClosure        :: LogicRule s sE t
    IntNegClosure        :: LogicRule s sE t
    IntAddAssociativity  :: LogicRule s sE t
    IntAddCommutativity  :: LogicRule s sE t
    IntAddIdentity       :: LogicRule s sE t
    IntAddInverse        :: LogicRule s sE t
    IntMulAssociativity  :: LogicRule s sE t
    IntMulCommutativity  :: LogicRule s sE t
    IntMulIdentity       :: LogicRule s sE t
    IntDistributivity    :: LogicRule s sE t
    IntOrderAddCompatibility :: LogicRule s sE t
    IntOrderMulCompatibility :: LogicRule s sE t

    -- Well-ordering of N axiom
    NatWellOrderingAxiom :: LogicRule s sE t
    deriving(Show)


instance REM.LogicRuleClass [LogicRule s sE t] s Text () sE where
     remark:: Text -> [LogicRule s sE t]
     remark rem = [(PredRule . PREDL.PropRule . PL.BaseRule . REM.Remark) rem]
     rep :: s -> [LogicRule s sE t ]
     rep s = [(PredRule . PREDL.PropRule . PL.BaseRule . REM.Rep) s]
     fakeProp:: [s] -> s -> [LogicRule s o t ]
     fakeProp deps s = [(PredRule . PREDL.PropRule . PL.BaseRule . REM.FakeProp deps) s]
     fakeConst:: Text -> () -> [LogicRule s sE t ]
     fakeConst o t = [PredRule $ PREDL.PropRule $ PL.BaseRule $ REM.FakeConst o t]


instance PL.LogicRuleClass [LogicRule s sE t] s () sE Text where
     mp:: s -> [LogicRule s sE t]
     mp a = [(PredRule . PREDL.PropRule . PL.MP) a]     
     exclMid:: s -> [LogicRule s sE t]
     exclMid a = [(PredRule . PREDL.PropRule . PL.ExclMid) a]
     simpL:: s -> [LogicRule s sE t]
     simpL a = [(PredRule . PREDL.PropRule . PL.SimpL) a]
     simpR :: s -> [LogicRule s sE t]
     simpR a = [(PredRule . PREDL.PropRule . PL.SimpR) a]

     adj:: s -> s -> [LogicRule s sE t]
     adj a b = [PredRule $ PREDL.PropRule $ PL.Adj a b]
     contraF :: s -> [LogicRule s sE t]
     contraF a = [PredRule $ PREDL.PropRule $ PL.ContraF a]
     absurd:: s -> [LogicRule s sE t]
     absurd a = [(PredRule . PREDL.PropRule . PL.Absurd) a]    
     disjIntroL :: s -> s -> [LogicRule s sE t]
     disjIntroL a b = [PredRule $ PREDL.PropRule $ PL.DisjIntroL a b]
    
     disjIntroR :: s -> s -> [LogicRule s sE t]
     disjIntroR a b = [PredRule $ PREDL.PropRule $ PL.DisjIntroR a b]
    
     disjElim :: s -> s -> s -> [LogicRule s sE t]
     disjElim a b c = [PredRule $ PREDL.PropRule $ PL.DisjElim a b c]
    
     doubleNegElim :: s -> [LogicRule s sE t]
     doubleNegElim a = [(PredRule . PREDL.PropRule . PL.DoubleNegElim) a]
    
     deMorganConj :: s -> [LogicRule s sE t]
     deMorganConj a = [(PredRule . PREDL.PropRule . PL.DeMorganConj) a]
    
     deMorganDisj :: s -> [LogicRule s sE t]
     deMorganDisj a = [(PredRule . PREDL.PropRule . PL.DeMorganDisj) a]
    
     bicondIntro :: s -> s -> [LogicRule s sE t]
     bicondIntro a b = [PredRule $ PREDL.PropRule $ PL.BicondIntro a b]
    
     bicondElimL :: s -> [LogicRule s sE t]
     bicondElimL a = [(PredRule . PREDL.PropRule . PL.BicondElimL) a]
    
     bicondElimR :: s -> [LogicRule s sE t]
     bicondElimR a = [(PredRule . PREDL.PropRule . PL.BicondElimR) a]
    
     absorpAnd :: s -> [LogicRule s sE t]
     absorpAnd a = [(PredRule . PREDL.PropRule . PL.AbsorpAnd) a]
    
     absorpOr :: s -> [LogicRule s sE t]
     absorpOr a = [(PredRule . PREDL.PropRule . PL.AbsorpOr) a]
    
     distAndOverOr :: s -> [LogicRule s sE t]
     distAndOverOr a = [(PredRule . PREDL.PropRule . PL.DistAndOverOr) a]
    
     distOrOverAnd :: s -> [LogicRule s sE t]
     distOrOverAnd a = [(PredRule . PREDL.PropRule . PL.DistOrOverAnd) a]
    
     peircesLaw :: s -> [LogicRule s sE t]
     peircesLaw p = [(PredRule . PREDL.PropRule . PL.PeircesLaw) p]

 






instance PREDL.LogicRuleClass [LogicRule s sE t] s t () sE Text where
     ei:: s -> Text -> [LogicRule s sE t ]
     ei s o = [PredRule $ PREDL.EI s o]
     eiHilbert:: s -> [LogicRule s sE t ]
     eiHilbert s = [(PredRule . PREDL.EIHilbert) s]
     
     eg:: t -> s -> [LogicRule s sE t ]
     eg t s = [PredRule $ PREDL.EG t s]
     ui:: t -> s -> [LogicRule s sE t]
     ui t s = [PredRule $ PREDL.UI t s]
     eNegIntro:: s -> [LogicRule s sE t]
     eNegIntro s = [(PredRule . PREDL.ENegIntro) s]
     aNegIntro:: s -> [LogicRule s sE t]
     aNegIntro s = [(PredRule . PREDL.ANegIntro) s]
     eqRefl :: t -> [LogicRule s sE t]
     eqRefl t = [PredRule $ PREDL.EqRefl t]

     eqSym :: s -> [LogicRule s sE t]
     eqSym s = [PredRule $ PREDL.EqSym s]

     eqTrans :: s -> s -> [LogicRule s sE t]
     eqTrans s1 s2 = [PredRule $ PREDL.EqTrans s1 s2]

     eqSubst :: Int -> s -> s -> [LogicRule s sE t]
     eqSubst idx templateSent eqSent = [PredRule $ PREDL.EqSubst idx templateSent eqSent]

class LogicRuleClass r s sE t | r->s, r->sE, r->t where
     specification :: [Int] -> Int -> t -> s -> r
     replacement :: [Int] -> Int -> Int -> t -> s -> r
     integerMembership    :: Int -> r
     integerAddition      :: Int -> Int -> r
     integerMultiplication:: Int -> Int -> r
     integerNegation      :: Int -> r
     integerCompare :: Int -> Int -> r
     integersAreUrelements :: r
     integerInequality    :: Int -> Int -> r
     emptySet             :: r
     extensionality       :: r
     emptySetNotInt       :: r
     regularity :: r
     union :: r
     powerSet :: r
     pairing :: r
     choice :: r
     intOrderAntiSymmetry :: r
     intOrderReflexivity :: r
     intOrderTransitivity:: r
     intOrderTotality:: r
     intAddClosure        :: r
     intMulClosure        :: r
     intNegClosure        :: r
     intAddAssociativity  :: r
     intAddCommutativity  :: r
     intAddIdentity       :: r
     intAddInverse        :: r
     intMulAssociativity  :: r
     intMulCommutativity  :: r
     intMulIdentity       :: r
     intDistributivity    :: r
     intOrderAddCompatibility :: r
     intOrderMulCompatibility :: r
     natWellOrdering :: r


instance LogicRuleClass [LogicRule s sE t] s sE t where
     specification :: [Int] -> Int -> t -> s -> [LogicRule s sE t]
     specification outerIdxs idx t s = [Specification outerIdxs idx t s]
     replacement :: [Int] -> Int -> Int -> t ->  s -> [LogicRule s sE t]
     replacement outerIdxs idx1 idx2 t s = [Replacement outerIdxs idx1 idx2 t s]
     integerMembership    :: Int -> [LogicRule s sE t]
     integerMembership i = [IntegerMembership i]
     integerAddition      :: Int -> Int -> [LogicRule s sE t]
     integerAddition i1 i2 = [IntegerAddition i1 i2]
     integerMultiplication:: Int -> Int -> [LogicRule s sE t]
     integerMultiplication i1 i2 = [IntegerMultiplication i1 i2]
     integerNegation      :: Int -> [LogicRule s sE t]
     integerNegation i = [IntegerNegation i]
     integerCompare :: Int -> Int -> [LogicRule s sE t]
     integerCompare i1 i2 = [IntegerCompare i1 i2]
     integersAreUrelements :: [LogicRule s sE t]
     integersAreUrelements = [IntegersAreUrelements]
     integerInequality    :: Int -> Int -> [LogicRule s sE t]
     integerInequality i1 i2 = [IntegerInequality i1 i2]
     emptySet :: [LogicRule s sE t]
     emptySet = [EmptySetAxiom]
     extensionality :: [LogicRule s sE t]
     extensionality       = [ExtensionalityAxiom]
     emptySetNotInt :: [LogicRule s sE t]
     emptySetNotInt = [EmptySetNotIntAxiom]
     regularity :: [LogicRule s sE t]
     regularity =  [RegularityAxiom]
     union :: [LogicRule s sE t]
     union = [UnionAxiom]
     powerSet :: [LogicRule s sE t]
     powerSet = [PowerSetAxiom]
     pairing :: [LogicRule s sE t]
     pairing = [PairingAxiom]
     choice :: [LogicRule s sE t]
     choice = [AxiomOfChoice]
     intOrderAntiSymmetry :: [LogicRule s sE t]
     intOrderAntiSymmetry = [IntOrderAntisymmetry]
     intOrderReflexivity :: [LogicRule s sE t]
     intOrderReflexivity = [IntOrderReflexivity]
     intOrderTransitivity :: [LogicRule s sE t]
     intOrderTransitivity = [IntOrderTransitivity]
     intOrderTotality :: [LogicRule s sE t]
     intOrderTotality = [IntOrderTotality]
     intAddClosure :: [LogicRule s sE t]
     intAddClosure        = [IntAddClosure]
     intMulClosure :: [LogicRule s sE t]
     intMulClosure        = [IntMulClosure]
     intNegClosure :: [LogicRule s sE t]
     intNegClosure        = [IntNegClosure]
     intAddAssociativity :: [LogicRule s sE t]
     intAddAssociativity  = [IntAddAssociativity]
     intAddCommutativity :: [LogicRule s sE t]
     intAddCommutativity  = [IntAddCommutativity]
     intAddIdentity       = [IntAddIdentity]
     intAddInverse :: [LogicRule s sE t]
     intAddInverse        = [IntAddInverse]
     intMulAssociativity  = [IntMulAssociativity]
     intMulCommutativity :: [LogicRule s sE t]
     intMulCommutativity  = [IntMulCommutativity]
     intMulIdentity :: [LogicRule s sE t]
     intMulIdentity       = [IntMulIdentity]
     intDistributivity :: [LogicRule s sE t]
     intDistributivity    = [IntDistributivity]
     intOrderAddCompatibility = [IntOrderAddCompatibility]
     intOrderMulCompatibility :: [LogicRule s sE t]
     intOrderMulCompatibility = [IntOrderMulCompatibility]
     natWellOrdering :: [LogicRule s sE t]
     natWellOrdering = [NatWellOrderingAxiom]






-- Finds the first element that appears more than once in the list.
findFirstDuplicate :: Ord a => [a] -> Maybe a
findFirstDuplicate xs = fst $ foldl' check (Nothing, Set.empty) xs
  where
    check :: Ord a => (Maybe a, Set.Set a) -> a -> (Maybe a, Set.Set a)
    check (Just dup, seen) _ = (Just dup, seen) -- Once found, stop checking
    check (Nothing, seen) x
      | Set.member x seen = (Just x, seen)      -- Found a duplicate
      | otherwise         = (Nothing, Set.insert x seen) -- Add to seen se




runProofAtomic :: (
               ProofStd s (LogicError s sE t) [LogicRule s sE t] Text (),
               Show sE, Typeable sE, Show s, Typeable s, TypeableTerm t Text () sE,
                TypedSent Text () sE s,
               Show t, Typeable t,
               StdPrfPrintMonad s Text () (Either SomeException),
                            PREDL.LogicSent s t () Text, LogicSent s t ,
                            Eq t, LogicTerm t) =>
                            LogicRule s sE t  ->
                            PrfStdContext () ->
                            PrfStdState s Text () ->
                            Either (LogicError s sE t) (Maybe s,Maybe (Text,()),PrfStdStep s Text ())
runProofAtomic rule context state  = 
      case rule of
          PredRule predR -> do
               left  LogicErrPredL (PREDL.runProofAtomic predR context state)
          ProofByAsm schema -> do
               (implication,step) <- left LogicErrPrfByAsm (runProofByAsm schema context state)
               return (Just implication, Nothing, step)
          ProofBySubArg schema -> do
               step <- left LogicErrPrfBySubArg (runProofBySubArg schema context state)
               return (Just $ argPrfConsequent schema, Nothing, step)
          Theorem schema -> do
               step <- left LogicErrTheorem (establishTheorem schema context state)
               return (Just $ theorem schema, Nothing, step)
          TheoremM schema -> do
               (theorem,step) <- left LogicErrTheoremM (establishTmSilentM schema context state)
               return (Just theorem,Nothing, step)
          ProofByUG schema -> do
               (generalized,step) <- left LogicErrUG (runProofByUG schema context state)
               return (Just generalized,Nothing, step)
          Specification outerIdxs idx t s -> do
               -- Check idx is not in outerIdxs
               when (idx `elem` outerIdxs) $ -- Use 'when' from Control.Monad for cleaner Either handling
                   throwError $ LogicErrSpecOuterIndexConflict idx outerIdxs -- Use new error

               -- Check for duplicates in outerIdxs
               case findFirstDuplicate outerIdxs of
                   Just dup -> throwError $ LogicErrSpecOuterIndexDuplicate dup outerIdxs -- Use new error with the duplicate
                   Nothing -> return () -- No duplicates found, continue

               -- Get context info
               let constDict = fmap fst (consts state)

               -- Create the template variable dictionary allowing X i for i in outerIdxs
               let tmpltVarTypeDictOuter = Data.Map.fromList $ Prelude.map (, ()) outerIdxs

               -- Check that t is sane, allowing outer template vars, but no V n vars.
               termType <- left (LogicErrSpecTermNotClosedSane t)
                               (getTypeTerm tmpltVarTypeDictOuter [] constDict t) -- Use [] for varStack

               -- Create the template variable dictionary allowing outer indices and the inner idx
               let tmpltVarTypeDictForS = Data.Map.insert idx () tmpltVarTypeDictOuter

               -- Check that 's' is sane, allowing outer template vars and X idx, but no V n vars.
               maybe (return ()) (throwError . LogicErrSpecTmpltNotSane s)
                     (checkSanity tmpltVarTypeDictForS [] constDict s) -- Use [] for varStack

               -- Build the axiom instance using the helper.
               let specAx = specAxiom outerIdxs idx t s -- Placeholder: Replace with updated helper call

               -- Build the axiom instance using the helper.
               -- CRITICAL ASSUMPTION: The *updated* specAxiom helper (likely in Langs/BasicUntyped.hs)
               -- must now consume ALL template variables
               -- (X idx and all X i where i is in outerIdxs), and return a fully closed proposition.
               let specAx = specAxiom outerIdxs idx t s -- Placeholder: Replace with updated helper call
                                                 -- e.g., ZFC.specAxiom outerIdxs idx t s

               -- **No final sanity check on specAx needed here if assumptions hold**
               -- Create the proof step
               let step = PrfStdStepStep specAx "AXIOM_SPECIFICATION" []
               return (Just specAx, Nothing, step)
          Replacement outerIdxs idx1 idx2 t s -> do
               -- Basic validation of indices
               when (idx1 == idx2) $
                   throwError $ LogicErrReplIndexConflict idx1 idx2 outerIdxs
               when (idx1 `elem` outerIdxs) $
                   throwError $ LogicErrReplIndexConflict idx1 idx1 outerIdxs
               when (idx2 `elem` outerIdxs) $
                   throwError $ LogicErrReplIndexConflict idx2 idx2 outerIdxs
               case findFirstDuplicate outerIdxs of
                   Just dup -> throwError $ LogicErrReplOuterIndexDuplicate dup outerIdxs
                   Nothing -> return ()

               -- Get context info
               let constDict = fmap fst (consts state)

               -- Template dictionary allowing X i for i in outerIdxs (for checking t)
               let tmpltVarTypeDictOuter = Data.Map.fromList $ Prelude.map (, ()) outerIdxs

               -- Check that t is sane (allows outer X vars, disallows V n, idx1, idx2)
               -- Assuming getTypeTerm checks that t does not contain X idx1 or X idx2 implicitly
               -- If not, add specific checks or adjust getTypeTerm.
               termType <- left (LogicErrSpecTermNotClosedSane t) -- Reuse Spec error or make new one for Repl
                               (getTypeTerm tmpltVarTypeDictOuter [] constDict t) -- Use [] for varStack

               -- Template dictionary allowing outer indices and the inner idx1, idx2 (for checking s)
               let tmpltVarTypeDictForS = Data.Map.insert idx1 () $ Data.Map.insert idx2 () tmpltVarTypeDictOuter

               -- Check that 's' is sane (allows outer X vars, X idx1, X idx2, disallows V n)
               maybe (return ()) (throwError . LogicErrReplTmpltNotSane s)
                     (checkSanity tmpltVarTypeDictForS [] constDict s) -- Use [] for varStack

               -- Build the axiom instance using the helper.
               -- CRITICAL ASSUMPTION: The *updated* replaceAxiom helper must now accept 'outerIdxs',
               -- consume ALL template variables (X idx1, X idx2, and all X i where i is in outerIdxs),
               -- and return a fully closed proposition.
               -- The version in Langs/BasicUntyped.hs currently does NOT do this.
               let replAx = replaceAxiom outerIdxs idx1 idx2 t s -- Using the corrected signature

               -- No final sanity check on replAx needed if assumptions hold

               -- Create the proof step
               let step = PrfStdStepStep replAx "AXIOM_REPLACEMENT" []
               return (Just replAx, Nothing, step)

          IntegerMembership i -> do
              let resultSent = integer i `memberOf` intSet
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "AXIOM_INTEGER_MEMBERSHIP" [])

          IntegerAddition i1 i2 -> do
              let termLHS = integer i1 .+. integer i2
              let termRHS = integer (i1 + i2) -- Meta-level calculation
              let resultSent = termLHS .==. termRHS
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "AXIOM_INTEGER_ADDITION" [])

          IntegerMultiplication i1 i2 -> do
              let termLHS = integer i1 .*. integer i2
              let termRHS = integer (i1 * i2) -- Meta-level calculation
              let resultSent = termLHS .==. termRHS
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "AXIOM_INTEGER_MULTIPLICATION" [])

          IntegerNegation i -> do
              let termLHS = intNeg (integer i)
              let termRHS = integer (-i) -- Meta-level calculation
              let resultSent = termLHS .==. termRHS
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "AXIOM_INTEGER_NEGATION" [])
          IntegerCompare i1 i2 -> do
              when (i1 > i2) $
                  throwError $ LogicErrIntCompareFalse i1 i2 -- Error for invalid comparison
              let resultSent = integer i1 .<=. integer i2
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "AXIOM_INTEGER_LTE" [])
          IntegersAreUrelements -> do
              -- Get the axiom instance by calling the renamed LogicSent method
              let axiomInstance = intsAreUrelementsAxiom -- Use the renamed method

              -- Sanity Check Optional/Removed

              -- Create the proof step
              let justificationText = "AXIOM_INTEGER_URELEMENT"
              let step = PrfStdStepStep axiomInstance justificationText []
              return (Just axiomInstance, Nothing, step)
          IntegerInequality i1 i2 -> do
              when (i1 == i2) $ -- This axiom asserts inequality, so it's an error if inputs are equal
                  throwError $ LogicErrIntInequalitySameValues i1 i2
              -- Construct the proposition: Integ i1 ./=. Integ i2
              -- This translates to: neg (Integ i1 .==. Integ i2)
              -- 'integer' comes from the `LogicTerm t` constraint.
              -- 'neg' comes from `PL.LogicSent s ()` (via `PREDL.LogicSent s t ()`).
              -- '.==.' comes from `PREDL.LogicSent s t ()`.
              -- For your specific types PropDeBr and ObjDeBr, these resolve to
              -- Neg ((Integ i1) :==: (Integ i2)), which is your (./=.) shorthand.
              let resultSent = neg (integer i1 .==. integer i2)
              return (Just resultSent, Nothing, PrfStdStepStep resultSent "AXIOM_INTEGER_INEQUALITY" [])
          EmptySetAxiom -> do
              let axiomInstance = emptySetAxiom -- From LogicSent s t constraint
              -- Optional: Sanity check if the axiom is complexly generated in LogicSent
              -- maybe (return ()) (throwError . MetaRuleErrNotClosed axiomInstance) (checkSanity mempty [] (fmap fst (consts state)) axiomInstance)
              let step = PrfStdStepStep axiomInstance "AXIOM_EMPTY_SET" []
              return (Just axiomInstance, Nothing, step)

          ExtensionalityAxiom -> do
              let axiomInstance = extensionalityAxiom -- From LogicSent s t constraint
              -- Optional: Sanity check
              -- maybe (return ()) (throwError . MetaRuleErrNotClosed axiomInstance) (checkSanity mempty [] (fmap fst (consts state)) axiomInstance)
              let step = PrfStdStepStep axiomInstance "AXIOM_EXTENSIONALITY" []
              return (Just axiomInstance, Nothing, step)
          RegularityAxiom -> do
              let axiomInstance = regularityAxiom -- From LogicSent s t constraint
              -- No sanity check needed as it's a fixed, closed proposition.
              let step = PrfStdStepStep axiomInstance "AXIOM_REGULARITY" []
              return (Just axiomInstance, Nothing, step) 
          UnionAxiom -> do
              let axiomInstance = unionAxiom -- From LogicSent s t constraint
              let step = PrfStdStepStep axiomInstance "AXIOM_UNION" []
              return (Just axiomInstance, Nothing, step)
          PowerSetAxiom -> do
              let axiomInstance = powerSetAxiom -- From LogicSent s t constraint
              let step = PrfStdStepStep axiomInstance "AXIOM_POWER_SET" []
              return (Just axiomInstance, Nothing, step)
          PairingAxiom -> do
              let axiomInstance = pairingAxiom -- From LogicSent s t constraint
              let step = PrfStdStepStep axiomInstance "AXIOM_PAIRING" []
              return (Just axiomInstance, Nothing, step)
          AxiomOfChoice -> do
              let axiomInstance = axiomOfChoice -- From LogicSent s t constraint
              let step = PrfStdStepStep axiomInstance "AXIOM_CHOICE" []
              return (Just axiomInstance, Nothing, step)
          IntOrderAntisymmetry -> do
              let axiomInstance = intOrderAntisymmetryAxiom -- From LogicSent s t constraint
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ORDER_ANTISYMMETRY" []
              return (Just axiomInstance, Nothing, step)
          IntOrderReflexivity -> do
              let axiomInstance = intOrderReflexivityAxiom -- From LogicSent s t constraint
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ORDER_REFLEXIVITY" []
              return (Just axiomInstance, Nothing, step)
          IntOrderTransitivity -> do
                let axiomInstance = intOrderTransitivityAxiom -- From LogicSent s t constraint
                let step = PrfStdStepStep axiomInstance "AXIOM_INT_ORDER_TRANSITIVITY" []
                return (Just axiomInstance, Nothing, step)
          IntOrderTotality -> do
                let axiomInstance = intOrderTotalityAxiom -- From LogicSent s t constraint
                let step = PrfStdStepStep axiomInstance "AXIOM_INT_ORDER_TOTALITY" []
                return (Just axiomInstance, Nothing, step)

          IntAddClosure -> do
              let axiomInstance = intAddClosureAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ADD_CLOSURE" []
              return (Just axiomInstance, Nothing, step)
          IntMulClosure -> do
              let axiomInstance = intMulClosureAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_MUL_CLOSURE" []
              return (Just axiomInstance, Nothing, step)
          IntNegClosure -> do
              let axiomInstance = intNegClosureAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_NEG_CLOSURE" []
              return (Just axiomInstance, Nothing, step)
          IntAddAssociativity -> do -- Was previously started/duplicated, now unique
              let axiomInstance = intAddAssociativityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ADD_ASSOCIATIVITY" []
              return (Just axiomInstance, Nothing, step)
          IntAddCommutativity -> do
              let axiomInstance = intAddCommutativityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ADD_COMMUTATIVITY" []
              return (Just axiomInstance, Nothing, step)
          IntAddIdentity -> do
              let axiomInstance = intAddIdentityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ADD_IDENTITY" []
              return (Just axiomInstance, Nothing, step)
          IntAddInverse -> do
              let axiomInstance = intAddInverseAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ADD_INVERSE" []
              return (Just axiomInstance, Nothing, step)
          IntMulAssociativity -> do
              let axiomInstance = intMulAssociativityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_MUL_ASSOCIATIVITY" []
              return (Just axiomInstance, Nothing, step)
          IntMulCommutativity -> do
              let axiomInstance = intMulCommutativityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_MUL_COMMUTATIVITY" []
              return (Just axiomInstance, Nothing, step)
          IntMulIdentity -> do
              let axiomInstance = intMulIdentityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_MUL_IDENTITY" []
              return (Just axiomInstance, Nothing, step)
          IntDistributivity -> do
              let axiomInstance = intDistributivityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_DISTRIBUTIVITY" []
              return (Just axiomInstance, Nothing, step)
          IntOrderAddCompatibility -> do
              let axiomInstance = intOrderAddCompatibilityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ORDER_ADD_COMPATIBILITY" []
              return (Just axiomInstance, Nothing, step)
          IntOrderMulCompatibility -> do
              let axiomInstance = intOrderMulCompatibilityAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_INT_ORDER_MUL_COMPATIBILITY" []
              return (Just axiomInstance, Nothing, step)
          NatWellOrderingAxiom -> do
              let axiomInstance = natWellOrderingAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_NAT_WELL_ORDERING" []
              return (Just axiomInstance, Nothing, step)
          EmptySetNotIntAxiom -> do
              let axiomInstance = emptySetNotIntAxiom
              let step = PrfStdStepStep axiomInstance "AXIOM_EMPTY_SET_IS_SET" []
              return (Just axiomInstance, Nothing, step)

    where
        proven = (keysSet . provenSents) state
        constDict = fmap fst (consts state)
        varStack = freeVarTypeStack context




instance (Show sE, Typeable sE, Show s, Typeable s, TypedSent Text () sE s,
             TypeableTerm t Text () sE, 
             Monoid (PrfStdState s Text ()), Show t, Typeable t,
             StdPrfPrintMonad s Text () (Either SomeException),
             Monoid (PrfStdContext ()),
             PREDL.LogicSent s t () Text,
             LogicSent s t, Eq t, LogicTerm t) 
          => Proof (LogicError s sE t) 
             [LogicRule s sE t] 
             (PrfStdState s Text ()) 
             (PrfStdContext ())
             [PrfStdStep s Text ()]
               s 
                 where

    runProofOpen :: [LogicRule s sE t ]
                     -> PrfStdContext () 
                     -> PrfStdState s Text ()
                     -> Either (LogicError s sE t) (PrfStdState s Text (),[PrfStdStep s Text ()], Last s)
    runProofOpen rs context oldState = foldM f (PrfStdState mempty mempty 0,[], Last Nothing) rs
       where
           f (newState,newSteps, mayLastProp) r =  fmap g (runProofAtomic r context (oldState <> newState))
             where
                 g ruleResult = case ruleResult of
                    (Just s,Nothing,step) -> (newState <> PrfStdState (Data.Map.insert s newLineIndex mempty) mempty 1,
                                         newSteps <> [step], (Last . Just) s)
                    (Just s,Just (newConst,tType), step) -> (newState <> 
                            PrfStdState (Data.Map.insert s newLineIndex mempty) 
                               (Data.Map.insert newConst (tType,newLineIndex) mempty) 1,
                               newSteps <> [step], (Last . Just) s)
                    (Nothing,Just (newConst,tType), step) -> (newState <> 
                            PrfStdState mempty
                               (Data.Map.insert newConst (tType,newLineIndex) mempty) 1,
                               newSteps <> [step], mayLastProp)
                    (Nothing,Nothing, step) -> (newState <>
                            PrfStdState mempty mempty 1,
                               newSteps <> [step], mayLastProp)
                    where
                        newStepCount = stepCount newState + 1
                        newLineIndex = stepIdxPrefix context <> [stepCount oldState + newStepCount-1]






instance REM.SubproofRule [LogicRule s sE t] s where
     proofBySubArg:: s -> [LogicRule s sE t] -> [LogicRule s sE t]
     proofBySubArg s r = [ProofBySubArg $ ProofBySubArgSchema s r]



instance PL.SubproofRule [LogicRule s sE t] s where
     proofByAsm:: s -> s -> [LogicRule s sE t] -> [LogicRule s sE t]
     proofByAsm asm cons subproof = [ProofByAsm $ ProofByAsmSchema asm cons subproof]


instance PREDL.SubproofRule [LogicRule s sE t] s Text () where
     theoremSchema:: TheoremSchema s [LogicRule s sE t] Text () -> [LogicRule s sE t]
     theoremSchema schema = [Theorem schema]
     theoremAlgSchema:: TheoremAlgSchema () [LogicRule s sE t] s Text () -> [LogicRule s sE t]
     theoremAlgSchema schema = [TheoremM schema]

     proofByUG:: s -> [LogicRule s sE t] -> [LogicRule s sE t]
     proofByUG s r  = [ProofByUG $ ProofByUGSchema s r]

standardRuleM :: (Monoid r,Monad m, Ord o, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL r o tType, StdPrfPrintMonad s o tType m    )
       => r -> ProofGenTStd tType r s o m (s,[Int])
standardRuleM rule = do
    -- function is unsafe and used for rules that generate one or more sentence.
    -- probably should not be externally facing.
     mayPropIndex <- monadifyProofStd rule
     maybe (error "Critical failure: No index looking up sentence.") return mayPropIndex



specificationM :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m    )
       => [Int] -> Int -> t -> s -> ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
specificationM outerIdxs idx t s = standardRuleM (specification outerIdxs idx t s)



replacementM :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m    )
       => [Int] -> Int -> Int -> t -> s -> ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
replacementM outerIdxs idx1 idx2 t s = standardRuleM (replacement outerIdxs idx1 idx2 t s)


integerMembershipM, integerNegationM :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m    )
       => Int -> ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
integerMembershipM i = standardRuleM (integerMembership i)
integerNegationM i = standardRuleM (integerNegation i)

integerAdditionM, integerMultiplicationM, integerCompareM, integerInequalityM
 :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m    )
       => Int -> Int -> ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
integerAdditionM i1 i2 = standardRuleM (integerAddition i1 i2)
integerMultiplicationM i1 i2 = standardRuleM (integerMultiplication i1 i2)
integerCompareM i1 i2 = standardRuleM (integerCompare i1 i2)
integerInequalityM i1 i2 = standardRuleM (integerInequality i1 i2)


integersAreUrelementsM, emptySetAxiomM, extensionalityAxiomM,emptySetNotIntM,regularityAxiomM, unionAxiomM,
             powerSetAxiomM, pairingAxiomM, axiomOfChoiceM, intOrderAntiSymmetryM,
             intOrderReflexivityM, intOrderTransitivityM, intOrderTotalityM,
             intAddClosureAxiomM, intMulClosureAxiomM, intNegClosureAxiomM,
             intAddAssociativityM, intAddCommutativityAxiomM, intAddIdentityAxiomM, intAddInverseAxiomM,
             intMulAssociativityAxiomM, intMulCommutativityAxiomM, intMulIdentityAxiomM,
             intDistributivityAxiomM,intOrderAddCompatibilityAxiomM, intOrderMulCompatibilityAxiomM,
             natWellOrderingAxiomM
       :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m,
       LogicRuleClass [LogicRule s sE t] s sE t)
       => ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
integersAreUrelementsM = standardRuleM integersAreUrelements
emptySetAxiomM = standardRuleM emptySet
extensionalityAxiomM = standardRuleM extensionality
emptySetNotIntM = standardRuleM emptySetNotInt
regularityAxiomM = standardRuleM regularity
unionAxiomM = standardRuleM union
powerSetAxiomM = standardRuleM powerSet
pairingAxiomM = standardRuleM pairing
axiomOfChoiceM = standardRuleM choice
intOrderAntiSymmetryM = standardRuleM intOrderAntiSymmetry
intOrderReflexivityM = standardRuleM intOrderReflexivity
intOrderTransitivityM = standardRuleM intOrderTransitivity
intOrderTotalityM = standardRuleM intOrderTotality
intAddClosureAxiomM        = standardRuleM intAddClosure
intMulClosureAxiomM        = standardRuleM intMulClosure
intNegClosureAxiomM        = standardRuleM intNegClosure
intAddAssociativityM       = standardRuleM intAddAssociativity -- Was previously started
intAddCommutativityAxiomM  = standardRuleM intAddCommutativity
intAddIdentityAxiomM       = standardRuleM intAddIdentity
intAddInverseAxiomM        = standardRuleM intAddInverse
intMulAssociativityAxiomM  = standardRuleM intMulAssociativity
intMulCommutativityAxiomM  = standardRuleM intMulCommutativity
intMulIdentityAxiomM       = standardRuleM intMulIdentity
intDistributivityAxiomM    = standardRuleM intDistributivity
intOrderAddCompatibilityAxiomM = standardRuleM intOrderAddCompatibility
intOrderMulCompatibilityAxiomM = standardRuleM intOrderMulCompatibility
natWellOrderingAxiomM = standardRuleM natWellOrdering


data MetaRuleError s where
   MetaRuleErrNotClosed :: s -> MetaRuleError s
   MetaRuleErrFreeVarsQuantCountMismatch :: MetaRuleError s

   deriving(Show,Typeable)


instance (Show s, Typeable s) => Exception (MetaRuleError s)



instance RuleInject [REM.LogicRule () s sE Text] [LogicRule s sE t] where
    injectRule:: [REM.LogicRule () s sE Text] -> [LogicRule s sE t]
    injectRule = Prelude.map (PredRule . PREDL.PropRule . PL.BaseRule)



instance RuleInject [PL.LogicRule () s sE Text] [LogicRule s sE t] where
    injectRule:: [PL.LogicRule () s sE Text] -> [LogicRule s sE t]
    injectRule = Prelude.map (PredRule . PREDL.PropRule)


instance RuleInject [PREDL.LogicRule s sE Text t ()] [LogicRule s sE t] where
    injectRule:: [PREDL.LogicRule s sE Text t ()] -> [LogicRule s sE t]
    injectRule = Prelude.map PredRule






