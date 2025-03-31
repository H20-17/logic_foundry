module RuleSets.Internal.ZFC 
(
    LogicError(..), LogicRule(..), 
    runProofAtomic, 
    LogicRuleClass(..),
    LogicSent(..),
     emptySetM,
     specificationM,
     replacementM,
     MetaRuleError(..)
) where


import Data.Monoid ( Last(..) )

import Control.Monad ( foldM, unless )
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

import RuleSets.Internal.BaseLogic hiding 
   (LogicRuleClass,
   SubproofRule,
   LogicError(..),
   SubproofError(..),
   LogicRule(..),
   LogicError(..),
   runProofAtomic)
import qualified RuleSets.Internal.BaseLogic as REM

import RuleSets.Internal.PropLogic hiding 
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
import qualified RuleSets.Internal.PropLogic as PL

import RuleSets.Internal.PredLogic hiding 
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
import qualified RuleSets.Internal.PredLogic as PREDL





class LogicTerm t where
   nullSet :: t
   integer :: Int -> t

class (PREDL.LogicSent s t ()) => LogicSent s t | s ->t where
   emptySetAxiom :: s
   specAxiom :: t -> s -> s
   replaceAxiom :: t -> s -> s
   parseIn :: s -> Maybe (t, t)
   memberOf :: t -> t -> s



data LogicError s sE t where
    LogicErrPrfByAsm :: PL.SubproofError s sE (LogicError s sE t) -> LogicError s sE t
    LogicErrPrfBySubArg :: REM.SubproofError s sE (LogicError s sE t) -> LogicError s sE t
    LogicErrUG :: PREDL.SubproofError s sE  (LogicError s sE t) -> LogicError s sE t
    LogicErrTheorem :: PREDL.ChkTheoremError s sE (LogicError s sE t) Text () -> LogicError s sE t 
    LogicErrTheoremM :: SomeException -> LogicError s sE t 
    LogicErrPredL ::  PREDL.LogicError s sE Text t () -> LogicError s sE t

    LogicErrReplTermNotClosedSane :: t -> sE -> LogicError s sE t
    LogicErrSpecTermNotClosedSane :: t -> sE -> LogicError s sE t
    LogicErrReplInstanceNotClosedSane :: s -> sE -> LogicError s sE t

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
    EmptySet :: LogicRule s sE t
    Specification :: t -> s -> LogicRule s sE t
    Replacement :: t -> s -> LogicRule s sE t
    deriving(Show)


instance REM.LogicRuleClass [LogicRule s sE t] s Text () sE where
     remark:: Text -> [LogicRule s sE t]
     remark rem = [(PredRule . PREDL.PropRule . PL.BaseRule . REM.Remark) rem]
     rep :: s -> [LogicRule s sE t ]
     rep s = [(PredRule . PREDL.PropRule . PL.BaseRule . REM.Rep) s]
     fakeProp:: s -> [LogicRule s o t ]
     fakeProp s = [(PredRule . PREDL.PropRule . PL.BaseRule . REM.FakeProp) s]
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
     contraF :: s -> s -> [LogicRule s sE t]
     contraF a notA = [PredRule $ PREDL.PropRule $ PL.ContraF a notA]
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


class LogicRuleClass r s sE t | r->s, r->sE, r->t where
     emptySet :: r
     specification :: t -> s -> r
     replacement :: t -> s -> r

instance LogicRuleClass [LogicRule s sE t] s sE t where
     emptySet :: [LogicRule s sE t]
     emptySet = [EmptySet]
     specification :: t -> s -> [LogicRule s sE t]
     specification t s = [Specification t s]
     replacement :: t ->  s -> [LogicRule s sE t]
     replacement t s = [Replacement t s]




runProofAtomic :: (
               ProofStd s (LogicError s sE t) [LogicRule s sE t] Text (),
               Show sE, Typeable sE, Show s, Typeable s, TypeableTerm t Text () sE,
                TypedSent Text () sE s,
               Show t, Typeable t,
               StdPrfPrintMonad s Text () (Either SomeException),
                            PREDL.LogicSent s t (), LogicSent s t ) =>
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
          EmptySet -> do
               let step = PrfStdStepStep emptySetAxiom "AXIOM_EMPTYSET" []
               return (Just emptySetAxiom, Nothing, step)
          Specification t s -> do
               -- Check that t is a closed and sane term

               left (LogicErrSpecTermNotClosedSane t) (getTypeTerm t [] constDict)
               -- Build an instance of the replacement axiom
               -- using the term t and the sentence s
               let specAx = specAxiom t s
               -- Check that the axiom instance is closed and sane.
               -- s should have only one "X 0" variable in it
               -- How the replacementAxiom function is defined should take
               -- take advantage of that, replacing X 0 with a bound variable. Sanity checking for closure
               -- after the specAxiom function is applied will ensure that
               -- No other variables are in the term. 
               maybe (return ()) (throwError . LogicErrReplInstanceNotClosedSane s) (
                            checkSanity [] specAx constDict)

               let step = PrfStdStepStep specAx "AXIOM_SPECIFICATION" []
               return (Just specAx, Nothing, step)
          Replacement t s -> do
               -- Check that t is a closed and sane term
               left (LogicErrSpecTermNotClosedSane t) (getTypeTerm t [] constDict)
               -- Build an instance of the specification axiom
               -- using the term t and the sentence s
               let replAx = replaceAxiom t s
               -- Check that the axiom instance is closed and sane.
               -- s should have only one "X 0" variable in it
               -- How the replacementAxiom function is defined should take
               -- take advantage of that, replacing X 0 with a bound variable. Sanity checking for closure
               -- after the replaceAxiom function is applied will ensure that
               -- No other variables are in the term.
               maybe (return ()) (throwError . LogicErrReplInstanceNotClosedSane s) (
                            checkSanity [] replAx constDict)

               let step = PrfStdStepStep replAx "AXIOM_REPLACEMENT" []
               return (Just replAx, Nothing, step)


    where
        proven = (keysSet . provenSents) state
        constDict = fmap fst (consts state)
        varStack = freeVarTypeStack context




instance (Show sE, Typeable sE, Show s, Typeable s, TypedSent Text () sE s,
             TypeableTerm t Text () sE, 
             Monoid (PrfStdState s Text ()), Show t, Typeable t,
             StdPrfPrintMonad s Text () (Either SomeException),
             Monoid (PrfStdContext ()),
             PREDL.LogicSent s t (),
             LogicSent s t) 
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

emptySetM :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m    )
       => ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
emptySetM = standardRuleM emptySet


specificationM, replacementM :: (Monad m, Show sE, Typeable sE, Show s, Typeable s, Show eL, Typeable eL,
       MonadThrow m, Show o, Typeable o, Show tType, Typeable tType, TypedSent o tType sE s,
       Monoid (PrfStdState s o tType), ProofStd s eL [LogicRule s sE t] o tType, StdPrfPrintMonad s o tType m    )
       => t -> s -> ProofGenTStd tType [LogicRule s sE t] s o m (s,[Int])
specificationM t s = standardRuleM (specification t s)
replacementM t s = standardRuleM (replacement t s)


data MetaRuleError s where
   MetaRuleErrNotClosed :: s -> MetaRuleError s
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






