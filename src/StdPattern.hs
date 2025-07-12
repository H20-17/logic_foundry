module StdPattern(
    PrfStdContext(..), PrfStdState(..), PrfStdStep(..), TestSubproofErr, TestSubproofMException(..), 
    RuleInject(..), ProofGenTStd, ProofStd,
    TypeableTerm(..),
    StdPrfPrintMonadFrame(..), StdPrfPrintMonad(..),
    monadifyProofStd,
    getProofState, runProofGeneratorT, Proof, runProof, ProofGeneratorT, modifyPS, getTopFreeVar, 
    getFreeVarCount,
    TypedSent(..),
    ShowableSent(..),
    ShowableTerm(..),
    showSentM
    
) where
import Kernel
    ( Proof,
      ProofGeneratorT,
      getProofState,
      runProofGeneratorT,
      runProof,
      modifyPS,
      RuleInject(..))
import Internal.StdPattern
    ( 
      StdPrfPrintMonad(..),
      StdPrfPrintMonadFrame(..),
      TestSubproofMException(..),
      TestSubproofErr,
      TypeableTerm(..),
      PrfStdStep(..),
      ProofStd,
      ProofGenTStd,
      PrfStdState(..),
      PrfStdContext(..),
      monadifyProofStd,
      getTopFreeVar,
      TypedSent(..),
      getFreeVarCount,
      ShowableSent(..),
      ShowableTerm(..),
      showSentM)