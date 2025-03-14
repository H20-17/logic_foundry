module StdPattern(
    PrfStdContext(..), PrfStdState(..), PrfStdStep(..), TestSubproofErr, BigException(..), 
    RuleInject(..), ProofGenTStd, ProofStd,
    TypeableTerm(..),
    StdPrfPrintMonadFrame(..), StdPrfPrintMonad(..),
    monadifyProofStd,
    getProofState, runProofGeneratorT, Proof, runProof, ProofGeneratorT, modifyPS, getTopFreeVar, 
    TypedSent(..)
    
) where
import Kernel
    ( Proof,
      ProofGeneratorT,
      getProofState,
      runProofGeneratorT,
      runProof,
      modifyPS)
import Internal.StdPattern
    ( 
      StdPrfPrintMonad(..),
      StdPrfPrintMonadFrame(..),
      BigException(..),
      TestSubproofErr,
      TypeableTerm(..),
      PrfStdStep(..),
      ProofStd,
      ProofGenTStd,
      PrfStdState(..),
      PrfStdContext(..),
      monadifyProofStd,
      getTopFreeVar,
      RuleInject(..),
      TypedSent(..))