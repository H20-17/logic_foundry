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
    ( runProof,
      runProofGeneratorT,
      PredLogicSent(..),
      ProofByUGSchema(ProofByUGSchema),
      ProofByAsmSchema(ProofByAsmSchema),
      StdPrfPrintMonad(..),
      StdPrfPrintMonadFrame(..),
      TheoremSchemaMT(TheoremSchemaMT),
      PropLogicSent(..),
      TypedSent(..),
      TypeableTerm(..),
      PrfStdStep(..),
      ProofGenTStd,
      getTopFreeVar
 )
import qualified RuleSets.PropLogic as PL
import RuleSets.PredLogicUntyped
import Langs.BasicUntyped
default(Text)









testTheoremMSchema :: (MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => TheoremSchemaMT () [PredRuleDeBr] PropDeBr Text m ()
testTheoremMSchema = TheoremSchemaMT  [("N",())] [z1,z2] theoremProg 
  where
    z1 = Forall (Bound 0  :<-: (Constant . pack) "N" :&&: Bound 0 :>=: Integ 10 :->: Bound 0 :>=: Integ 0)
    z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
    z3 = (Integ 0 :>=: Integ 0) :||: ((Integ 0 :>=: Integ 0) :||: (Integ 0 :>=: Integ 0))
    z4 = ((Integ 0 :>=: Integ 0) :||: (Integ 0 :>=: Integ 0)) :||: (Integ 0 :>=: Integ 21)
    z5 = (Integ 0 :>=: Integ 0) :->: ((Integ 0 :>=: Integ 0) :->: (Integ 0 :>=: Integ 88))


main :: IO ()
main = do
    let y0 =  (Integ 0 :==: Integ 0) :->: (Integ 99 :==: Integ 99)
    let y1 = Integ 0 :==: Integ 0
    let y2= (Integ 99 :==: Integ 99) :->: (Integ 1001 :==: Integ 1001)
    let x0 = Exists (Forall ((Integ 0 :==: Free 102) 
              :&&: (Bound 0 :<-: Bound 1)) :&&: (Bound 1 :<-: Bound 1))
    let x1 = Forall (Forall (Forall ((Bound 3 :==: Bound 2) :&&: Forall (Bound 0 :==: Bound 1))))
    (print . show) (checkSanity [(),()] x0 mempty)
    (print . show) x1
    let f = parseForall x1
    case f of
        Just l -> do
            let term1 = Hilbert (Integ 0 :<-: Integ 0)
            let fNew = lType2Func l term1
            (print.show) fNew
        Nothing -> print "parse failed!"
       --let z = applyUG xn () 102
--    -- (print . show) z
    let proof = [
                  PL.FakeProp y0
                , PL.FakeProp y1
                , PL.FakeProp y2
                , PL.MP y0
                , PL.MP y2
                , PL.ProofByAsm $ ProofByAsmSchema y1  (Integ 99 :==: Integ 99) [PL.MP $ y1 .->. (Integ 99 :==: Integ 99)]
                ] 



    let zb = runProof proof
    -- either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb
    print "OI leave me alone"
    let z1 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10)) :->: (Bound 0 :>=: Integ 0))
    let z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
    let generalizable = Lambda (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10)) :->: (Bound 0 :==: Integ 0))
    let asm = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
    let mid = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 0)
    let proof2 = [
                    FakeConst "N" (),
                    fakeProp z1,
                    fakeProp z2,
                    ProofByUG (ProofByUGSchema generalizable
                                     [
                                        ProofByAsm (ProofByAsmSchema asm (Free 0 :==: Integ 0) [
                                             UI (Free 0) z1,
                                             mp $ asm .->. (Free 0 :>=: Integ 0),
                                             simpL $ (:&&:) (Free 0  :<-: (Constant . pack) "N") (Free 0 :>=: Integ 10),
                                             adj (Free 0  :<-: (Constant . pack) "N") (Free 0 :>=: Integ 0),
                                             UI (Free 0) z2,
                                             mp $ mid .->. (Free 0 :==: Integ 0)
                                        ] )
                                     ]
                                  )
                 ]

    let proof3 = [
                    ProofByUG (ProofByUGSchema generalizable
                                     [
                                        ProofByAsm (ProofByAsmSchema asm z1 [
                                             UI (Free 0) z1,
                                              
                                             mp $ asm .->. (Free 0 :>=: Integ 0)
                                      
                                        ]  )
                                     ]
                                  )
                 ]
    let zb2 = runProof proof2 


    let zb3 = runProof [FakeConst "N" (), fakeProp z1, fakeProp z2, UI (Free 0) z1]
    --either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd)  zb2
    --either (putStrLn . show) (putStrLn . unpack . showPropDeBrStepsBase . snd) zb3
    (a,b,c,d) <- runProofGeneratorT testprog
    print "hi wattup"
    (putStrLn . unpack . showPropDeBrStepsBase) c
--    print "YOYOYOYOYOYOYOYOYOYO"
--    --(a,b,c,d,e) <- checkTheoremM testTheoremMSchema
--    print "yo"
--    --(putStrLn . unpack . showPropDeBrStepsBase) d
--    return ()



testprog::ProofGenTStd () [PredRuleDeBr] PropDeBr Text IO ()
testprog = do
      let z1 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10))  :->: (Bound 0 :>=: Integ 0))
      let z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
      let generalizable = ((Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)) :->: (Free 0 :==: Integ 0)
      let asm = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
      let asm2 = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
      let mid = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 0)
      fakeConstM "N" ()
      fakePropM z1
      fakePropM z2
      
      fux<- runProofByUGM do
          runProofByAsmM  asm2 do
              (s5,())<- runProofBySubArgM  do
                 newFreeVar <- getTopFreeVar
                 (s1,_) <- uiM newFreeVar z1
                 (s2,_) <- mpM s1
                 (natAsm,_) <- simpLM asm
                 (s3,_) <- adjM natAsm s2
                 (s4,_) <- uiM newFreeVar z2
                 (s5,_) <- mpM s4
                 return ()
--              runTheoremM (\schm -> [PredProofTheorem schm]) testTheoremMSchema
              return ()
     
      runTheoremM  testTheoremMSchema
      runTmSilentM  testTheoremMSchema
      return ()

theoremProg::(MonadThrow m, StdPrfPrintMonad PropDeBr Text () m) => ProofGenTStd () [PredRuleDeBr] PropDeBr Text m ()
theoremProg = do
    let z1 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 10))  :->: (Bound 0 :>=: Integ 0))
    let z2 = Forall (((Bound 0  :<-: (Constant . pack) "N") :&&: (Bound 0 :>=: Integ 0)) :->: (Bound 0 :==: Integ 0))
    let generalizable = ((Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)) :->: (Free 0 :==: Integ 0)
    let asm = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
    let asm2 = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 10)
    let mid = (Free 0  :<-: (Constant . pack) "N") :&&: (Free 0 :>=: Integ 0)
    (generalized, ()) <- runProofByUGM do
          (imp,()) <- runProofByAsmM asm2 do
              newFreeVar <- getTopFreeVar
              (s1,_) <- uiM newFreeVar z1
              (s2,_) <- mpM s1
              --(lift . print) "Coment1"
              --(lift . print . show) s1

              (natAsm,_) <- simpLM asm
              --(lift . print) "COmment 2"
              (s3,_) <- adjM natAsm s2
              (s4,line_idx) <- uiM newFreeVar z2
              -- (lift . print . show) line_idx
              (s5,_) <- mpM s4
              (s6,_) <- simpLM asm
              return ()
          return ()
    return ()
--              return (s5,())


