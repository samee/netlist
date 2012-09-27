module Test.Demo where

import Control.Monad
import Control.Monad.State
import Data.List
import System.Random

import Circuit.Gcil.Compiler
import Circuit.Gcil.Demo as Demo
import Test.Gcil
import Util

-- Use the naive O(n^2) method
localWideAngle thMax l = maximum [f a b | a<-l, b<-l, a<=b] where
  f a b = Prelude.min (b-a) (thMax-b+a)

randomWideAngleTest thMax n rgen = flip runState rgen $ do
  l <- replicateM n $ state $ randomR (0,thMax-1)
  return (sort l,localWideAngle thMax l)

wideAngleCase algo theta thMax expected = do
  thetaVars   <- replicateM (length theta) (newInput thetaWidth 1)
  thMaxVar    <- newInput thetaWidth 1
  expectedVar <- newInput thetaWidth 2
  result      <- algo thetaVars thMaxVar
  eq <- ignoreAndsUsed $ equalU expectedVar result
  newOutput (bitToInt eq)
  return ( [(gblName expectedVar, expected)]
         , zip (map gblName $ thMaxVar:thetaVars) (thMax:theta))

  where thetaWidth = valueSize thMax
      

burnWideAngleTest theta thMax expected = do
  writeTestCase "wideAngleTest" 
    (wideAngleCase Demo.wideAngle theta thMax expected) fst snd
  writeTestCase "wideAngleNaiveTest" 
    (wideAngleCase Demo.wideAngleNaive theta thMax expected) fst snd

naiveCost thMax n = fcost + maxcost where
  fcost = 4*w*fcount -- 2 subtractions and a min operation
  maxcost = (fcount-1)*2*w
  fcount = (n*(n-1)) `div` 2
  w = valueSize thMax

runTests = forM_ ns $ \n -> do
             putStrLn $ "Case n = "++show n
             (l,expected) <- getStdRandom (randomWideAngleTest thMax n)
             burnWideAngleTest l thMax expected
             putStrLn $ "Naive method would use "
                         ++show (naiveCost thMax n)++" gates"
  where
  thMax = 256
  ns = [128, 256, 512, 1024, 2048]
