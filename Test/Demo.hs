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
  writeTestCase ("wideAngleTest" ++ show (length theta))
    (wideAngleCase Demo.wideAngle theta thMax expected) fst snd
  writeTestCase ("wideAngleNaiveTest" ++ show (length theta))
    (wideAngleCase Demo.wideAngleNaive theta thMax expected) fst snd

runWideAngleTests = forM_ ns $ \n -> do
             putStrLn $ "Case n = "++show n
             (l,expected) <- getStdRandom (randomWideAngleTest thMax n)
             burnWideAngleTest l thMax expected
             putStrLn $ "Naive method would use "
                         ++show (naiveCost thMax n)++" gates"
  where
  thMax = 256
  ns = [128, 256, 512, 1024, 2048]

naiveCost thMax n = fcost + maxcost where
  fcost = 4*w*fcount -- 2 subtractions and a min operation
  maxcost = (fcount-1)*2*w
  fcount = (n*(n-1)) `div` 2
  w = valueSize thMax

localRectangleInHistogram l = maximum [h*w | prefix <- init $ tails l,
    (h,w) <- scanl heightScanner (0,maxBound) prefix]  where
  heightScanner (i,h) h2 = (i+1, Prelude.min h h2)

randomRectangleInHistogram n hmax rgen = flip runState rgen $ do
  l <- replicateM n $ state $ randomR (0,hmax)
  return (l,localRectangleInHistogram l)

rectangleInHistogramCase hs hwidth expected = do
  hVars <- replicateM (length hs) (newInput hwidth 1)
  expectedVar <- newInput resultWidth 2
  result <- rectangleInHistogram hVars
  eq <- ignoreAndsUsed $ equalU expectedVar result
  newOutput (bitToInt eq)
  return  ( [(gblName expectedVar, expected)]
          , zip (map gblName $ hVars) hs)

  where resultWidth = valueSize (length hs) + hwidth


burnRectangleInHistogramCase hs hwidth expected =
  writeTestCase ("rectangleInHistogram" ++ show (length hs))
    (rectangleInHistogramCase hs hwidth expected) fst snd

runRectangleInHistogramTests = 
  forM_ [128,256,512,1024] $ \n -> do
    (hs,exp) <- getStdRandom (randomRectangleInHistogram n 255)
    burnRectangleInHistogramCase hs 8 exp

runTests = do runWideAngleTests
              runRectangleInHistogramTests


