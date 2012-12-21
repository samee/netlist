
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import qualified Data.Array as A
import Data.List
import Debug.Trace
import System.Random
import System.IO

import Circuit.NetList
import Circuit.NetList.Gcil
import qualified Circuit.Sorter as Sort
import Benchmark.DemoCircuits
--import Test.Gcil
import Util

-- Use the naive O(n^2) method
localWideAngle thMax l = maximum [f a b | a<-l, b<-l, a<=b] where
  f a b = min (b-a) (thMax-b+a)

-- This is currently unused
-- Was having some mysterious memory problems with the other version
localWideAngle2 thMax l = aux 0 0 1 where
  aux result j i | i>=n = result
                 | j<i && f j i <= f (j+1) i = aux result' (j+1) i
                 | otherwise = aux result' j (i+1)
    where
    result' = max result $ f j i
  n = length l
  f j i = fixup $ (arr A.! i) - (arr A.! j)
  arr = A.listArray (0,n-1) $ sort l
  fixup x = min x (thMax-x)
  sampleDiff d = traceShow pair d where 
    pair = head $ [(j,i) | j<-l, i<-l, fixup (i-j) == d]

randomWideAngleTest thMax n rgen = flip runState rgen $ do
  l1 <- replicateM half $ state $ randomR (0,thMax-1)
  l2 <- replicateM (n-half) $ state $ randomR (0,thMax-1)
  return (sort l1,sort l2,thMax)
  where half = n `div` 2

wideAngleCase algo (theta1,theta2,thMax) = do
  theta1V <- mapM (testInt ServerSide thetaWidth) theta1
  theta2V <- mapM (testInt ClientSide thetaWidth) theta2
  result <- liftNet $ do
    theta <- Sort.merge cmpSwap theta1V theta2V
    r <- algo theta (constInt thMax)
    newOutput =<< bitify r
    return r
  ignoreAndsUsed $ liftNet 
                 $ newOutput =<< bitify =<< equal result (constInt expected)
  where expected = localWideAngle thMax $ theta1++theta2
        thetaWidth = valueSize thMax

{-
runWideAngleTests = forM_ ns $ \n -> do
             putStrLn $ "Case n = "++show n
             (l,expected) <- getStdRandom (randomWideAngleTest thMax n)
             burnWideAngleTest l thMax expected
             putStrLn $ "Naive method would use "
                         ++show (naiveCost thMax n)++" gates"
  where
  thMax = 256
  ns = [128, 256, 512, 1024, 2048]

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

-}

traceMerge x@(l1,l2,_) = traceShow (runIdentity $ Sort.merge cx l1 l2) x
  where 
  cx a b = return $ if a<b then (a,b) else (b,a)

main = do hSetBuffering stdout LineBuffering
          forM_ [128,256,512,1024,2048] $ \n -> do
            pack <- getStdRandom (randomWideAngleTest 256 n)
            burnBenchmark ("wideAngleSmart"++show n) 
              $ wideAngleCase wideAngle pack
            burnBenchmark ("wideAngleNaive"++show n)
              $ wideAngleCase wideAngleNaive pack
