module Test.StableMarriage where

import Data.List
import Data.Array
import Debug.Trace
import System.Random

import Circuit.Interpreted.StableMarriage
import Util

randomTest :: RandomGen r => Int -> r -> (Bool,r)
randomTest n rgen = (checkStability,rgen3) where
  (_,orderM) = mapAccumL (\rgen _ -> swap $ randomlist rgen) rgen1 [1..n]
  (_,orderF) = mapAccumL (\rgen _ -> swap $ randomlist rgen) rgen2 [1..n]
  [rgen1,rgen2,rgen3] = randSplit 3 rgen
  rankM = arraymat $ map inversePermute orderM
  rankF = arraymat $ map inversePermute orderF
  marriage = traceShow ("OrderM",orderM) $ traceShow ("OrderF",orderF) $ stableMarriage orderM orderF
  curRankF = arrayfy [rankF!f!match | (f,match) <- zip [0..n-1] marriage]
  curRankM = arrayfy [rankM!m!match | (m,match) <- zip [0..n-1] 
                                        $ inversePermute marriage]

  checkStability = and [ curRankM!m <= rankM!m!f || curRankF!f <= rankF!f!m
                       | m <- [0..n-1], f <- [0..n-1]]
  randomlist rgen = randomPermute [0..n-1] rgen

  arrayfy l = listArray (0,n-1) l
  arraymat mat = arrayfy (map arrayfy mat)
  swap (a,b) = (b,a)

runTests = do --res <- getStdRandom $ randomTest 10
              let res = fst $ randomTest 10 $ mkStdGen 1
              putStrLn $ show $ res
