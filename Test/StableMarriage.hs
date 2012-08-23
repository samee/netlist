module Test.StableMarriage where

import Data.List
import Data.Array
import System.Random

import Circuit.Interpreted.StableMarriage
import Util

randomTest :: RandomGen r => r -> Int -> Bool
randomTest rgen n = checkStability where
  (_,orderM) = mapAccumL (\rgen _ -> randomlist rgen) rgen1 [1..n]
  (_,orderF) = mapAccumL (\rgen _ -> randomlist rgen) rgen2 [1..n]
  (rgen1,rgen2) = split rgen
  rankM = map inversePermute orderM
  rankF = map inversePermute orderF
  marriage = stableMarriage orderM orderF
  curRankF = map (\(ranks,match) -> ranks!match) $ zip (arrayfy rankF) marriage
  curRankM = map (\(ranks,match) -> ranks!match) $ zip (arrayfy rankM) 
                                                 $ inversePermute marriage
  checkMale ranks sheRanks curM curF  = all (\(a,b) -> a>=curM || b>=curF)
                                      $ zip ranks sheRanks

  checkStability = all (\(a,b,c,d) -> checkMale a b c d)
                      $ zip4 rankM (transpose rankF) curRankM curRankF

  randomlist rgen = (rgen2, randomPermute rgen1 [0..n-1]) 
    where (rgen1,rgen2) = split rgen

  arrayfy l = map (listArray (0,n-1)) l

runTests :: IO ()
runTests = return ()
