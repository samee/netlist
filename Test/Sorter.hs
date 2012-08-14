module Test.Sorter where
import Control.Monad.Identity
import Debug.Trace
import System.Random

import qualified Circuit.Sorter as CS


batcherSortTest :: Ord a => [a] -> Bool
batcherSortTest l = sorted l' where
  l' = runIdentity $ CS.batcherSort swp l
  swp a b = return $ if a<=b then (a,b) else (b,a)


--shellSortTest :: Ord a => [a] -> Bool
shellSortTest l = sorted l' where
  l' = runIdentity $ CS.shellSort rgen swp l
  swp a b = return $ if a<=b then (a,b) else (b,a)
  rgen = fst $ head $ reads "ShellsortTest" :: StdGen

sorted [] = True
sorted [x] = True
sorted (x:y:l) = (x<=y) && sorted (y:l)

shortList = [4,2,6,34,5,8,2,4,6]
longList rgen = (take 20 full,rgen2) where
  (rgen1,rgen2) = split rgen
  full = randomRs (0,100) rgen1 :: [Int]

batcherSortTestShort = batcherSortTest shortList
shellSortTestShort = shellSortTest shortList

runTests = do
  ll <- getStdRandom longList
  putStrLn $ show batcherSortTestShort ++ "   Test.Sorter.batcherSortTestShort"
  putStrLn $ show   shellSortTestShort ++ "   Test.Sorter.shellSortTestShort"
  putStrLn $ show (shellSortTest ll) ++ "   Test.Sorter.shellSortTest"
