module Test.SorterNative where
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
longList rgen = (take 2000 full,rgen2) where
  (rgen1,rgen2) = split rgen
  full = randomRs (0,100) rgen1 :: [Int]

batcherSortTestShort = batcherSortTest shortList
shellSortTestShort = shellSortTest shortList

shortTests = do
  ll <- getStdRandom longList
  let tests = [(batcherSortTestShort, "batcherSortTestShort")
              ,(batcherSortTest   ll, "batcherSortTest"     )
              ,(  shellSortTestShort,   "shellSortTestShort")
              ,(    shellSortTest ll,   "shellSortTest"     )
              ]
  status <- liftM and $ forM tests $ \(testproc, testname) -> do
    putStrLn $ show testproc ++ "   " ++ testname
    return testproc
  putStrLn $ "Tests "++if status then "passed" else "failed"

longTests = putStrLn "Tests passed"
