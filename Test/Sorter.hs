module Test.Sorter where
import Control.Monad.Identity

import qualified Circuit.Sorter as CS


batcherSortTest :: Ord a => [a] -> Bool
batcherSortTest l = sorted l' where
  l' = runIdentity $ CS.sort swp l
  swp a b = return $ if a<=b then (a,b) else (b,a)

sorted [] = True
sorted [x] = True
sorted (x:y:l) = (x<=y) && sorted (y:l)

runTests = putStrLn $ show $ batcherSortTest [4,2,6,34,5,8,2,4,6]
