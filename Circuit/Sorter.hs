module Circuit.Sorter (sort,merge,CmpSwap) where
import Control.Monad
import Data.Bits
import Debug.Trace

import Util

type CmpSwap m a = a -> a -> m (a,a)

sort :: Monad m => CmpSwap m a -> [a] -> m [a]
sort  = batcherSort

merge :: Monad m => CmpSwap m a -> [a] -> [a] -> m [a]
merge = batcherMerge

splitHalf l = splitAt hlen l where hlen = length l `div` 2

batcherSort _ [] = return []
batcherSort _ [x] = return [x]
batcherSort cmpSwap l = do
  let (h1,h2) = splitHalf l
  h1 <- batcherSort cmpSwap h1
  h2 <- batcherSort cmpSwap h2
  batcherMerge cmpSwap h1 h2

batcherMerge _ [] b = return b
batcherMerge cmpSwap [a] [b] = do (a,b) <- cmpSwap a b; return [a,b]
batcherMerge cmpSwap a b = do
  let (ae,ao) = splitOddEven a; (be,bo) = splitOddEven b
  ce <- batcherMerge cmpSwap ae be
  co <- batcherMerge cmpSwap ao bo
  batcherSwap cmpSwap (unsplitOddEven ce co)

batcherSwap _ []  = return []
batcherSwap _ [x] = return [x]
batcherSwap cmpSwap (x:y:l) = do
  (x,y) <- cmpSwap x y
  liftM (x:) $ batcherSwap cmpSwap (y:l)

unsplitOddEven [] y = y
unsplitOddEven x [] = x
unsplitOddEven (x:xs) (y:ys) = x:y:unsplitOddEven xs ys 

