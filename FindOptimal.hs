module Main where
import Control.Monad
import Util

bitonicSwapCount x = x `div` 2
bitonicMergeCount x = if x <= 1 then 0
                      else bitonicSwapCount x + bitonicMergeCount h
                                              + bitonicMergeCount (x-h)
  where h = x `div` 2

bitonicSortCount x =  if x<=1 then 0 
                      else bitonicSortCount h + bitonicSortCount (x-h)
                            + bitonicMergeCount x
  where h = x `div` 2

batcherSwapCount 0 = 0
batcherSwapCount x = x-1

batcherMergeCount x y | y == 0 || x ==0 = 0
                      | x == 1 && y == 1 = 1
                      | otherwise 
  = batcherMergeCount (div (x+1) 2) (div (y+1) 2) 
  + batcherMergeCount (div x 2) (div y 2)
  + batcherSwapCount (x+y)

batcherSortCount x  | x<=1 = 0
                    | otherwise = batcherSortCount h
                                + batcherSortCount (x-h)
                                + batcherMergeCount h (x-h)
                    where h = x `div` 2

-- Assumes first h is sorted already
batcherHalfSort h x | x <= 1 = 0
                    | h >= x = 0
                    | h <= 0 = batcherSortCount x
                    | otherwise = batcherHalfSort h mid
                                + batcherHalfSort (h-mid) (x-mid)
                                + batcherMergeCount mid (h-mid)
                    where mid = div x 2

{-
indexSize 0 = 0
indexSize 1 = 0
indexSize x = 1 + indexSize ((x+1)`div`2)
-}

-- x : op cost
-- t : op count
-- n : array size
-- w : array element width in bits

arrayBatchOpCost x t n w = sortOps + merge + doOps + unzip
  where
  sortOps = bitonicSortCount t * taggedPair
  merge = bitonicMergeCount (t+n) * taggedPair
  doOps = (x+logn)*(n+t)
  unzip = bitonicSortCount (n+t) * (1+w+max logt logn) -- bit reuse in doOps
  logt = indexSize t
  logn = indexSize n
  taggedPair = 1 + logt + logn

arrayBatchReadCost x t n w = sortOps + doOps + unzip
  where
  sortOps = batcherHalfSort (n+t) n * (logn+1 + mixSize)
  doOps = (n+t-1)*(1+logt+w+w)
  unzip = batcherSortCount (n+t) * (1+logt + 1+logt+w)
  logn = indexSize n
  logt = indexSize t
  mixSize = 1 + logn + (max logt w)

oldReadCost n w = (n-1)*w

arrayBatchWriteCost x t n w = sortOps + doOps + unzip
  where
  sortOps = batcherHalfSort (n+t) n * (2*logn+2*logt+w)
  doOps = (n+t-1)*(logn + 1+logn+w + w)
  unzip = batcherSortCount (n+t) * (logn+1+logn+w)
  logn = indexSize n
  logt = indexSize t

decoderCost i o | i<=1    = 0
                | o>r-i-1 = decoderCost i (r-i-1)
                | True    = min (rh-1) o + decoderCost (i-1) (2*o)
                where r = 2^i; rh = 2^(i-1)

oldWriteCost n w = decoderCost logn n+n*w where logn = indexSize n

minarg :: Ord b => [a] -> (a->b) -> a
minarg [] _ = undefined
minarg (arg:args) f = aux args f (arg,f arg) where
  aux [] _ (i,_) = i
  aux (a:as) f (i,res) = i' `seq` aux as f (i',res') where
    (i',res') = if cur < res then (a,cur) else (i,res)
    cur = f a


searchBreadth = 20

-- starts search in a range, proceeds if range is saturated. Positive ints only
minArgR :: Ord b => Int -> Int -> (Int->b) -> Int
minArgR lo hi f | lo < 1 = minArgR 1 hi f
                | minPoint == 1 = 1
                | minPoint == lo = minArgR (lo-searchBreadth) lo f
                | minPoint == hi = minArgR hi (hi+searchBreadth) f
                | otherwise = minPoint
                where minPoint = minarg [lo..hi] f

minTdescend init n w = (tres, f tres, oldWriteCost n w)
  where tres = minArgR (init-searchBreadth) (init+searchBreadth) f
        f t = fromIntegral (arrayBatchWriteCost 0 t n w)/fromIntegral t
{-
minT :: Fractional a => Int -> Int -> Int -> (Int, a, Int)
minT x n w = (tres,f tres, oldReadCost n w)
  where tres = minarg [lo..hi] f
        f t = fromIntegral (arrayBatchReadCost x t n w)/fromIntegral t
        lo = n
        hi = 3*n
-}
main =
  putStrLn $ show $ arrayBatchReadCost 0 50 50 16 {-
  let w = 16; x = 16 in
  foldM_ (\prev n -> do
    let fields@(minpoint,_,_) = minTdescend prev n w
    putStrLn $ show n ++ "  " ++ show fields
    return minpoint) 1 [1..1000]
    -- -}
