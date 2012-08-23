module Util where

import Control.Monad
import Control.Monad.ST
import Data.Array as A
import Data.Array.ST
import Data.Bits
import Data.STRef
import Debug.Trace
import System.Random

mapAccumM :: Monad m => (c -> a -> m (c,b)) -> c -> [a] -> m (c,[b])
mapAccumM f init xs = do
  (acc,rev) <- foldM (\(acc,ys) x -> do
                        (acc',y) <- f acc x
                        return (acc',y:ys)) (init,[]) xs
  return (acc, reverse rev)

mapWithIndexM :: Monad m => (Int -> a -> m b) -> [a] -> m [b]
mapWithIndexM f as =
  liftM snd $ mapAccumM (\i a -> do r <- f i a; return (i+1,r)) 0 as

indexSize 0 = 0
indexSize 1 = 0
indexSize x = 1 + indexSize ((x+1) `div` 2)

valueSize 0 = 1
valueSize x = indexSize (x+1)

-- Note: 0 return True
isPowerOf2 x = x .&. (x-1) == 0

powerOf2Le x | isPowerOf2 x = x
             | otherwise = powerOf2Le (x .&. (x-1))

powerOf2Lt x | isPowerOf2 x = x `div` 2
             | otherwise = powerOf2Le x

-- Divides l into n parts as evenly as it can
divideList n l  | n == 0    = []
                | len <= sz = [l]
                | otherwise = tk : divideList (n-1) dr
  where
  len = length l
  sz  = len `div` n
  (tk,dr) = splitAt sz l

splitOddEven [] = ([],[])
splitOddEven [x] = ([x],[])
splitOddEven (x:y:l) = (x:xs,y:ys) where (xs,ys) = splitOddEven l

inversePermute l = A.elems inv where
  n = length l
  inv = A.array (0,n-1) $ map (\i -> (arr ! i,i)) [0..n-1]
  arr = listArray (0,n-1) l

randomPermute :: RandomGen g => g -> [Int] -> [Int]
randomPermute rgen x = runST $ do
    g   <- newSTRef rgen
    arr <- newArray x
    let newInd st = do
          (i,rgen') <- liftM (randomR (st,n-1)) (readSTRef g)
          writeSTRef g rgen'
          return i
    forM [0..n-1] $ \i -> do
      j <- newInd i
      p <- readArray arr i
      q <- readArray arr j
      writeArray arr j p
      return q
  where n = length x
        newArray :: [Int] -> ST s (STUArray s Int Int)
        newArray x = newListArray (0,length x-1) x


traceme x = traceShow x x

