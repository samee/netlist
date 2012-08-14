module Util where

import Control.Monad
import Data.Bits
import Debug.Trace

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

traceme x = traceShow x x

