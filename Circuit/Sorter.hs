module Circuit.Sorter (sort,merge,CmpSwap,batcherSort,shellSort) where
import Control.Monad
import Data.Bits
import Debug.Trace

import Util hiding (inversePermute)

-- Included for Randomized Shellsort
import Data.Array
import Data.Array.ST
import Data.STRef
import System.Random as R

type CmpSwap m a = a -> a -> m (a,a)

sort :: Monad m => CmpSwap m a -> [a] -> m [a]
--sort  = batcherSort
sort = shellSort (mkStdGen 3949384)

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


---------------------------- Randomized Shellsort --------------------------

permute inds l = map (arr !) inds where
  arr = listArray (0,length l-1) l

inversePermute inds l = elems $ runSTArray $ permuted l where
  n = length l
  permuted l = do
    arr <- newArray_ (0,n-1)
    forM_ (zip inds l) $ uncurry $ writeArray arr
    return arr

-- Assumes length a >= length b
shellSortCompareRegions :: (RandomGen r,Monad m) =>
                           r -> (a -> a -> m(a,a)) -> [a] -> [a] -> m ([a],[a])
shellSortCompareRegions rgen cmp a b = do
    let (ashuf,atail) = splitAt bn $! permute p a
    (ashuf',b') <- liftM unzip $ mapM (uncurry cmp) $ zip ashuf b
    let a' = inversePermute p $ ashuf' ++ atail
    return (a',b')
  where
  an = length a
  bn = length b
  p = fst $ randomPermute [0..an-1] rgen


splitEach x [] = []
splitEach x (a:as)  | null t    = a:splitEach x as
                    | otherwise = h:splitEach x (t:as) 
                    where (h,t) = splitAt x a

-- Assumes off > 0
forwModify :: Monad m => (a -> a -> m(a,a)) -> Int -> [a] -> m [a]
forwModify f off l = aux [] l where
  aux acc l | null t = return $ reverse acc ++ l
            | otherwise = do
                (h1,t1) <- f (head h) (head t)
                aux (h1:acc) $ (tail h++[t1]++tail t)
            where (h,t) = splitAt off l

flipIO f x y = do (p,q) <- f y x; return (q,p)
backModify f off l = liftM reverse $ forwModify (flipIO f) off $ reverse l

modifyInPairs :: Monad m => (a -> a -> m (a,a)) -> [a] -> m [a]
modifyInPairs _ [] = return []
modifyInPairs _ [x] = return [x]
modifyInPairs f (x1:x2:xs) = do (x1',x2') <- f x1 x2
                                rest <- modifyInPairs f xs
                                return $ x1':x2':xs

skipLoop :: Monad m => Int -> ([a] -> m [a]) -> [a] -> m [a]
skipLoop st f x | null t = return x
                | otherwise = f t >>= return.(h++) where (h,t) = splitAt st x

rgenSplits 0 rgen = [rgen]
rgenSplits i rgen = rgen1:rgenSplits (i-1) rgen2 
  where (rgen1,rgen2) = R.split rgen

{-
shellSort :: (RandomGen g,Monad m)
          => g -> CmpSwap m a -> [a] -> m [a]
          -}
shellSort rgen cmp a = aux rgen (powerOf2Lt $ length a) [a] where
  aux _     0 as' = return $ concat as'
  aux rgen sz as' = do
    let as = splitEach sz as'
        rgens = rgenSplits 6 rgen
    as <- forwModify (shellSortCompareRegions (rgens!!0) cmp) 1 as
    as <- backModify (shellSortCompareRegions (rgens!!1) cmp) 1 as
    as <- forwModify (shellSortCompareRegions (rgens!!2) cmp) 3 as
    as <- forwModify (shellSortCompareRegions (rgens!!3) cmp) 2 as
    as <- modifyInPairs (shellSortCompareRegions (rgens!!4) cmp) as
    as <- skipLoop 1 (modifyInPairs (shellSortCompareRegions (rgens!!5) cmp)) as
    aux (last rgens) (sz `div` 2) as
