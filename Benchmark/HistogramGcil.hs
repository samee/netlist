import Control.Monad
import Data.List
import System.Random

import Circuit.NetList
import Circuit.NetList.Gcil
import qualified Circuit.Sorter
import Util

{-

I want to make a histogram of X[i] values.
  The data is stored by two different parties in shares A[i], B[i]
  such that X[i]=A[i]+B[i]
  The code I want to run:
  for(i=0;i<n;++i) count[A[i]+B[i]]++;

-}

outputBlinded mb | knownNothing mb = return ()
                 | otherwise = do 
                    np <- netIsNothing mb
                    (d,f) <- mux np (netFromJust mb) (constInt 0, constInt 0)
                    void $ do
                      newOutput =<< bitify np
                      newOutput =<< bitify d
                      newOutput =<< bitify f

swapIfGreater a b = do c <- greaterThan a b
                       condSwap c a b

swapIfGreater2 (a1,a2) (b1,b2) = do c <- greaterThan a2 b2
                                    c <- chainGreaterThan c a1 b1
                                    condSwap c (a1,a2) (b1,b2)

nothingIsGreater ja jb = do pa <- netIsNothing ja
                            pb <- netIsNothing jb
                            c  <- greaterThan (fst $ netFromJust ja)
                                              (fst $ netFromJust jb)
                            c  <- chainGreaterThan c pa pb
                            condSwap c ja jb

adjSweep :: Monad m => (a -> a -> m(a,a)) -> [a] -> m [a]
adjSweep _ [] = return []
adjSweep _ [a] = return [a]
adjSweep f (a1:a2:a) = do (a1',a2') <- f a1 a2
                          liftM (a1':) $ adjSweep f (a2':a)

type UIntSorter = [NetUInt] -> NetWriter [NetUInt]

-- It is standard practice to blind netMaybe output values (done later)
sumFreqsCustomSort :: UIntSorter -> [NetUInt] -> [NetUInt]
                   -> NetWriter [NetMaybe (NetUInt,NetUInt)]
sumFreqsCustomSort firstSort a b = do
  -- Assume they are sorted
  ss <- firstSort <=< forM (zip a b) $ \(a,b) -> add a b
  fscattered <- adjSweep adjSum $ map justOne ss
  -- For no apparent reason, I felt like sorting this here :-/
  Circuit.Sorter.sort nothingIsGreater fscattered
  where
  w = valueSize $ length a
  justOne s = netJust (s, constIntW w 1)

sumFreqs = sumFreqsCustomSort $ Circuit.Sorter.sort swapIfGreater
sumFreqsStable = sumFreqsCustomSort stableSort

-- FIXME this is why CmpSwap should have *separate* functions for compare 
--  and swap. I could have made a general function for stableSort
stableSort :: [NetUInt] -> NetWriter [NetUInt]
stableSort l = liftM (map fst) $ Circuit.Sorter.sort swapIfGreater2 pairs
  where
  w = indexSize $ length l
  pairs = zip l $ map (constIntW w) [0..] :: [(NetUInt,NetUInt)]


adjSum ja jb = do keySame <- equal d1 d2
                  sum <- add f1 f2
                  ra  <- condZap keySame ja
                  f2' <- condAdd keySame f2 f1
                  return (ra, netJust(d2,f2'))
                  where
                  (d1,f1) = netFromJust ja
                  (d2,f2) = netFromJust jb

-- Doesn't handle short lists well
cursorSweep :: Monad m => (a -> b -> m(a,b)) -> a -> [b] -> m [b]
cursorSweep _ _ [] = return []
cursorSweep f a (b:bs) = do (a',b') <- f a b
                            liftM (b':) $ cursorSweep f a' bs

sumFreqsNaive :: [NetUInt] -> [NetUInt] 
              -> NetWriter [NetMaybe (NetUInt,NetUInt)]
sumFreqsNaive a b = do
  -- Assume they are sorted
  s <- forM (zip a b) $ \(a,b) -> add a b
  foldM addKvPairs init s
  where
  w = valueSize $ length a
  init = replicate (length a) netNoth
  addKvPairs pairList s = cursorSweep addStep (netJust s) pairList
  addStep :: NetMaybe NetUInt -> NetMaybe (NetUInt,NetUInt)
          -> NetWriter (NetMaybe NetUInt, NetMaybe (NetUInt,NetUInt))
  addStep mbS mbPair 
    | knownNothing mbS    = return (mbS, mbPair)
    | knownNothing mbPair = return ( netNoth
                                   , netJust(netFromJust mbS,constIntW w 1))
    | otherwise = do
        case1'<- netNot =<< netIsNothing mbS
        case2 <- netAnd case1' =<< netIsNothing mbPair
        case3 <- bind2 netAnd (netXor case1' case2) (equal s ps)
        pf'   <- condAdd case3 (constInt 1) pf
        op    <- netOr case2 case3
        mbS'  <- condZap op mbS
        mbPair' <- mux op mbPair (netJust (s,pf'))
        return (mbS',mbPair')
        where
        s = netFromJust mbS
        (ps,pf) = netFromJust mbPair

  -- if mbS is Nothing -> mbPair, mbS
  -- else if pbPair is Nothing -> (s,1), Nothing
  -- else if s==pair.s -> (s,pair.f+1), Nothing
  -- else -> mbPair, mbS
  
randomList _ 0 rgen = ([],rgen)
randomList ulim n rgen = (aux n rgen1, rgen2) where
  (rgen1,rgen2) = System.Random.split rgen
  aux 0 _ = []
  aux n rg = x : aux (n-1) rg' where (x,rg') = randomR (0,ulim-1) rg

-- Warning: sorted versions of uniformly randomly selected lists have
--   different distributions compared to a uniformly randomly selected
--   sorted list. Then again, since our runtimes do not depend on private
--   inputs, So who cares!
randomSortedList ulim n rgen = (sort l,rgen') where
  (l,rgen') = randomList ulim n rgen

mkcktSumFreqs calc w a b = do
  av <- mapM (testInt ServerSide w) a
  bv <- mapM (testInt ClientSide w) b
  dfpairs <- liftNet $ calc av bv
  liftNet $ forM dfpairs outputBlinded

main = forM [16,32,64,128,256,512] $ \sz -> do
         a <- getStdRandom $ randomSortedList (2^16) sz
         b <- getStdRandom $ randomSortedList (2^16) sz
         burnBenchmark ("speedGood"++show sz)
           $ mkcktSumFreqs sumFreqs 16 a b
         burnBenchmark ("speedBad"++show sz)
           $ mkcktSumFreqs sumFreqsNaive 16 a b
         burnBenchmark ("speedStable"++show sz)
           $ mkcktSumFreqs sumFreqsStable 16 a b
