import Control.Monad
import Data.List
import System.Random

import Circuit.NetList
import Circuit.NetList.Gcil
import qualified Circuit.Sorter
import Util

{-

Storytime: two team of athletes from two different countries will compete in
  this big upcoming competition.  The make up of their team is still secret.
  However, the two want to see how their teams compare against each other. Their
  comparison metric is as follows: they sort the atheletes of their respective
  teams by their average running speeds. Then they compare the fastest of one
  team vs fastest of the other, the 2nd fastest of one vs the 2nd fastest of
  the other, etc. Finally, they want a frequency list of these speed 
  differences. E.g., in these comparisons, we saw a speed difference of +10 m/s
  4 times, +5 m/s 9 times, -5 m/s 20 times etc.
-}

outputBlinded mb | knownNothing mb = return ()
                 | otherwise = do 
                    np <- netIsNothing mb
                    (d,f) <- mux np (netFromJust mb) (constInt 0, constInt 0)
                    newOutput =<< bitify np
                    newOutput =<< bitify d
                    newOutput =<< bitify f

swapIfGreater a b = do c <- greaterThan a b
                       condSwap c a b

nothingIsGreater ja jb = do pa <- netIsNothing ja
                            pb <- netIsNothing jb
                            c  <- netAnd pa =<< netNot pb
                            condSwap c ja jb

adjSweep :: Monad m => (a -> a -> m(a,a)) -> [a] -> m [a]
adjSweep _ [] = return []
adjSweep _ [a] = return [a]
adjSweep f (a1:a2:a) = do (a1',a2') <- f a1 a2
                          liftM (a1':) $ adjSweep f (a2':a)

-- It is standard practice to blind netMaybe output values
speedDifferences :: [NetSInt] -> [NetSInt] 
                 -> NetWriter [NetMaybe (NetSInt,NetUInt)]
speedDifferences a b = do
  -- Assume they are sorted
  d <- forM (zip a b) $ \(a,b) -> sub a b
  d <- Circuit.Sorter.sort swapIfGreater d
  fscattered <- adjSweep adjSum $ map justOne d
  -- For no apparent reason, I felt like sorting this here :-/
  Circuit.Sorter.sort nothingIsGreater fscattered
  where
  w = valueSize $ length a
  justOne x = netJust (x, constIntW w 1)

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

speedDifferencesBad :: [NetSInt] -> [NetSInt] 
                    -> NetWriter [NetMaybe (NetSInt,NetUInt)]
speedDifferencesBad a b = do
  -- Assume they are sorted
  d <- forM (zip a b) $ \(a,b) -> sub a b
  foldM addDfPairs init d
  where
  w = valueSize $ length a
  init = replicate (length a) netNoth
  addDfPairs pairList d = cursorSweep addStep (netJust d) pairList
  addStep :: NetMaybe NetSInt -> NetMaybe (NetSInt,NetUInt)
          -> NetWriter (NetMaybe NetSInt, NetMaybe (NetSInt,NetUInt))
  addStep mbD mbPair 
    | knownNothing mbD    = return (mbD, mbPair)
    | knownNothing mbPair = return ( netNoth
                                   , netJust(netFromJust mbD,constIntW w 1))
    | otherwise = do
        case1'<- netNot =<< netIsNothing mbD
        case2 <- netAnd case1' =<< netIsNothing mbPair
        case3 <- bind2 netAnd (netXor case1' case2) (equal d pd)
        pf'   <- condAdd case3 (constInt 1) pf
        op    <- netOr case2 case3
        mbD'  <- condZap op mbD
        mux op (mbD,mbPair) (mbD',netJust (pd,pf'))
        where
        d = netFromJust mbD
        (pd,pf) = netFromJust mbPair

  -- if mbD is Nothing -> mbPair, mbD
  -- else if pbPair is Nothing -> (d,1), Nothing
  -- else if d==pair.d -> (d,pair.f+1), Nothing
  -- else -> mbPair, mbD
  
randomList _ 0 rgen = ([],rgen)
randomList ulim n rgen = (aux n rgen1, rgen2) where
  (rgen1,rgen2) = System.Random.split rgen
  aux 0 _ = []
  aux n rg = x : aux (n-1) rg' where (x,rg') = randomR (0,ulim-1) rg

randomSortedList ulim n rgen = (sort l,rgen') where
  (l,rgen') = randomList ulim n rgen

mkcktSpeedDiff calc w a b = do
  av <- mapM (testInt ServerSide w) a
  bv <- mapM (testInt ClientSide w) b
  dfpairs <- liftNet $ calc av bv
  liftNet $ forM dfpairs outputBlinded

main = forM [16,32,64,128,256,512] $ \sz -> do
         a <- getStdRandom $ randomSortedList (2^16) sz
         b <- getStdRandom $ randomSortedList (2^16) sz
         burnBenchmark ("speedGood"++show sz)
           $ mkcktSpeedDiff speedDifferences 16 a b
         burnBenchmark ("speedBad"++show sz)
           $ mkcktSpeedDiff speedDifferencesBad 16 a b
