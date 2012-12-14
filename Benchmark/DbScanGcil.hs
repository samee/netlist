
import Control.Monad
import Data.Map as M

import Benchmark.Util
import Circuit.NetList
import Circuit.NetList.Gcil
import Util

-- This version of DBSCAN does not return core vs non-core point records
-- Return value assigns each input data point to a cluster index, starting with
-- 1. Cluster index 0 means outlier. Also returns the total cluster count

dbscan :: (a -> a -> Bool) -> Int -> [a] -> ([Int],Int)
dbscan neighbor minpts l = aux (zip [0..] l) M.empty 0 where
  aux [] clus cc = (M.elems clus,cc)
  aux ((i,x):ps) clus cc 
    | M.member i clus = aux ps clus cc
    | nc < minpts     = aux ps (M.insert i 0 clus) cc
    | otherwise       = cc' `seq` aux ps clus' cc'
    where
    nc = length ne
    ne = [j | (j,x') <- zip [0..] l, neighbor x x']
    cc' = cc+1
    clus' = dbscanExpand neighbor minpts clus cc' l i

-- Assumes initKey is not an outlier
dbscanExpand neighbor minpts clusInit cc l initKey = aux clusInit [initKey]
  where
  asc = zip [0..] l
  aux clus [] = clus
  aux clus (i:is)
    | M.member i clus = aux clus  is
    | nc < minpts     = aux clus' is
    | otherwise       = aux clus' $ ne++is
    where
    clus' = M.insert i cc clus
    ne = [j | (j,x) <- asc, i/=j, neighbor x curx]
    nc = length ne
    curx = l!!i

-- The same depth-first algorithm presented above is now a circuit below
-- For more info, look at circitizeDbscan.txt

-- 'emptystk' here is just a hack into the type system, so that I can
--   specify the internal stack type being used when calling the function
-- TODO put an O(n) stack length cap with a "pushed" flag?
dbscanGcil emptystk neighbor minpts l = do
  let cc = constInt 0
      outerLoop = netTrue
      i = constIntW (indexSize n) 0
      stk = emptystk
      cluster = replicate n i

  (cluster,cc,_,_,_) <- foldM (\(cluster,cc,outerLoop,i,stk) _ -> do
    startExpand <- do c1 <- greaterThan (constInt n) i
                      c2 <- equal (constInt 0) =<< muxList i cluster
                      netAnds [outerLoop,c1,c2]
    checkNeighbor <- return startExpand
    cp <- return i
    stopExpand <- bind2 netAnd (netNot outerLoop) (stkNull stk)
    outerLoop' <- netOr outerLoop stopExpand
    i <- condAdd stopExpand i (constInt 1)
    keepExpand <- netXor stopExpand =<< netNot outerLoop
    -- fromJust could have been avoided FIXME
    cur <- liftM netFromJust $ stkTop stk  
    stk <- stkCondPop keepExpand stk
    unvisited <- netAnd keepExpand 
              =<< equal (constInt 0) =<< muxList cur cluster
    cluster <- naiveListWrite unvisited cur cc cluster
    checkNeighbor <- netOr checkNeighbor unvisited
    cp <- mux unvisited cp cur

    closeVec <- mapM (neighbor cp) l
    nc <- countTrue closeVec
    pc <- netAnd checkNeighbor =<< greaterThan nc (constInt $ minpts-1)
    stk <- foldM (\stk (x,c) -> do c' <- netAnd c pc
                                   stkCondPush c' x stk) stk l
    startExpand2 <- netAnd outerLoop pc
    cc <- condAdd startExpand2 cc (constInt 1)
    outerLoop' <- netAnd outerLoop' =<< netNot startExpand2

    return (cluster,cc,outerLoop',i,stk)
    ) (cluster,cc,outerLoop,i,stk) [1..2*n]
  return (cluster,cc)

  where n = length l

-- TODO eyeball this a little longer with circitize by the side
-- Make a new data maker. Fix data range. Run, debug, collect data.

-- TODO this part needs to go in some kind of a Utility file, useful only for
--   benchmarking
netDiff a b = do c <- greaterThan a b
                 bind2 (mux c) (sub b a) (sub a b)

dist p1 p2 = do bind2 add (netDiff (fst p1) (fst p2)) 
                          (netDiff (snd p1) (snd p2))

-- Counts in a convoluted way to reduce bitwidths as much as possible
countTrue :: [NetBool] -> NetWriter NetUInt
countTrue [] = return (constIntW 1 0)
countTrue l 
  | Just (h,t) <- oddLength = do zo <- liftM intFromBits $ bitify h
                                 add zo =<< countTrue t
  | otherwise = do r1 <- countTrue t1
                   r2 <- countTrue t2
                   add r1 =<< extendBy 1 r2
  where
  n = length l
  half = n `div` 2
  (t1,t2) = splitAt half l
  oddLength | odd (length l) = Just (head l, tail l)
            | otherwise = Nothing


main = return ()
