module Test.StackDimacs where

import Control.Monad

import Circuit.NetList
import Circuit.NetList.Dimacs
import qualified Circuit.Stack as CS
import Util

intW = 8
sumW = 16

sumToZeroFast l = liftM fst $ foldM (\(s,done) v -> do
  done <- netOr done =<< equal (constInt 0) v
  s <- add s =<< mux done v (constInt 0)
  return (s,done)) ((constIntW sumW 0),netFalse) l

sumToZero l = liftM fst $ foldM (\(s,stk) _ -> do
                            mbtop <- CS.top stk
                            if knownNothing mbtop 
                               then return (s,stk)
                               else do
                                 let t = netFromJust mbtop 
                                 c <- netNot =<< equal (constInt 0) t
                                 s <- add s t
                                 stk <- CS.condPop c stk
                                 return (s,stk)
                            ) (constIntW sumW 0, CS.fromList l) [1..n]
  where n = length l

sumToZeroSlow l = liftM fst $ foldM (\(s,done) i -> do
  v <- muxList (constIntW (indexSize n) i) l
  done <- netOr done =<< equal (constInt 0) v
  s <- add s =<< mux done v (constInt 0)
  return (s,done)) ((constIntW sumW 0),netFalse) [0..n-1]
  where n = length l

sumAll [] = return (constIntW sumW 0)
sumAll (x:xs) = do s <- sumAll xs
                   add s x

localSumToZero = sum . takeWhile (/=0)

dmWords l = foldr (\x acc -> x-|-" "-|-acc) (dmShow "") l

sumSolve summer prefLo prefHi fullLo n = do
  inputs <- replicateM n (freshInt intW)
  forM_ inputs $ \x -> dmAssert <=< liftNet $ greaterThan (constInt $ n+1) x
  dmPutStrLn $ dmWords inputs
  dmAssert <=< liftNet $ do
    prefixSum <- summer (inputs :: [NetUInt])
    fullSum <- sumAll inputs
    c1 <- netNot =<< greaterThan (constInt prefLo) prefixSum
    c2 <- netNot =<< greaterThan prefixSum (constInt prefHi)
    c3 <- netNot =<< greaterThan (constInt fullLo) fullSum
    netAnds [c1,c2,c3]

runTests = burnSatQuery "sumSolve" <=< dimacsList 
             $ sumSolve sumToZeroSlow 1000 1000 5000 200
