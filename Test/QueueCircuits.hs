module Test.QueueCircuits (runTests) where

import Control.Monad
import Control.Monad.State
import Data.Bits
import Data.Sequence (Seq,ViewR((:>)),(<|))
import qualified Data.Sequence as S
import Debug.Trace
import System.Random

--import Circuit.Gcil.Compiler as Gc
--import Circuit.Gcil.Queue as Gq
import Circuit.NetList
import Circuit.NetList.Gcil as Gc
import Circuit.Queue as Gq
--import Test.Gcil (writeTestCase)
import Util

data QueueAction = QueuePush Int | QueuePop Int deriving Show

-- Push/pop only one-byte integers
intW = 8
maxTestInt = 2^intW - 1

randomTest :: RandomGen g => Int -> Int -> g -> ([QueueAction],g)
randomTest opCount maxlen rgen = runState (aux S.empty opCount) rgen 
  where
  aux :: RandomGen g => Seq Int -> Int -> State g [QueueAction]
  aux _ 0 = return []
  aux q opCount = do
    rlen <- state $ randomR (0,maxlen)
    (q,acts) <- if len<rlen then pushRandom (Prelude.min opCount $ rlen-len) q
                else popRandom (Prelude.min opCount $ len-rlen) q
    liftM (acts++) $ aux q (opCount-length acts)

    where
    len = S.length q

pushRandom 0 q = return (q,[])
pushRandom n q = do
  x <- state $ randomR (0,maxTestInt)
  (q,acts) <- pushRandom (n-1) (x<|q)
  return (q, QueuePush x:acts)

popRandom 0 q = return (q,[])
popRandom n q = do
  let q1 :> x = S.viewr q
  (q2,acts) <- popRandom (n-1) q1
  return (q2, QueuePop x:acts)

compileActs maxQLength acts = do
  pushVars <- mapM (testInt ServerSide intW) pushVals
  popVars  <- mapM (testInt ClientSide intW) popVals
  res <- cktMain pushVars popVars acts $ Gq.capLength maxQLength Gq.empty
  gcilOutBits res -- =<< liftNet (bitify res)
  where
  (pushVals,popVals) = splitPushPop acts

  cktMain :: [NetUInt] -> [NetUInt] -> [QueueAction] -> Queue NetUInt
          -> GcilMonad NetBool
  cktMain [] [] [] _ = return netTrue
  cktMain (x:a) b (QueuePush _:acts) q = do
    q'<- liftNet $ Gq.condPush netTrue x q
    cktMain a b acts q'
  cktMain a (x:b) (QueuePop _:acts) q = do
    mb <- liftNet $ Gq.front q
    q'<- liftNet $ Gq.condPop netTrue q
    r <- cktMain a b acts q'
    ignoreAndsUsed $ liftNet $ do
      b  <- netNot =<< netIsNothing mb
      eq <- equal (netFromJust mb) x
      netAnds [r,b,eq]

splitPushPop [] = ([],[])
splitPushPop (QueuePush x: l) = (x:a,b) where (a,b) = splitPushPop l
splitPushPop (QueuePop  x: l) = (a,x:b) where (a,b) = splitPushPop l

ceilPowerOf2 x | isPowerOf2 x = x
               | otherwise = x + (x .&. ( -x ))

data SimpleQueue a = SimpleQueue { sqContents :: [a]
                                 , sqHead :: NetUInt
                                 , sqTail :: NetUInt
                                 , sqMaxLen :: Int
                                 }

simpleEmpty maxl = SimpleQueue { sqContents = []
                               , sqHead = constIntW w 0
                               , sqTail = constIntW w 0
                               , sqMaxLen = ceilPowerOf2 maxl
                               } where
                               w = indexSize maxl

sqPush c v q = do
  let oldlen = length $ sqContents q
      (newlen,oldbuff) = if oldlen == sqMaxLen q
                           then (oldlen,sqContents q) 
                           else (oldlen+1,sqContents q ++ [v])
  dec <- decoderREn c 0 newlen (sqTail q)
  newbuff <- forM (zip dec $ oldbuff) $ \(d,old) -> mux d old v
  newtail <- condAdd c (sqTail q) (constInt 1)
  return $ q { sqContents = newbuff, sqTail = newtail }

sqPop c q = do
  newhead <- condAdd c (sqHead q) (constInt 1)
  return $ q { sqHead = newhead }

sqFront q = muxList (sqHead q) (sqContents q)

-- TODO did I ever tell you how I hate code duplication?
queueCount maxn acts = countGates $ gcilList $ compileActs maxn acts
naiveCount maxn acts = countGates $ gcilList $ do
  pushVars <- mapM (testInt ServerSide intW) pushVals
  popVars  <- mapM (testInt ClientSide intW) popVals
  cktMain pushVars popVars acts (simpleEmpty maxn)
  where
  (pushVals,popVals) = splitPushPop acts

  cktMain :: [NetUInt] -> [NetUInt] -> [QueueAction] -> SimpleQueue NetUInt
          -> GcilMonad ()

  cktMain [] [] [] _  = return ()
  cktMain (x:a) b (QueuePush _:acts) q = do
    q' <- liftNet $ sqPush netTrue x q
    cktMain a b acts q'
  cktMain a (x:b) (QueuePop _:acts) q = do
    mb <- liftNet $ sqFront q
    q' <- liftNet $ sqPop netTrue q
    cktMain a b acts q'

qsize = 200

{-
runTests = getStdRandom (randomTest 2000 qsize) 
       >>= burnTestCase "queuetest" . gcilList . compileActs qsize
       -}

runTests = do putStrLn "-------------- Queue sizes ------------------"
              putStrLn "n opcount Naive(total,and) MyQueue(total,and)"
              forM_ [16,32,64,128,256,512,1024,2048] $ \maxl ->
                forM_ [maxl `div` 2, maxl, maxl*2] $ \opcount -> do
                  acts <- getStdRandom $ randomTest opcount maxl
                  putStrLn $ show maxl ++ "  " ++ show opcount ++ "  "
                          ++ show (naiveCount maxl acts) ++ "  " 
                          ++ show (queueCount maxl acts)



