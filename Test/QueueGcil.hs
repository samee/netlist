module Test.QueueGcil where

import Control.Monad
import Control.Monad.State
import Data.Bits
import Data.Sequence (Seq,ViewR((:>)),(<|))
import qualified Data.Sequence as S
import Debug.Trace
import System.Random

import Circuit.NetList
import Circuit.NetList.Gcil as Gc
import Circuit.Queue as Gq
import Test.Util.Simple
import Util

data QueueAction = QueuePush Int | QueuePop Int deriving Show

-- Push/pop only one-byte integers
intW = 16
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

compileActs emptyQ maxQLength acts = do
  pushVars <- mapM (testInt ServerSide intW) pushVals
  popVars  <- mapM (testInt ClientSide intW) popVals
  cktMain pushVars popVars acts $ qCapLength maxQLength emptyQ
  where
  (pushVals,popVals) = splitPushPop acts

  cktMain :: QueueType q => [NetUInt] -> [NetUInt] -> [QueueAction] -> q NetUInt
          -> GcilMonad NetBool
  cktMain [] [] [] _ = return netTrue
  cktMain (x:a) b (QueuePush _:acts) q = do
    q'<- liftNet $ qCondPush netTrue x q
    cktMain a b acts q'
  cktMain a (x:b) (QueuePop _:acts) q = do
    mb <- liftNet $ qFront q
    q'<- liftNet $ qCondPop netTrue q
    r <- cktMain a b acts q'
    ignoreAndsUsed $ liftNet $ do
      b  <- netNot =<< netIsNothing mb
      eq <- equal (netFromJust mb) x
      netAnds [r,b,eq]

splitPushPop [] = ([],[])
splitPushPop (QueuePush x: l) = (x:a,b) where (a,b) = splitPushPop l
splitPushPop (QueuePop  x: l) = (a,x:b) where (a,b) = splitPushPop l

shortTests = getStdRandom (randomTest 200 qsize) 
         >>= burnTestCase "queuetest" . compileActs Gq.empty qsize
  where qsize = 100

longTests = getStdRandom (randomTest 2000 qsize)
         >>= burnTestCase "queueLongTest" . compileActs Gq.empty qsize
  where qsize = 200
