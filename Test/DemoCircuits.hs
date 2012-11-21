-- Used only by Test.Demo
module Test.DemoCircuits where

import Control.Monad
import Data.List
import Debug.Trace

import Circuit.Sorter
import Circuit.NetList
import qualified Circuit.Queue as Nq
import qualified Circuit.Stack as Ns
import Util


-- Given a set of points on the circumference of a circle,
-- find the widest angle made by them at the center. All angles are
-- scaled by a factor of maxTheta/(2*pi) to avoid use of floating point
-- Assumes n >= 2, and that theta is sorted in ascending order
{-
Implements the following code, in circuit (why is this still so painful!)
result = 0
j = 0
i = 1
while(i<n)
{
  result = max result (f theta[i] theta[j])
  if ((j<i) && (f theta[i] theta[j] <= modDiff maxTheta theta[i] theta[j+1]))
    j++
  else
    i++
}

Mapping: theta[j+1..i]       -> inRange (Queue, possibly empty)
         f theta[i] theta[j] -> curSep
         theta[i]            -> curi    (same as last item pushed in inRange)
         theta[i+1..n-1]     -> unseen  (Queue, possibly empty)
-}

wideAngle :: [NetUInt] -> NetUInt -> NetWriter NetUInt
wideAngle theta maxTheta = if n <= 1
  then return $ constInt 0
  else do
    let result  = constIntW (intWidth maxTheta) 0
        unseen  = Nq.fromList $ tail $ tail theta
        inRange = Nq.fromList [theta!!1]
        curi    = theta!!1
    curSep <- modDiff maxTheta (theta!!0) (theta!!1)
    (result,_,_,_) <- foldM (\(result,inRange,curSep,curi,unseen) _ -> do
      result <- netMax result curSep
      nextmb <- Nq.front inRange
      (c,curSepj) <- netCaseMaybe (\mb -> case mb of
        Nothing -> return (netFalse,curSep)
        Just nextj -> do nextSep <- modDiff maxTheta nextj curi
                         c <- netNot =<< greaterThan curSep nextSep
                         return (c,nextSep)
        ) nextmb
      mbnexti <- Nq.front unseen
      notdone <- netNot =<< netIsNothing mbnexti
      -- TODO fix fromJust if known nothing
      tb <- netAnd notdone c
      fb <- netXor notdone tb
      inRange <- Nq.condPop tb inRange
      curSep  <- mux tb curSep curSepj
      inRange <- Nq.condPush fb (netFromJust mbnexti) inRange
      curSep  <- mux fb curSep =<< modDiff maxTheta 
      {-
      if c && 
      -}
      return (result,inRange,curSep,curi,unseen)) [1..2*n]





    let result  = constIntW (intWidth maxTheta) 0
        unseen  = Nq.fromList $ tail theta
        inRange = Nq.fromList [theta!!1]
    curSep <- modDiff maxTheta (theta!!0) (theta!!1)
    (result,_,_,_) <- foldM (\(result,inRange,curSep,unseen) _ -> do




      mbcuri   <- Nq.front unseen
      if knownNothing mbcuri then return (result,inRange,curSep,unseen)
      else do
        let curi = netFromJust mbcuri 
        iend     <- netIsNothing mbcuri
        -- FIXME curSep should not change if unseen is empty
        result   <- netMax result curSep
        nextmb   <- Nq.front inRange
        (c,curSep')  <- netCaseMaybe (\mb -> case mb of 
                        Nothing -> return (netFalse,curSep)
                        Just nextj -> do 
                          nextSep <- modDiff maxTheta nextj curi
                          c' <- netNot =<< greaterThan curSep nextSep
                          return (c',nextSep)
                        ) nextmb
        tb      <- netAnd c  =<< netNot iend
        fb      <- netXor tb =<< netNot iend
        inRange <- Nq.condPop tb inRange
        curSep  <- mux tb curSep curSep'
        unseen  <- Nq.condPop fb unseen
        inRange <- Nq.condPush fb curi inRange
        ...
        return (result,inRange,curSep,unseen)
      ) (result,inRange,curSep,unseen) [1..2*n-1]
    return result
  where
  n = length theta
  (firstHalf,secondHalf) = splitAt (n`div`2) theta

-- modDiff m a b assumes a <= b < maxtheta
modDiff m a b = do 
  x <- sub b a
  y <- sub m x
  netMin x y

fold1M f l = foldM f (head l) (tail l)

foldMWithBreak :: Monad m => (a -> b -> m (Maybe a)) -> a -> [b] -> m a
foldMWithBreak f init [] = return init
foldMWithBreak f init (h:t) = do mb <- f init h
                                 case mb of Nothing -> return init
                                            Just x  -> foldMWithBreak f x t

-- Naive O(n^2) comparison
wideAngleNaive theta maxTheta = join $ fold1M (liftM2 netMax) l
  where
  allPair = [(a,b) | (a,bs) <- zip theta (tail $ tails theta), b <- bs]
  l = map (uncurry $ modDiff maxTheta) allPair

-- shiftLeft amt x = bitConcat [x,(constIntW amt 0)]

multiply :: NetUInt -> NetUInt -> NetWriter NetUInt
multiply a b = aux =<< bitify b where
  addop bt = mux bt (constInt 0) a 
  -- = Gc.bitwiseAnd a =<< Gc.sextend awidth (bitToInt bt)
  -- awidth = bitWidth a
  aux b = if bwidth == 1 then addop =<< lsb b
          else do (bt,b') <- splitLsb b
                  s <- shiftLeft 1 =<< aux b'
                  add s =<< addop bt
          where bwidth = bitWidth b
  {-
  aux b = if bwidth == 1 then addop =<< lsb b -- (intToBit b)
                         else do (bt,b') <- splitMsb b
                                 s <- leadz =<< multiply a b'
                                 addU s =<< shiftLeft (bwidth-1) =<< addop bt
        where bwidth = bitWidth b
              leadz x = zextend (bitWidth x + 1) x
              -}
                             
-- TODO stack needs condModifyTop
{-
Stack of (height,startx) pair

Add zeroes to both sides

if top shorterThan current, push (current.x,current.h), i++
if top sameHeightAs current, i++
if top tallerThan current, updateWith (current.x-top.x)*top.h, pop
  -}
rectangleInHistogram :: [NetUInt] -> NetWriter NetUInt
rectangleInHistogram heights = do
  (best,_,_,_) <- foldMWithBreak (\(best,heightsLeft,ascStack,nxLeftEnd) _ -> do
    mbcur <- Ns.top heightsLeft
    if knownNothing mbcur then return Nothing
    else liftM Just $ do
      mbright <- Ns.top heightsLeft
      let (rightEnd,rightH) = netFromJust mbright
      notDone <- netNot =<< netIsNothing mbright
      (leftEnd,leftH) <- liftM netFromJust $ Ns.top ascStack
      shortCase <- greaterThan rightH leftH
      tallCase  <- greaterThan leftH rightH
      heightsLeft <- flip Ns.condPop heightsLeft =<< netNot tallCase
      pushC <- netAnd shortCase notDone
      ascStack <- Ns.condPush pushC (nxLeftEnd,rightH) ascStack
      xdiff <- sub rightEnd leftEnd
      candidate <- multiply leftH xdiff
      better  <- greaterThan candidate best
      updateC <- netAnds [tallCase,notDone,better]
      best    <- mux updateC best =<< extend resultWidth candidate
      nxLeftEnd'<- add const1 rightEnd
      nxLeftEnd <- mux tallCase nxLeftEnd' leftEnd
      ascStack <- Ns.condPop tallCase ascStack
      return (best,heightsLeft,ascStack,nxLeftEnd)
    ) (resultInit,Ns.fromList heightsLeft,Ns.fromList [(constIntW xw 0,const0)]
      ,constIntW xw 1) 
    [1..2*n]
  return best
  where
  n = length heights
  xw = valueSize (n+1)
  heightsLeft = zip (map constInt [1..]) $ heights++[const0]
  resultWidth = xw+maximum (map intWidth heights)
  const1 = constInt 1
  const0 = constInt 0
  resultInit = constIntW resultWidth 0
