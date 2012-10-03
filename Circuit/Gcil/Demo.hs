module Circuit.Gcil.Demo where

import Control.Monad
import Data.List

import Circuit.Gcil.Compiler as Gc
import Circuit.Gcil.Queue as Gq


-- Given a set of points on the circumference of a circle,
-- find the widest angle made by them at the center. All angles are
-- scaled by a factor of maxTheta/(2*pi) to avoid use of floating point
-- Assumes n >= 2, and that theta is sorted in ascending order
{-
Implements the following code, in circuit (why is this still so painful!)
result = 0
i = j = 0
while(i<n)
{
  result = max result (f theta[i] theta[j])
  if ((j+1<n) && (f theta[i] theta[j] <= modDiff maxTheta theta[i] theta[j+1]))
    j++
  else
    i++
}

Mapping: theta[i..j] -> inRange (Queue, never empty)
         theta[j]    -> cur
         theta[i]    -> lastInRange
         theta[j+1..n-1] -> unseen (Queue)
-}
wideAngle theta maxTheta = do
  let result  = constArg (gblWidth maxTheta) 0
      unseen  = Gq.fromList $ tail theta
      cur     = head theta
      inRange = Gq.fromList [head theta]
  (result,_,_,_) <- foldM (\(result,cur,unseen,inRange) _ -> do
    lastInRange  <- liftM castFromJust $ Gq.front inRange
    curAngle <- modDiff maxTheta lastInRange cur
    result   <- Gc.max result curAngle
    nextmb   <- Gq.front unseen
    (c,cur)  <- Gc.caseGblMaybe (\mb -> case mb of 
                  Nothing -> return (bitZero,cur)
                  Just next -> do 
                    nextAngle <- modDiff maxTheta lastInRange next
                    c' <- Gc.not =<< greaterThanU curAngle nextAngle
                    return (c',next)
                  ) nextmb
    unseen  <- Gq.condPop c unseen
    inRange <- Gq.condPush c cur inRange
    c       <- Gc.not c
    inRange <- Gq.condPop c inRange
    return (result,cur,unseen,inRange)
    ) (result,cur,unseen,inRange) [1..2*n-1]
  return result
  where
  n = length theta

-- modDiff m a b assumes a <= b < maxtheta
modDiff m a b = do 
  x <- subU b a
  y <- subU m x
  Gc.min x y

fold1M f l = foldM f (head l) (tail l)

-- Naive O(n^2) comparison
wideAngleNaive theta maxTheta = join $ fold1M (liftM2 Gc.max) l
  where
  allPair = [(a,b) | (a,bs) <- zip theta (tail $ tails theta), b <- bs]
  l = map (uncurry $ modDiff maxTheta) allPair

-- TODO stack needs condModifyTop
{-
Stack of (height,startx) pair

Add zeroes to both sides

if top shorterThan current, push (current.x,current.h), i++
if top sameHeightAs current, i++
if top tallerThan current, updateWith (current.x-top.x)*top.h, pop
rectangleInHistogram heights = do
  (best,_,_) <- foldM (\(best,heightsLeft,ascStack) i -> do
    mbtop <- Gs.top ascStack
    if knownNothing mbtop then return (best,heightsLeft,ascStack)
    else do 
    ) ((constArg resultWidth 0),heightsLeft,Gs.fromList (constArg 1 0)) [1..n]
  return best

  -}
