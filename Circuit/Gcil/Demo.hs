module Circuit.Gcil.Demo where

import Control.Monad
import Data.List
import Debug.Trace

import Circuit.Gcil.Compiler as Gc
import Circuit.Gcil.Queue as Gq
import Circuit.Gcil.Stack as Gs
import Util


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

foldMWithBreak :: Monad m => (a -> b -> m (Maybe a)) -> a -> [b] -> m a
foldMWithBreak f init [] = return init
foldMWithBreak f init (h:t) = do mb <- f init h
                                 case mb of Nothing -> return init
                                            Just x  -> foldMWithBreak f x t

-- Naive O(n^2) comparison
wideAngleNaive theta maxTheta = join $ fold1M (liftM2 Gc.max) l
  where
  allPair = [(a,b) | (a,bs) <- zip theta (tail $ tails theta), b <- bs]
  l = map (uncurry $ modDiff maxTheta) allPair

shiftLeft amt x = Gc.concat [x,(constArg amt 0)]

multiply a b = aux b where
  addop bt = Gc.bitwiseAnd a =<< Gc.sextend awidth (bitToInt bt)
  awidth = gblWidth a
  aux b = if bwidth == 1 then addop (intToBit b)
                         else do (bt,b') <- splitMsb b
                                 s <- leadz =<< multiply a b'
                                 addU s =<< shiftLeft (bwidth-1) =<< addop bt
        where bwidth = gblWidth b
              leadz x = zextend (gblWidth x + 1) x
                             
-- TODO stack needs condModifyTop
{-
Stack of (height,startx) pair

Add zeroes to both sides

if top shorterThan current, push (current.x,current.h), i++
if top sameHeightAs current, i++
if top tallerThan current, updateWith (current.x-top.x)*top.h, pop
  -}
rectangleInHistogram heights = do
  (best,_,_,_) <- foldMWithBreak (\(best,heightsLeft,ascStack,nxLeftEnd) _ -> do
    mbcur <- Gs.top heightsLeft
    if knownNothing mbcur then return Nothing
    else liftM Just $ do
      mbright <- Gs.top heightsLeft
      let (rightEnd,rightH) = castFromJust mbright
      notDone <- Gc.not =<< gblIsNothing mbright
      (leftEnd,leftH) <- liftM castFromJust $ Gs.top ascStack
      shortCase <- greaterThanU rightH leftH
      tallCase  <- greaterThanU leftH rightH
      heightsLeft <- flip Gs.condPop heightsLeft =<< Gc.not tallCase
      pushC <- Gc.and shortCase notDone
      ascStack <- Gs.condPush pushC (nxLeftEnd,rightH) ascStack
      xdiff <- subU rightEnd leftEnd
      candidate <- multiply leftH xdiff
      better  <- Gc.greaterThanU candidate best
      updateC <- Gc.andList [tallCase,notDone,better]
      best    <- Gc.mux updateC best =<< zextend resultWidth candidate
      --nxLeftEnd <- Gc.mux pushC nxLeftEnd =<< Gc.addU const1 rightEnd
      --nxLeftEnd <- Gc.mux tallCase nxLeftEnd leftEnd
      nxLeftEnd'<- Gc.addU const1 rightEnd
      nxLeftEnd <- Gc.mux tallCase nxLeftEnd' leftEnd
      ascStack <- Gs.condPop tallCase ascStack
      --newOutput $ bitToInt pushC
      return (best,heightsLeft,ascStack,nxLeftEnd)
    ) (resultInit,Gs.fromList heightsLeft,Gs.fromList [(constArg xw 0,const0)]
      ,constArg xw 1) 
    [1..2*n]
  return best
  where
  n = length heights
  xw = valueSize (n+1)
  heightsLeft = zip (map (constArg xw) [1..]) $ heights++[const0]
  resultWidth = xw+maximum (map gblWidth heights)
  const1 = constArg 1 1
  const0 = constArg 1 0
  resultInit = constArg resultWidth 0
