module Test.Stack where

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Maybe
import Debug.Trace
import System.Random

changeElt _ _ [] = []
changeElt 0 x (a:as) = x:as
changeElt i x (a:as) = a:changeElt (i-1) x as

data Stack a = Stack
  { buff :: [Maybe a]
  , buffhead :: Int
  , parent :: Maybe (Stack (a,a))
  , noadjust :: Bool
  }

stackEmpty = Stack  { buff      = replicate 6 Nothing
                    , buffhead  = 2
                    , parent    = Nothing
                    , noadjust  = True
                    }

-- Memoize between modifications, so parent lookup is disabled
stackNull :: Stack a -> Bool
stackNull stk = meempty && parentEmpty where
  meempty = buffhead stk == 2 && all isNothing (take 2 $ buff stk)
  parentEmpty = case parent stk of Nothing -> True; Just p -> stackNull p

stackSingleton x = condPush True x stackEmpty

condPush b v stk = snd $ condStackOp b (Just v) False stk
condPop b stk = condStackOp False Nothing b stk

-- Conditional stack operation: a conditional push followed by a conditional pop
condStackOp :: Bool -> Maybe a -> Bool -> Stack a -> (Maybe a, Stack a)
condStackOp True Nothing _ _ = error "Pushing in Nothing"
condStackOp pushCond pushVal popCond stk = (top, adjust newstack) where
  top = buff stk !! (buffhead stk - 1)
  -- Try changing this, given that we do not have an empty indicator
  newstack = stk  { buff = if not pushCond && not popping then buff stk
                           else if popping then changeElt (bh-1) Nothing bf
                           else changeElt bh pushVal bf
                  , buffhead  = bh - b2i popping + b2i pushCond
                  }
  bf = buff stk
  bh = buffhead stk
  b2i True  = 1
  b2i False = 0
  popping = popCond && not (stackNull stk)
  (lo,hi) = if noadjust stk then (2,4) else (1,5)


-- Restriction: we cannot use more than a single condStackOp call
adjust stk  | hi-lo<6 = stk { noadjust = False }
            | otherwise = stk { buff = shiftbuff
                              , buffhead = shiftbh
                              , parent = mbparent
                              , noadjust = True
                              }
  where
  (lo,hi) = if noadjust stk then (1,5) else (0,6)
  bh = buffhead stk
  -- fullTail == False --> either parent empty or Nothing
  (pv,fullTail) = case buff stk of (Just a):(Just b):_ -> (Just (a,b),True)
                                   otherwise -> (Nothing,False)
  parentpop  = bh < 2
  parentpush = bh >= 4 && fullTail
  shiftbh = if parentpop then bh+2 else if bh >= 4 then bh-2 else bh

  newparent = case pv of Nothing -> Nothing
                         Just x -> Just $ stackSingleton x

  (popa,popb,mbparent) = case parent stk of
      Nothing -> (Nothing,Nothing,newparent)
      Just p -> distJust $ condStackOp parentpush pv parentpop p

  distJust (Nothing,x) = (Nothing,Nothing,Just x)
  distJust (Just (a,b),x) = (Just a,Just b,Just x)
  
  shiftbuff = if parentpop then [popa,popb]++take 4 (buff stk)
              else if bh >= 4 then drop 2 (buff stk) ++ [Nothing,Nothing]
              else buff stk
  
-- Write up Circuit.Interpreted.Stack.*
-- test it. Refactor? Circuit.Gcil.Stack
testStack :: RandomGen g => g -> (Bool,g)
testStack rgen = flip runState rgen $ do
  n   <- state $ randomR (10,100)
  liftM isJust $ runMaybeT $ foldM (\(stk',stk,len) _ -> do
    rlen <- lift $ state $ randomR (0,2*n)
    newvals <- lift $ replicateM (max 0 (rlen-len)) $ state $ randomR vrange
    if len<rlen then return (newvals++stk',stackPushN newvals stk,rlen)
    else if len==rlen then return (stk',stk,rlen)
    else let (exp,rstk') = splitAt  (len-rlen) stk'
             (res,rstk ) = stackPopN (len-rlen) stk in
         if exp==res then return (rstk',rstk,rlen) else fail ""
    ) ([],stackEmpty,0) [1..100]
  where 
    vrange :: (Int,Int)
    vrange = (0,100)
    stackPopN 0 stk = ([],stk)
    stackPopN n stk = case mb of
      Nothing -> (xs,stk'')
      Just x  -> (x:xs,stk'')
      where (mb,stk') = condPop True stk
            (xs,stk'')= stackPopN (n-1) stk'
    stackPushN [] stk = stk
    stackPushN (x:xs) stk = condPush True x $ stackPushN xs stk
  

runTests = do testStatus <- replicateM 10 $ getStdRandom testStack
              putStrLn $ show (and testStatus) ++ "   Test.Stack.testStack"
