module Circuit.StableMarriage where

import Control.Monad
import Data.List
import Debug.Trace

import Circuit.Array
import Util

{-
TODO
Complete specs
Write code
test interpreted
write stack circuit
test interpreted stack circuit
write circuit
test
Refactor internals (with new types like stackSpecs and maybeSpecs)
-}

-- int should be big enough for [0,n] *inclusive*
data StableMarriageSpecs m int bool pairQueue = StableMarriageSpecs 
  { smsConstInt       :: Int -> m int
  , smsConstBool      :: Bool -> m bool
  , smsInversePermute :: [int] -> m [int]
  , smsReadBatch      :: [int] -> [int] -> m [int]
  , smsIncr           :: int -> m int
  , smsMux            :: bool -> (int,int) -> (int,int) -> m (int,int)
  , smsLessThan       :: int -> int -> m bool
  , smsUnionWith      :: ((int,int) -> (int,int) -> m (int,int))
                      -> [(int,(int,int))] -> [(int,(int,int))] 
                      -> m [(int,(int,int))]
  , smsAbsent        :: Int -> [int] -> m [bool]
  , smsQueueFromList :: [(int,int)] -> m pairQueue
  , smsQueueFront    :: pairQueue -> m (int,int)
  , smsQueuePop      :: bool -> pairQueue -> m pairQueue
  }

-- Assumes that orderM and orderF are n by n matrices
stableMarriage  :: (Show int,Show bool,Monad m) => StableMarriageSpecs m int bool pairStack 
                -> [[int]] -> [[int]] -> m [int]

stableMarriage specs orderM orderF = do
  invalid     <- smsConstInt specs n
  trueConst   <- smsConstBool specs True
  allInds     <- mapM (smsConstInt specs) [0..n-1]
  rankF       <- mapM (smsInversePermute specs) orderF
  sheLikesMe_ranks  <- mapM (uncurry $ smsReadBatch specs)
                    $ zip (transpose rankF) orderM
  sheLikesMe    <- mapM (smsQueueFromList specs . uncurry zip) 
                $ zip orderM sheLikesMe_ranks
  unengagedM    <- return $ replicate n trueConst
  statusF       <- return $ replicate n (invalid,invalid)
  (statusF,_,_) <- forModify (statusF,sheLikesMe,unengagedM) [1..n] 
    $ \(statusF,sheLikesMe,unengagedM) r -> do
      luckyness   <- traceShow ("StatusF",statusF) $ mapM (smsQueueFront specs) sheLikesMe
      deltaStatus <- forM (zip3 allInds  unengagedM luckyness) 
        $ \(m,uneng,(f,lucky)) -> do
          (m,l) <- smsMux specs uneng (invalid,invalid) (m,lucky) 
          return (f,(m,l))
      sheLikesMe <- mapM (uncurry $ smsQueuePop specs) 
                  $ zip unengagedM sheLikesMe
      temp <- smsUnionWith specs updateStatus deltaStatus $ zip allInds statusF 
      statusF <- mapM (return.snd) temp
      unengagedM <- if r<n then smsAbsent specs n $ map fst statusF
                           else return unengagedM
      return $ traceShow ("unengagedM",unengagedM) $ (statusF,sheLikesMe,unengagedM)
  return $ map fst $ traceShow ("StatusFEnd",statusF) statusF
  where
  updateStatus (m1,v1) (m2,v2) = do
    small  <- smsLessThan specs v1 v2
    smsMux specs small (m2,v2) (m1,v1)
  n = length orderM

forModify :: Monad m => a -> [b] -> (a -> b -> m a) -> m a
forModify init l f = foldM f init l
