module Circuit.StableMarriage where

import Control.Monad
import Data.List

import Circuit.Array

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
stableMarriage  :: Monad m => StableMarriageSpecs m int bool pairStack 
                -> [[int]] -> [[int]] -> m [int]

stableMarriage specs orderM orderF = do
  invalid     <- smsConstInt specs n
  allInds     <- mapM (smsConstInt specs) [0..n-1]
  rankF       <- mapM (smsInversePermute specs) orderF
  sheLikesMe_ranks  <- mapM (uncurry $ smsReadBatch specs)
                    $ zip (transpose rankF) orderM
  sheLikesMe    <- mapM (smsQueueFromList specs . uncurry zip) 
                $ zip orderM sheLikesMe_ranks
  unengagedM    <- replicateM n $ smsConstBool specs True
  statusF       <- replicateM n (dup n)
  (statusF,_,_) <- forModify (statusF,sheLikesMe,unengagedM) [1..n] 
    $ \(statusF,sheLikesMe,unengagedM) r -> do
      luckyness   <- mapM (smsQueueFront specs) sheLikesMe
      deltaStatus <- forM (zip3 allInds  unengagedM luckyness) 
        $ \(m,uneng,(f,lucky)) -> 
          dup n >>= smsMux specs uneng (m,lucky) >>= return.((,)f)
      sheLikesMe <- mapM (uncurry $ smsQueuePop specs) 
                  $ zip unengagedM sheLikesMe
      temp <- smsUnionWith specs updateStatus deltaStatus $ zip allInds statusF 
      statusF <- mapM (return.snd) temp
      unengagedM <- if r<n then smsAbsent specs n $ map snd statusF
                          else return unengagedM
      return (statusF,sheLikesMe,unengagedM)
  return $ map fst statusF
  where
  updateStatus (m1,v1) (m2,v2) = do
    small  <- smsLessThan specs v1 v2
    smsMux specs small (m1,v1) (m2,v2)
  n = length orderM
  dup n = do x <- smsConstInt specs n; return (x,x)

forModify :: Monad m => a -> [b] -> (a -> b -> m a) -> m a
forModify init l f = foldM f init l
