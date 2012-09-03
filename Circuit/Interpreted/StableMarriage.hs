module Circuit.Interpreted.StableMarriage 
( Circuit.Interpreted.StableMarriage.stableMarriage
) where

import Control.Monad.Identity
import Data.Array as A
import Data.List

import Circuit.StableMarriage as Ckt
import Util


-- ith element of result is the male to whom the ith female is married
stableMarriage :: [[Int]] -> [[Int]] -> [Int]
stableMarriage orderM orderF 
    = runIdentity $ Ckt.stableMarriage specs orderM orderF where
  specs :: StableMarriageSpecs Identity Int Bool [(Int,Int)]
  specs = Ckt.StableMarriageSpecs 
    { smsConstInt = return
    , smsConstBool = return
    , smsInversePermute = return.inversePermute
    , smsReadBatch = \l inds -> mapM (return.(l!!)) inds
    , smsIncr = return.(+1)
    , smsMux = \c a b -> return $ if c then b else a
    , smsLessThan = \a b -> return (a<b)
    , smsUnionWith = myunion
    , smsAbsent = absentMask
    , smsQueueFromList = return
    , smsQueueFront = return.head
    , smsQueuePop = \b q -> return $ if b then tail q else q
    }
  myunion :: (Monad m,Ord k) 
          => (v -> v -> m v) -> [(k,v)] -> [(k,v)] -> m [(k,v)]
  myunion f as bs = unionSorted $ sortBy cmpFst (as++bs)
    where
    cmpFst a b = compare (fst a) (fst b)
    unionSorted [] = return []
    unionSorted [a] = return [a]
    unionSorted ((k1,v1):(k2,v2):as) 
      | k1 == k2 = do x<-f v1 v2; unionSorted ((k1, x) : as)
      | k1 /= k2 = unionSorted ((k2,v2):as) >>= return.((k1,v1):)

absentMask n xs = return $ A.elems $ A.listArray (0,n-1) (replicate n True) // 
                  [(i,False) | i <- xs, i<n ]
