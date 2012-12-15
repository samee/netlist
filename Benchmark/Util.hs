-- Provides utilities for comparing our data structures with naive versions

module Benchmark.Util where
import Control.Monad

import Circuit.NetList
import qualified Circuit.Stack as CS
import Util

-- Array
naiveListWrite :: Swappable a => NetBool -> NetUInt -> a -> [a] -> NetWriter [a]
naiveListWrite cond i val l = do
  en   <- decoderREn cond 0 (length l) i
  forM (zip en l) $ \(w,old) -> mux w old val

-- Stack --
class StackType s where
  stkEmpty     :: s a
  stkFromList  :: [a] -> s a
  stkNull      :: s a -> NetWriter NetBool
  stkCondPop   :: Swappable a => NetBool ->      s a -> NetWriter (s a)
  stkCondPush  :: Swappable a => NetBool -> a -> s a -> NetWriter (s a)
  stkTop       :: Swappable a =>                 s a -> NetWriter (NetMaybe a)
  stkCapLength :: Int -> s a -> s a
  stkEmpty         = stkFromList []
  stkCapLength _ s = s

instance StackType CS.Stack where
  stkFromList  = CS.fromList
  stkNull      = CS.null
  stkCondPop   = CS.condPop
  stkCondPush  = CS.condPush
  stkTop       = CS.top
  stkCapLength = CS.capLength

data SimpleStack a = SimpleStack { ssContent :: [a]
                                 , ssTopPtr  :: NetUInt
                                 , ssMaxLen  :: Int
                                 }

-- Mostly copied from (not yet) old version of Test.StackGcil
-- TODO remove duplicate code from that file and from Benchmark.StackDimacs
instance StackType SimpleStack where
  stkFromList l = SimpleStack { ssContent = l
                              , ssTopPtr  = constInt $ length l
                              , ssMaxLen  = maxBound
                              }
  stkNull s = equal (ssTopPtr s) (constInt 0)
  -- Warning: Unsafe to pop a null stack!
  stkCondPop c s = do top <- condSub c (ssTopPtr s) (constInt 1)
                      return $ s { ssTopPtr = top }
  stkCondPush c v s = do
    newbuff <- naiveListWrite c (ssTopPtr s) v oldbuff
    top     <- condAdd c (ssTopPtr s) (constIntW niw 1)
    return $ s { ssContent = newbuff, ssTopPtr = top }
    where
    niw = min (indexSize newlen) (1 + intWidth (ssTopPtr s))
    oldlen = length $ ssContent s
    (newlen,oldbuff) = if ssMaxLen s == oldlen
                          then (oldlen  ,ssContent s)
                          else (oldlen+1,ssContent s++[v])
  stkTop s = case ssContent s of 
                  [] -> return netNoth
                  buff  -> do
                    nl <- stkNull s
                    condZap nl . netJust =<< muxList (ssTopPtr s) buff
  stkCapLength cap s = s { ssMaxLen = cap }

