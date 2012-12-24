-- Provides utilities for comparing our data structures with naive versions

module Test.Util.Simple where
import Control.Monad
import Data.Bits

import Circuit.NetList
import qualified Circuit.Stack as CS
import qualified Circuit.Queue as CQ
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


-- Queue --

class QueueType q where
  qEmpty     :: q a
  qFromList  :: [a] -> q a
  qNull      :: q a -> NetWriter NetBool
  qCondPop   :: Swappable a => NetBool ->      q a -> NetWriter (q a)
  qCondPush  :: Swappable a => NetBool -> a -> q a -> NetWriter (q a)
  qFront     :: Swappable a =>                 q a -> NetWriter (NetMaybe a)
  qCapLength :: Int -> q a -> q a
  qEmpty         = qFromList []
  qCapLength _ q = q

instance QueueType CQ.Queue where
  qEmpty     = CQ.empty
  qFromList  = CQ.fromList
  qNull      = CQ.null
  qCondPop   = CQ.condPop
  qCondPush  = CQ.condPush
  qFront     = CQ.front
  qCapLength = CQ.capLength

-- Conventions: max length of sqContent is a power of 2 - 1
-- so sqMaxIndexW actually stores the ceiling of log, not quite the log
data SimpleQueue a = SimpleQueue { sqContent :: [a]
                                 , sqHead, sqTail :: NetUInt
                                 , sqMaxIndexW :: Int
                                 }

instance QueueType SimpleQueue where
  qFromList l = SimpleQueue { sqContent = l
                            , sqHead = constIntW w 0
                            , sqTail = constIntW w $ length l
                            , sqMaxIndexW = bitSize $ length l
                            }
    where w = valueSize (length l)
  -- XXX qpush can resize index widths
  qNull q = equal (sqHead q) (sqTail q)
  -- Warning: not safe to pop empty queue
  qCondPop c q = do h <- condAdd c (sqHead q) (constInt 1)
                    return $ q { sqHead = h }
  qFront q = case sqContent q of
                [] -> return netNoth
                l  -> do x <- muxList (sqHead q) l
                         a <- qNull q
                         condZap a $ netJust x

  qCapLength len q = q { sqMaxIndexW = valueSize len }
  qCondPush c x q = do
    w <- decoderREn c 0 oldlen (sqTail q)
    buff <- forM (zip oldbuff w) $ \(oldx,w) -> mux c oldx x
    tx   <- extend nw (sqTail q)
    hx   <- extend nw (sqHead q)
    tx   <- condAdd c tx (constInt 1)
    return q { sqContent = mkbuff buff, sqHead = hx, sqTail = tx }
    where
    oldbuff = sqContent q
    oldlen = length oldbuff
    nw = min (sqMaxIndexW q) (valueSize $ 1+oldlen)
    extendbuff = oldlen < 2^(sqMaxIndexW q)-1
    mkbuff b = if extendbuff then b++[x] else b

