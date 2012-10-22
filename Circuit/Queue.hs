module Circuit.Queue 
( Queue
, Circuit.Queue.empty
, fromList
, capLength
, front
, Circuit.Queue.null
, condPush, condPop) where

import Control.Monad
import Util

import Circuit.NetList

-- We can simply use gblIsNothing bits and avoid headPtr and tailPtr ops TODO
data Queue a = Queue { buffer :: [NetMaybe a]
                     , headPtr :: NetUInt
                     , tailPtr :: NetUInt
                     , parent :: Maybe (Queue (a,a))
                     , headAdjusted :: Bool   -- pop-side
                     , tailAdjusted :: Bool   -- push-side
                     , maxLength :: Int
                     }

-- Internal configs
-- By the way things are set up, pop only chooses from the first 5 buffer slots
--                               push only writes into one of the last 3
ptrWidth = 3
buffSize = 6
bufferHead q = take 3 $ buffer q
bufferTail q = drop 3 $ buffer q


empty = Queue { buffer = replicate buffSize netNoth
              , headPtr = constIntW ptrWidth 3
              , tailPtr = constIntW ptrWidth 3
              , parent = Nothing
              , headAdjusted = True
              , tailAdjusted = True
              , maxLength = maxBound
              }


fromList :: Swappable g => [g] -> Queue g
fromList [] = empty
fromList [x] = empty { buffer = [netNoth,netNoth,netNoth
                                ,netJust x,netNoth,netNoth]
                     , tailPtr = constIntW ptrWidth 4
                     , tailAdjusted = False
                     }
fromList (x1:x2:l) 
  | even $ length l = (twoItems x1 x2) { parent = parentList l }
  | otherwise = (threeItems x1 x2 (last l)) { parent = parentList $ init l }
  where
  twoItems x1 x2 = empty  { buffer = [netNoth,netJust x1,netJust x2
                                     ,netNoth,netNoth,netNoth]
                          , headPtr = constIntW ptrWidth 1
                          }
  threeItems x1 x2 x3 = empty { buffer =  [netNoth,netJust x1,netJust x2
                                          ,netJust x3,netNoth,netNoth]
                              , headPtr = constIntW ptrWidth 1
                              , tailPtr = constIntW ptrWidth 4
                              , tailAdjusted = False
                              }
  parentList [] = Nothing
  parentList l = Just $ fromList $ pairUp l

front q = muxList (headPtr q) $ take 5 $ buffer q

-- Apparently I do not need to check parent
null q = equal (headPtr q) (tailPtr q)

-- Internal use unambiguous aliases
gqnull = Circuit.Queue.null
gqempty = Circuit.Queue.empty

parentLength len = (len-2) `div` 2

capLength :: Int -> Queue a -> Queue a
capLength len q = q { maxLength = len
                    , parent = cappedParent
                    }
  where
  cappedParent = case parent q of 
    Nothing -> Nothing
    Just p -> Just $ capLength (parentLength len) p

-- If this changes significantly, fromList may also have to change
condPush :: Swappable a => NetBool -> a -> Queue a -> NetWriter (Queue a)
condPush c v q = do
  dec <- hackeyDecoder c $ tailPtr q
  newtail <- forM (zip dec $ bufferTail q) $ \(write,oldv) -> 
                mux write oldv (netJust v)
  tptr <- condAdd c (tailPtr q) (constInt 1)
  adjustTail $ q { buffer = bufferHead q++newtail
                 , tailPtr = tptr }

-- Internal use by condPush
-- case i of 00 -> [0,1,0]; 01 -> [0,0,1]; 11 -> [1,0,0]
hackeyDecoder en i = do
  (i0,i') <- splitLsb =<< bitify i
  i1 <- lsb i'
  (ab,c) <- decoderUnit en i1
  (a,b)  <- decoderUnit ab i0
  return [c,a,b]

condPop :: Swappable a => NetBool -> Queue a -> NetWriter (Queue a)
condPop c q = do
  c <- netAnd c =<< netNot =<< gqnull q
  dec <- decoderEn c $ headPtr q
  newbuff <- liftM (++[last $ buffer q]) $ forM (zip dec $ init $ buffer q)
              $ \(erase,oldv) -> condZap erase oldv
  newhead <- condAdd c (headPtr q) (constInt 1)
  adjustHead >=> resetIfEmpty $ q { buffer = newbuff
                                  , headPtr = newhead
                                  }

resetIfEmpty q = do
  eq <- equal (headPtr q) (tailPtr q)
  pnull <- parentNull q
  emp <- netAnd pnull eq
  tptr <- mux emp (tailPtr q) (constInt 3)
  hptr <- mux emp (headPtr q) (constInt 3)
  return $ q { headPtr = hptr, tailPtr = tptr }

-- Internal use
parentNull q = case parent q of
                    Nothing  -> return netTrue
                    Just par -> gqnull par

adjustTail q | tailAdjusted q         = return $ q { tailAdjusted = False }
             | knownNothing (buff!!4) = return $ q { tailAdjusted = True  }
             | knownNothing (buff!!3) = error "Queue tail problem"
             | otherwise = do
               let parentPayload = (assumeJust 3, assumeJust 4)
               tailSlide <- greaterThan (tailPtr q) (constInt 4)
               tptr      <- condSub tailSlide  (tailPtr q) (constInt 2)
               pnull     <- parentNull q
               headFull  <- greaterThan (constInt 2) (headPtr q)
               slideToParent <- netAnd tailSlide 
                            =<< netOr headFull =<< netNot pnull
               slideToHead   <- netXor slideToParent tailSlide
               newhead <- zipMux slideToHead (bufferHead q) 
                                             (take 3 $ drop 2 buff)
               hptr    <- condSub slideToHead (headPtr q) (constInt 2)
               newtail <- zipMux tailSlide (bufferTail q) 
                                           (last buff:[netNoth,netNoth])
               newPar  <- if maxlen <= 3 then return Nothing
                          else liftM Just $ condPush slideToParent 
                                  parentPayload oldparent
               return $ q { buffer = newhead++newtail
                          , headPtr = hptr
                          , tailPtr = tptr
                          , parent = newPar
                          , tailAdjusted = True
                          }
  where
  oldparent = case parent q of 
    Nothing -> capLength (parentLength maxlen) empty
    Just p  -> p
  buff = buffer q
  maxlen = maxLength q
  assumeJust i = netFromJust (buff!!i)

adjustHead :: Swappable g => Queue g -> NetWriter (Queue g)
adjustHead q | headAdjusted q = return $ q { headAdjusted = False }
             | otherwise = do
               headSlide <- greaterThan (headPtr q) (constInt 1)
               (parentPayload,newPar) <- slideFromParent headSlide
               noPayload <- netIsNothing (head parentPayload)
               tailFull <- greaterThan (tailPtr q) (constInt 4)
               slideFromTail <- netAnd tailFull =<< netXor headSlide noPayload
               finalPayload <- zipMux noPayload parentPayload tailPayload
               tailNotStuck <- netAnd headSlide tailFull
               slideSuccess <- netOr tailNotStuck =<< netNot noPayload
               tailUsed     <- netAnd tailNotStuck noPayload
               hptr <- condSub slideSuccess (headPtr q) (constInt 2)
               tptr <- condSub tailUsed (tailPtr q) (constInt 2)
               newHead <- zipMux slideSuccess (bufferHead q)
                                              ((buffer q!!2):finalPayload)
               newTail <- zipMux tailUsed (bufferTail q)
                                          ((buffer q!!5):[netNoth,netNoth])
               return $ q { buffer = newHead++newTail
                          , headPtr = hptr
                          , tailPtr = tptr
                          , parent = newPar
                          , headAdjusted = True
                          }
  where
  nothpair = [netNoth,netNoth] -- well, list actually
  tailPayload = take 2 $ bufferTail q
  slideFromParent headSlide = case parent q of
    Nothing -> return (nothpair,Nothing)
    Just par -> do mb <- front par
                   par' <- condPop headSlide par
                   payload <- mux headSlide netNoth mb
                   mbpl <- distrJust payload
                   return (mbpl,Just par')

  distrJust mbp | knownNothing mbp = return nothpair
                | otherwise = do p <- netIsNothing mbp
                                 let (a,b) = netFromJust mbp
                                 mapM (condZap p.netJust) [a,b]
{-
head ___X__ tail
Pop muxes over first 5,
Push muxes over last 3

A 'slide' is simply a left shift by 2 places

pushAdjust ::= Make sure the next two push operations work, and so does
               however many pops left before popAdjust

  if tailPtr > 4 then, tailSlide = True, tailPtr-=2
  -- Check where the outgoing elements should go: head or parent
  if parent is not null then slideToParent
  else if headPtr < 2   then slideToParent
  else slideToHead

  reset ptrs if size == 0

popAdjust ::= Make sure the next two pop operations work, making room for
              the 1 or two pushes left

  if headPtr > 1 then headSlide = True
  -- Check where the incoming elements are coming from: tail or parent
  if parent is not null then slideFromParent, headPtr -= 2
  -- Two different tailPtr conditions. Why? TODO
  else if tailPtr > 4 then slideFromTail, headPtr -= 2
  -- else if size == 1 then slideFromTail, headPtr -= 2 -- Re check TODO
  else do nothing, even if headSlide is True

  reset ptrs if size == 0
-}
