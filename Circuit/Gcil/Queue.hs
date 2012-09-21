module Circuit.Gcil.Queue 
( Queue
, Circuit.Gcil.Queue.empty
, capLength
, front
, Circuit.Gcil.Queue.null
, condPush, condPop) where

import Control.Monad

import Circuit.Gcil.Compiler as Gc
import Debug.Trace

-- We can simply use gblIsNothing bits and avoid headPtr and tailPtr ops TODO
data Queue a = Queue { buffer :: [GblMaybe a]
                     , headPtr :: GblInt
                     , tailPtr :: GblInt
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


empty = Queue { buffer = replicate buffSize $ gblMaybe Nothing
              , headPtr = constArg ptrWidth 3
              , tailPtr = constArg ptrWidth 3
              , parent = Nothing
              , headAdjusted = True
              , tailAdjusted = True
              , maxLength = maxBound
              }


front q = muxList (headPtr q) $ take 5 $ buffer q
-- Apparently I do not need to check parent
null q = equalU (headPtr q) (tailPtr q)

-- Internal use unambiguous aliases

gqnull = Circuit.Gcil.Queue.null
gqempty = Circuit.Gcil.Queue.empty

parentLength len = (len-2) `div` 2

capLength :: Int -> Queue a -> Queue a
capLength len q = q { maxLength = len
                    , parent = cappedParent
                    }
  where
  cappedParent = case parent q of 
    Nothing -> Nothing
    Just p -> Just $ capLength (parentLength len) p

condPush :: Garbled g => GblBool -> g -> Queue g -> GcilMonad (Queue g)
condPush c v q = do
  dec <- hackeyDecoder c $ tailPtr q
  newtail <- forM (zip dec $ bufferTail q) $ \(write,oldv) -> 
                mux write oldv (gblMaybe $ Just v)
  tptr <- condAddS c (tailPtr q) (constArg ptrWidth 1)
  adjustTail $ q { buffer = bufferHead q++newtail
                 , tailPtr = tptr }

-- Internal use by condPush
-- case i of 00 -> [0,1,0]; 01 -> [0,0,1]; 11 -> [1,0,0]
hackeyDecoder en i = do
  i0 <- liftM intToBit $ select 0 1 i
  i1 <- liftM intToBit $ select 1 2 i
  (ab,c) <- decoderUnit en i1
  (a,b)  <- decoderUnit ab i0
  return [c,a,b]

condPop :: (GblShow g,Garbled g) => GblBool -> Queue g -> GcilMonad (Queue g)
condPop c q = do
  c <- Gc.and c =<< Gc.not =<< gqnull q
  dec <- decoderWithEnable c $ headPtr q
  newbuff <- liftM (++[last $ buffer q]) $ forM (zip dec $ init $ buffer q)
              $ \(erase,oldv) -> condNothing erase oldv
  newhead <- condAddS c (headPtr q) (constArg ptrWidth 1)
  adjustHead >=> resetIfEmpty $ q { buffer = newbuff
                                  , headPtr = newhead
                                  }

resetIfEmpty q = do
  eq <- equalU (headPtr q) (tailPtr q)
  pnull <- parentNull q
  emp <- Gc.and pnull eq
  tptr <- mux emp (tailPtr q) (constArg ptrWidth 3)
  hptr <- mux emp (headPtr q) (constArg ptrWidth 3)
  return $ q { headPtr = hptr, tailPtr = tptr }

-- Internal use
noth = gblMaybe Nothing
parentNull q = case parent q of
                    Nothing  -> return Gc.bitOne
                    Just par -> gqnull par

adjustTail q | tailAdjusted q         = return $ q { tailAdjusted = False }
             | knownNothing (buff!!4) = return $ q { tailAdjusted = True  }
             | knownNothing (buff!!3) = error "Queue tail problem"
             | otherwise = do
               let parentPayload = (assumeJust 3, assumeJust 4)
               tailSlide <- greaterThanU (tailPtr q) (constArg ptrWidth 4)
               tptr      <- condAddS tailSlide  (tailPtr q) 
                                                (constArg ptrWidth (-2))
               pnull     <- parentNull q
               headFull  <- greaterThanU (constArg 3 2) (headPtr q)
               slideToParent <- Gc.and tailSlide 
                            =<< Gc.or headFull =<< Gc.not pnull
               slideToHead   <- xor slideToParent tailSlide
               newhead <- zipMux slideToHead (bufferHead q) 
                                             (take 3 $ drop 2 buff)
               hptr    <- condAddS slideToHead (headPtr q) 
                                   (constArg ptrWidth (-2))
               newtail <- zipMux tailSlide (bufferTail q) 
                                           (last buff:[noth,noth])
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
  assumeJust i = castFromJust (buff!!i)

class Garbled g => GblShow g where
  gblShow :: g -> GcilMonad ()

instance GblShow GblInt where
  gblShow x = addU (constArg 1 0) x >>= newOutput

instance (GblShow g,GblShow g') => GblShow (g,g') where
  gblShow (x,y) = do gblShow x; gblShow y

showConst w i = addU (constArg w i) (constArg 1 0)  >>= gblShow

instance GblShow g => GblShow (GblMaybe g) where
  gblShow (GblMaybe _ Nothing) = do showConst 15 10101
                                    showConst 1 0
                                    showConst 1 0
  gblShow (GblMaybe p (Just x)) = do showConst 15 10101
                                     gblShow (bitToInt p)
                                     gblShow x

--adjustHead :: Garbled g => Queue g -> GcilMonad (Queue g)
adjustHead q | headAdjusted q = return $ q { headAdjusted = False }
             | otherwise = do
               headSlide <- greaterThanU (headPtr q) (constArg ptrWidth 1)
               (parentPayload,newPar) <- slideFromParent headSlide
               noPayload <- gblIsNothing (head parentPayload)
               tailFull <- greaterThanU (tailPtr q) (constArg ptrWidth 4)
               slideFromTail <- Gc.and tailFull =<< Gc.xor headSlide noPayload
               finalPayload <- zipMux noPayload parentPayload tailPayload
               tailNotStuck <- Gc.and headSlide tailFull
               slideSuccess <- Gc.or tailNotStuck =<< Gc.not noPayload
               tailUsed     <- Gc.and tailNotStuck noPayload
               hptr <- condAddS slideSuccess (headPtr q) 
                                             (constArg ptrWidth (-2))
               tptr <- condAddS tailUsed (tailPtr q)
                                         (constArg ptrWidth (-2))
               newHead <- zipMux slideSuccess (bufferHead q)
                                              ((buffer q!!2):finalPayload)
               newTail <- zipMux tailUsed (bufferTail q)
                                          ((buffer q!!5):[noth,noth])
               return $ q { buffer = newHead++newTail
                          , headPtr = hptr
                          , tailPtr = tptr
                          , parent = newPar
                          , headAdjusted = True
                          }
  where
  nothpair = [noth,noth] -- well, list actually
  tailPayload = take 2 $ bufferTail q
  slideFromParent headSlide = case parent q of
    Nothing -> return (nothpair,Nothing)
    Just par -> do mb <- front par
                   par' <- condPop headSlide par
                   payload <- mux headSlide (gblMaybe Nothing) mb
                   return (distrJust payload,Just par')

  distrJust (GblMaybe _ Nothing) = nothpair
  distrJust (GblMaybe p (Just (a,b))) 
    = [GblMaybe p (Just a),GblMaybe p (Just b)]

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
