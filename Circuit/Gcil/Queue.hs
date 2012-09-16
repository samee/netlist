module Circuit.Gcil.Queue where

import Circuit.Gcil.Compiler as GC

-- We can simply use gblIsNothing bits and avoid headPtr and tailPtr ops TODO
data Queue a = Queue { buffer :: [GblMaybe a]
                     , headPtr :: GblInt
                     , tailPtr :: GblInt
                     , parent :: Maybe (Queue (a,a))
                     , headAdjusted :: Bool   -- pop-side
                     , tailAdjusted :: Bool   -- push-side
                     }

-- By the way things are set up, pop only chooses from the first 5 buffer slots
--                               push only writes into one of the last 3
ptrWidth = 3
buffSize = 6

empty = Queue { buffer = replicate buffSize $ gblMaybe Nothing
              , headPtr = constArg ptrWidth 1
              , tailPtr = constArg ptrWidth 1
              , parent = Nothing
              , headAdjusted = True
              , tailAdjusted = True
              }


front q = muxList (q headPtr) $ take 5 $ buffer q
-- Apparently I do not need to check parent
null q = equalU (headPtr q) (tailPtr q)

condPush c v q = do
  dec <- hackeyDecoder c $ tailPtr q
  newbuff <- forM (zip dec $ drop 3 $ buffer q) $ \write oldv -> 
                mux write oldv v
  newtail <- condAddS (tailPtr q) (constArg ptrWidth 1)
  adjustTail $ q { buffer = (take 3 $ buffer q)++newbuff
                 , tailPtr = newtail
                 }

-- Internal use by condPush
-- case i of 00 -> [0,1,0]; 01 -> [0,0,1]; 11 -> [1,0,0]
hackeyDecoder en i = do
  i0 <- liftM intToBit $ select 0 1 i
  i1 <- liftM intToBit $ select 1 2 i
  (ab,c) <- decoderUnit en i1
  (a,b)  <- decoderUnit ab i0
  return [a,b,c]

condPop c q = do
  dec <- decoderWithEnable c $ headPtr q
  newbuff <- liftM (++[last $ buffer q]) $ forM (zip dec $ init $ buffer q)
              $ \erase oldv -> condNothing erase oldv
  dhead   <- condAddS (headPtr q) (constArg ptrWidth 1)
  newhead <- addS (headPtr q) dhead
  adjustHead $ q  { buffer = newbuff
                  , headPtr = newhead
                  }

-- Internal use
parentNull q = case parent q of
                    Nothing  -> return gblOneBit
                    Just par -> null par

adjustTail q | tailAdjusted q = q { tailAdjusted = False }
             | otherwise = do
               tailSlide <- greaterThanU (tailPtr q) (constArg ptrWidth 4)
               tptr      <- condAddS (tailPtr q) (constArg ptrWidth (-2))
               pnull     <- parentNull q
               headFull  <- greaterThanU (constArg 3 2) (headPtr q)
               slideToParent <- and tailSlide =<< or headFull =<< not pnull
               slideToHead   <- xor slideToParent tailSlide
               newhead <- zipMux slideToHead (take 3 $ buff) 
                                             (drop 2 $ take 3 buff)
               hptr    <- condAddS slideToHead (headptr q) 
                                   (constArg ptrWidth (-2))
               newtail <- zipMux tailSlide (take 3 $ buff) 
                                           (last buff++[blank,blank])
               newPar  <- condPush slideToParent 
                            (castFromJust (buff!!3),castFromJust (buff!!4))
                            oldparent
               return $ q { buffer = newhead++newtail
                          , headptr = hptr
                          , tailptr = tptr
                          , parent = newPar
                          , tailAdjusted = True
                          }
  where
  oldparent = case parent q of Nothing -> empty; Just p -> p
  buff = buffer q


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
