module Circuit.Gcil.Queue where

data Queue a = Queue { buffer :: [GblMaybe a]
                     , headPtr :: GblInt
                     , tailPtr :: GblInt
                     , parent :: Maybe (Queue (a,a))
                     , headAdjusted :: Bool
                     , tailAdjusted :: Bool
                     }

ptrWidth = 3
buffSize = 6

empty = Queue { buffer = replicate buffSize $ gblMaybe Nothing
              , headPtr = constArg ptrWidth 1
              , tailPtr = constArg ptrWidth 1
              , parent = Nothing
              , headAdjusted = True
              , tailAdjusted = True
              }


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
