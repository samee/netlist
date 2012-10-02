module Circuit.Gcil.Stack where

import Data.Maybe
import Control.Monad
import Prelude hiding (null)

import Circuit.Gcil.Compiler as GC

-- Unless I have a reason to mux between stacks (I shouldn't), 
-- the rest field stays Maybe, not GblMaybe. If you are muxing between stacks
-- you should check to see if something similar can be done by tweaking push
-- and pop conditions. Note, we do NOT implement Garbled (Stack a), by choice.
-- That would create all sorts of problems related with the 'adjusted' field,
-- resizing to equal size, and other things.
data Stack a = Stack  { buffer   :: [GblMaybe a]
                      , buffhead :: GblInt
                      , rest     :: Maybe (Stack (a,a))
                      , adjusted :: Bool
                      , maxLength:: Int
                      }

buffsize = 5
ptrwidth = 3
buffmin = 2  -- buffer holds at least this many items after adjustment
             -- if parent is not empty
buffmax = 3  -- buffer holds upto this many items after adjustment, without
             -- spilling into 'rest'. Change trimStack if this changes

empty = Stack { buffer = replicate buffsize $ gblMaybe Nothing
              , buffhead = constArg ptrwidth buffmin
              , rest = Nothing
              , adjusted = True
              , maxLength = maxBound
              }

singleton x = condPush bitOne x empty

-- Internal method: called only after adjustment
trimStack (stk@Stack{rest=Nothing}) = stk
trimStack (stk@Stack{rest=Just par,maxLength=cap})
  | cap <= buffmax = stk { rest = Nothing }
  | otherwise      = stk

parentStack :: Stack a -> Stack (a,a)
parentStack (Stack{rest=Just par}) = par
parentStack (stk@Stack{rest=Nothing,maxLength=cap})
  = case rest $ capLength cap (stk{rest=Just empty}) of
      Nothing -> empty
      Just p -> p

capLength :: Int -> Stack a -> Stack a
capLength cap stk | cap <= buffmax = stk { maxLength = cap, rest = Nothing }
                  | otherwise = case rest stk of
                      Nothing -> stk { maxLength = cap }
                      Just parent -> stk { maxLength = cap
                                         , rest = Just (capLength newcap parent)
                                         }
  where newcap = (cap - buffmin) `div` 2

-- Can I improve this if things have *just* been adjusted?
top :: Garbled g => Stack g -> GcilMonad (GblMaybe g)
top stk = muxListOffset 1 (buffhead stk) (buffer stk)
null stk = mapM gblIsNothing (buffer stk) >>= GC.andList

-- Same as condOp False _ True, but does not require a dummy 2nd argument
condPop :: Garbled v => GblBool -> Stack v -> GcilMonad (Stack v)
condPop popCond stk = do
  popDone <- null stk >>= GC.not >>= GC.and popCond
  popper <- decoderWithEnable popDone $ buffhead stk
  newbuff <- forM (zip (buffer stk) (drop 1 popper)) $ \(elt,zap) ->
                condNothing zap elt
  newbh <- ifThenElse popDone (constArg 3 (-1)) (constArg 3 0)
        >>= addS (buffhead stk)
  adjust $ stk { buffer = newbuff, buffhead = newbh }

condPush b v stk = condOp b v bitZero stk

-- Does a conditional push followed by a conditional pop. Pushing AND popping
-- in the same call therefore has no effect. Popping an empty stack also has
-- no effect
condOp :: Garbled v => GblBool -> v -> GblBool -> Stack v -> GcilMonad (Stack v)
condOp pushCond pushVal popCond stk = do
  -- TODO get a more efficient decoder for 5 possibilities at different lo
  popDone  <- GC.not pushCond >>= GC.and popCond
  pushDone <- GC.xor popDone pushCond >>= GC.xor popCond -- push AND NOT pop
  popDone  <- null stk >>= GC.not >>= GC.and popDone

  popper   <- decoderWithEnable popDone  $ buffhead stk
  pusher   <- decoderWithEnable pushDone $ buffhead stk
  newbuff  <- forM (zip (buffer stk) (drop 1 popper)) $ \(elt,zap) ->
                condNothing zap elt
  newbuff  <- forM (zip newbuff pusher) $ \(elt,pc) ->
                mux pc elt $ gblMaybe (Just pushVal)
  bhTouch  <- xor pushDone popDone
  -- if popDone then deltaBh == -1
  -- else if pushDone then deltaBh == +1
  -- else deltaBh = 0
  deltaBh  <- GC.concat [bitToInt popDone, bitToInt bhTouch]
  newbh    <- addS deltaBh (buffhead stk) >>= trunc ptrwidth
  adjust $ stk { buffer = newbuff, buffhead = newbh }

adjust :: Garbled v => Stack v -> GcilMonad (Stack v)
adjust stk = if adjusted stk then return $ stk { adjusted = False} else do
  -- things can fail, buff!! things can be Nothing, and parent pops may not work
  needLSlide <- greaterThanU (buffhead stk) (constArg 3 (buffmin+1))
  needPop    <- greaterThanU (constArg 3 buffmin) (buffhead stk)
  needPush   <- GC.and needLSlide =<< GC.not =<< hollowStack
  -- needPush implies not hollowStack, which implies the casting is safe below
  newpar     <- if maxLength stk <= buffmin 
                  then return Nothing
                  else (if knownNothing b0 || knownNothing b1 
                    then condPop needPop oldparent
                    else condOp needPush (castFromJust b0,castFromJust b1) 
                            needPop oldparent) >>= return.Just
  (pop0,pop1) <- liftM distrJust $ top oldparent
  afterPush<- zipMux needLSlide buff (drop 2 buff++[noth,noth])
  newbuff  <- zipMux needPop afterPush (pop0:pop1:take 4 buff)
  deltaBh  <- ifThenElse needLSlide (constArg 3 (-2)) (constArg 3 0)
          >>= ifThenElse needPop  (constArg 3   2 )
  newbh    <- addS deltaBh (buffhead stk)
  return $ trimStack $ stk  { buffer   = newbuff
                , buffhead = newbh
                , rest     = newpar
                , adjusted = True
                }
  where
  buff = buffer stk
  b0 = buff!!0
  b1 = buff!!1
  noth = gblMaybe Nothing
  oldparent = parentStack stk
  hollowStack = gblIsNothing b0

distrJust (GblMaybe _ Nothing)      = (gblMaybe Nothing,gblMaybe Nothing)
distrJust (GblMaybe p (Just (a,b))) = (GblMaybe p (Just a),GblMaybe p (Just b))
