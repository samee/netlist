module Circuit.Gcil.Stack where

import qualified Circuit.Gcil.Compiler as GC
import Circuit.Gcil.Compiler (GblMaybe)

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
                      }

buffsize = 5
ptrwidth = 3

empty = Stack { buffer = replicateM buffsize $ gblMaybe Nothing
              , buffhead = constArg ptrwidth 2
              , rest = Nothing
              , adjusted = True
              }

singleton x = condPush True x empty

top stk = muxListOffset 1 (buffhead stk) (buffer stk)
null stk = mapM gblIsNothing (buffer stk) >>= GC.andList

-- Same as condOp False _ True, but does not require a dummy 2nd argument
condPop popCond stk = do
  popDone <- null stk >>= GC.not >>= GC.and popCond
  popper <- decoderWithEnable popDone $ buffhead stk
  newbuff <- forM (zip (buffer stk) (drop 1 popper)) $ \(elt,zap) ->
                condNothing zap elt
  newbh <- ifThenElse popDone (constArg 3 -1) (constArg 3 0)
        >>= addS (buffhead stk)
  adjust $ stk { buffer = newbuff, buffhead = newbh }


-- Does a conditional push followed by a conditional pop. Pushing AND popping
-- in the same call therefore has no effect. Popping an empty stack also has
-- no effect
condOp :: Garbled v => GblBit -> v -> GblBit -> Stack v -> GcilMonad (Stack v)
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
                mux pc elt $ gblMaybe (Just pc)
  bhTouch  <- xor pushDone popDone
  -- if popDone then deltaBh == -1
  -- else if pushDone then deltaBh == +1
  -- else deltaBh = 0
  deltaBh  <- concat [bitToInt popDone, bitToInt bhTouch]
  newbh    <- addS deltaBh (buffhead stk) >>= trunc ptrwidth
  adjust $ stk { buffer = newbuff, buffhead = newbh }

adjust stk = if adjusted stk then return $ stk { adjusted = False} else $ do
  -- things can fail, buff!! things can be Nothing, and parent pops may not work
  needLSlide <- greaterThanU (buffhead stk) (constArg 3 3)
  needPop    <- greaterThanU (constArg 3 2) (buffhead stk)
  needPush   <- GC.and needLSlide <<= GC.not <<= hollowStack
  -- needPush implies not hollowStack, which implies the casting is safe below
  newpar     <- if knownNothing b0 || knownNothing b1 
                  then condPop needPop oldparent
                  else condOp needPush (castFromJust b0,castFromJust b1) 
                          needPop oldparent
  (pop0,pop1) <- liftM distrJust $ top oldparent
  newbuff  <- ifThenElse needLSlide (drop 2 buff++[Nothing,Nothing]) buff
          >>= ifThenElse needPop  (pop0:pop1:take 4 buff)
  deltaBh  <- ifThenElse needPush (constArg 3 (-2)) (constArg 3 0)
          >>= ifThenElse needPop  (constArg 3   2 )
  newbh    <- addS deltaBh (buffhead stk)
  return $ Stack  { buffer   = newbuff
                  , buffhead = newbh
                  , rest     = Just newpar
                  , adjusted = True
                  }
  where
  buff = buffer stk
  b0 = buff!!0
  b1 = buff!!1
  oldparent = case rest stk of Nothing -> empty; Just p -> p
  hollowStack = gblIsNothing b0

distrJust (GblMaybe _ Nothing) = (gblMaybe Nothing,gblMaybe Nothing)
distrJust (GblMaybe p (a,b)) = (GblMaybe p a,GblMaybe p b)
