module Circuit.Stack
( Stack
, empty
, fromList
, capLength
, Circuit.Stack.length
, top
, Circuit.Stack.null
, condPop
, condPush
, condModTop
) where

import Control.Monad
import Circuit.NetList as N
import Data.Tuple
import Util

data Stack a = Stack { buffer :: [NetMaybe a]
                     , headPtr :: NetUInt
                     , parent :: Maybe (Stack (a,a))
                     , pushAdjusted :: Bool
                     , popAdjusted :: Bool
                     , maxLength :: Int
                     }

len = Prelude.length
buffsize = 5
ptrWidth = 3

empty = Stack { buffer = replicate buffsize netNoth
              , headPtr = constIntW ptrWidth 2
              , parent = Nothing
              , pushAdjusted = True
              , popAdjusted = True
              , maxLength = maxBound
              }

-- Just a Stack prefilled with the input elements. The elements will get popped
-- out the order they appear in the list (as if they were pushed in in the 
-- reverse order)
fromList :: [a] -> Stack a
fromList [] = empty
fromList [x] = empty { buffer = [netNoth,netNoth,netJust x
                                ,netNoth,netNoth]
                     , headPtr = constIntW ptrWidth 3
                     , pushAdjusted = False
                     }
fromList [x,y] = empty { buffer = [netJust y,netJust x,netNoth
                                  ,netNoth,netNoth]
                       , headPtr = constIntW ptrWidth 2
                       }
fromList [x,y,z]  = empty { buffer =  [netJust z,netJust y,netJust x
                                      ,netNoth,netNoth]
                          , headPtr = constIntW ptrWidth 3
                          , pushAdjusted = False
                          }
fromList l = (fromList $ take hs l) { 
                parent = Just $ fromList $ map swap $ pairUp $ drop hs l 
                } where hs = if odd $ len l then 3 else 2


-- I know top will never be in the last slot (ensured by pushAdjust)
top stk = muxListOffset (headPtr stk) 1 (init $ buffer stk)

-- Assumes stack is not empty
-- Assumes 1 <= headPtr <= 4
-- Ensured by invariants, just like in condPush
condModTop c x stk = do p <- select2Bits $ headPtr stk
                        write <- decoderREn c 1 5 p
                        initbuff' <- forM (zip write $ init buff) $ \(w,mb) ->
                                      mux w mb (netJust x)
                        return $ stk { buffer = initbuff' ++ [last buff] }
  where
  buff = buffer stk

null stk = do a <- netIsNothing (buffer stk !! 1)
              b <- equal (constInt 2) (headPtr stk)
              netAnd a b

stknull = Circuit.Stack.null

capLength :: Int -> Stack a -> Stack a
capLength cap stk = case parent stk of 
                         Nothing -> capped
                         Just p ->  capped { parent = Just $ capLength plen p }
  where capped = stk { maxLength = cap }
        plen = (cap - 2) `div` 2

trimStack stk = if maxLength stk <= 3 then stk { parent = Nothing } else stk

-- buffer stk !! 4 is assumed empty
length :: Stack a -> NetWriter NetUInt
length stk = do s <- foldM (\s mb -> do 
                       c <- netNot =<< netIsNothing mb
                       condAdd c s (constInt 1)) 
                       (constIntW ptrWidth 0) (take 4 $ buffer stk)
                case parent stk of 
                     Nothing -> return s
                     Just p -> add s =<< shiftLeft 1 =<< Circuit.Stack.length p

select2Bits :: NetUInt -> NetWriter NetUInt
select2Bits i = liftM intFromBits $ bitSelect 0 2 =<< bitify i

-- Assumes that 1 <= headPtr <= 4
-- 1 <= headPtr is ensured by adjustPop, while headPtr <= 4 is ensured
-- by adjustPush, since otherwise we would not have enough space for a push
condPush :: Swappable a => NetBool -> a -> Stack a -> NetWriter (Stack a)
condPush c x stk = do p <- select2Bits $ headPtr stk
                      write <- decoderEn c p
                      hp <- condAdd c (headPtr stk) (constInt 1)
                      newtail <- forM (zip write tl) $ \(w,mb) ->
                                    mux w mb (netJust x)
                      adjustPush $ stk  { buffer = spliceBack newtail
                                        , headPtr = hp }
  where
  tl = rotate 1 $ tail $ buffer stk
  spliceBack newtail = (head $ buffer stk) : rotate (-1) newtail

-- Right rotates a list for positive offset
rotate 0 l = l
rotate off l = tl++hd where (hd,tl) = splitAt p l
                            p = if off < 0 then -off else len l - off

-- Assumes that 1 <= headPtr <= 4
-- headPtr <= 4 is ensured by adjustPush, while 1 <= headPtr is needed
-- if pop is to succeed

condPop :: Swappable a => NetBool -> Stack a -> NetWriter (Stack a)
condPop c stk = do 
  c <- netAnd c =<< netNot =<< stknull stk
  p <- select2Bits $ headPtr stk
  hp <- condSub c (headPtr stk) (constInt 1)
  erase <- decoderEn c hp
  newinit <- forM (zip erase $ init $ buffer stk) $ uncurry condZap
  adjustPop $ stk  { buffer = newinit ++ [buffer stk !! 4]
                   , headPtr = hp
                   }

-- Unless buffer 0 and 1 are known nothing, we need a new parent
adjustPush :: Swappable a => Stack a -> NetWriter (Stack a)
adjustPush stk | pushAdjusted stk = return $ stk { pushAdjusted = False }
               | otherwise = do
  slideLcond <- greaterThan (headPtr stk) (constInt 3)
  newhp      <- condSub slideLcond (headPtr stk) (constInt 2)
  pushC      <- netAnd slideLcond =<< netNot =<< hollowHead buff
  newbuff    <- zipMux slideLcond (take 3 buff) (drop 2 buff) 
                    >>= return. ( ++[netNoth,netNoth] )
  newParent  <- if knownNothing $ head buff then return $ parent stk
                else if mxlen <= 3 then return Nothing
                else liftM Just $ condPush pushC pushItem oldParent
  return $ stk  { buffer = newbuff, headPtr = newhp, parent = newParent
                , pushAdjusted = True
                }
  where
  buff = buffer stk
  hollowHead l = netIsNothing $ head l
  mxlen = maxLength stk
  pushItem = (netFromJust $ buff !! 0, netFromJust $ buff !! 1)
  oldParent = case parent stk of 
                   Nothing -> empty { maxLength = (mxlen - 2) `div` 2 }
                   Just p  -> p

adjustPop :: Swappable a => Stack a -> NetWriter (Stack a)
adjustPop stk | popAdjusted stk = return $ stk { popAdjusted = False }
              | otherwise = do
  slideRcond <- greaterThan (constInt 2) (headPtr stk)
  newhp <- condAdd slideRcond (headPtr stk) (constInt 2)
  (popItems,newParent) <- case parent stk of 
                               Nothing -> return ([netNoth,netNoth],Nothing)
                               Just p  -> do 
                                  pres <- liftM Just $ condPop slideRcond p
                                  popitm <- distrJust =<< top p
                                  return (popitm,pres)
  newbuff <- zipMux slideRcond (take 3 buff) (popItems++take 1 buff)
                 >>= return. ( ++drop 3 buff )
  return $ stk  { buffer = newbuff, headPtr = newhp
                , parent = newParent
                , popAdjusted = True
                }
  where
  buff = buffer stk
  distrJust mbpair = if knownNothing mbpair
                        then return [netNoth,netNoth]
                        else do
                          let (a,b) = netFromJust mbpair
                          c <- netIsNothing mbpair
                          mapM (condZap c.netJust) [a,b]
                          
