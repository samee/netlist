module Circuit.Gcil.Stack
( Stack
, empty
, fromList
, capLength
, top
, Circuit.Gcil.Stack.null
, condPop
, condPush
) where

import Control.Monad
import Circuit.Gcil.Compiler as Gc
import Util

data Stack a = Stack { buffer :: [GblMaybe a]
                     , headPtr :: GblInt
                     , parent :: Maybe (Stack (a,a))
                     , pushAdjusted :: Bool
                     , popAdjusted :: Bool
                     , maxLength :: Int
                     }

buffsize = 5
ptrWidth = 3

empty = Stack { buffer = replicate buffsize Gc.gblNoth
              , headPtr = constArg ptrWidth 2
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
fromList [x] = empty { buffer = [Gc.gblNoth,Gc.gblNoth,Gc.gblJust x
                                ,Gc.gblNoth,Gc.gblNoth]
                     , headPtr = constArg ptrWidth 3
                     , pushAdjusted = False
                     }
fromList [x,y] = empty { buffer = [Gc.gblJust y,Gc.gblJust x,Gc.gblNoth
                                  ,Gc.gblNoth,Gc.gblNoth]
                       , headPtr = constArg ptrWidth 2
                       }
fromList [x,y,z]  = empty { buffer =  [Gc.gblJust z,Gc.gblJust y,Gc.gblJust x
                                      ,Gc.gblNoth,Gc.gblNoth]
                          , headPtr = constArg ptrWidth 3
                          , pushAdjusted = False
                          }
fromList l = (fromList $ take hs l) { 
                parent = Just $ fromList $ pairUp $ drop hs l 
                } where hs = if odd $ length l then 3 else 2


-- I know top will never be in the last slot (ensured by pushAdjust)
top stk = muxListOffset 1 (headPtr stk) (init $ buffer stk)

null stk = do a <- gblIsNothing (buffer stk !! 1)
              b <- equalU (constArg ptrWidth 2) (headPtr stk)
              Gc.and a b

stknull = Circuit.Gcil.Stack.null

capLength :: Int -> Stack a -> Stack a
capLength cap stk = case parent stk of 
                         Nothing -> capped
                         Just p ->  capped { parent = Just $ capLength plen p }
  where capped = stk { maxLength = cap }
        plen = (cap - 2) `div` 2

trimStack stk = if maxLength stk <= 3 then stk { parent = Nothing } else stk

-- Assumes that 1 <= headPtr <= 4
-- 1 <= headPtr is ensured by adjustPop, while headPtr <= 4 is ensured
-- by adjustPush, since otherwise we would not have enough space for a push
condPush :: Garbled a => GblBool -> a -> Stack a -> GcilMonad (Stack a)
condPush c x stk = do p <- select 0 2 $ headPtr stk
                      write <- decoderWithEnable c p
                      hp <- addU (bitToInt c) (headPtr stk)
                      newtail <- forM (zip write tl) $ \(w,mb) ->
                                    mux w mb (gblJust x)
                      adjustPush $ stk  { buffer = spliceBack newtail
                                        , headPtr = hp }
  where
  tl = rotate 1 $ tail $ buffer stk
  spliceBack newtail = (head $ buffer stk) : rotate (-1) newtail

-- Right rotates a list for positive offset
rotate 0 l = l
rotate off l = tl++hd where (hd,tl) = splitAt p l
                            p = if off < 0 then -off else length l - off

-- Assumes that 1 <= headPtr <= 4
-- headPtr <= 4 is ensured by adjustPush, while 1 <= headPtr is needed
-- if pop is to succeed

condPop :: Garbled a => GblBool -> Stack a -> GcilMonad (Stack a)
condPop c stk = do 
  c <- Gc.and c =<< Gc.not =<< stknull stk
  p <- select 0 2 $ headPtr stk
  hp <- condAddS c (headPtr stk) (constArg ptrWidth (-1))
  erase <- decoderWithEnable c hp
  newinit <- forM (zip erase $ init $ buffer stk) $ uncurry condNothing
  adjustPop $ stk  { buffer = newinit ++ [buffer stk !! 4]
                   , headPtr = hp
                   }

-- Unless buffer 0 and 1 are known nothing, we need a new parent
adjustPush :: Garbled a => Stack a -> GcilMonad (Stack a)
adjustPush stk | pushAdjusted stk = return $ stk { pushAdjusted = False }
               | otherwise = do
  slideLcond <- greaterThanU (headPtr stk) (constArg ptrWidth 3)
  newhp <- condAddS slideLcond (headPtr stk) (constArg ptrWidth (-2))
  pushC <- Gc.and slideLcond =<< Gc.not =<< hollowHead buff
  newbuff <- zipMux slideLcond buff $ drop 2 buff ++ [gblNoth,gblNoth]
  newParent <- if knownNothing $ head buff then return $ parent stk
               else if mxlen <= 3 then return Nothing
               else liftM Just $ condPush pushC pushItem oldParent
  return $ stk  { buffer = newbuff, headPtr = newhp, parent = newParent
                , pushAdjusted = True
                }
  where
  buff = buffer stk
  hollowHead l = gblIsNothing $ head l
  mxlen = maxLength stk
  pushItem = (Gc.castFromJust $ buff !! 0, Gc.castFromJust $ buff !! 1)
  oldParent = case parent stk of 
                   Nothing -> empty { maxLength = (mxlen - 2) `div` 2 }
                   Just p  -> p

adjustPop :: Garbled a => Stack a -> GcilMonad (Stack a)
adjustPop stk | popAdjusted stk = return $ stk { popAdjusted = False }
              | otherwise = do
  slideRcond <- greaterThanU (constArg ptrWidth 2) (headPtr stk)
  newhp <- condAddS slideRcond (headPtr stk) (constArg ptrWidth 2)
  (popItems,newParent) <- case parent stk of 
                               Nothing -> return ([gblNoth,gblNoth],Nothing)
                               Just p  -> do 
                                  pres <- liftM Just $ condPop slideRcond p
                                  mbpair <- top p
                                  return (distrJust mbpair,pres)
  newbuff <- zipMux slideRcond buff $ popItems ++ take 4 buff
  return $ stk  { buffer = newbuff, headPtr = newhp
                , parent = newParent
                , popAdjusted = True
                }
  where
  buff = buffer stk
  distrJust (GblMaybe _ Nothing) = [gblNoth,gblNoth]
  distrJust (GblMaybe p (Just (a,b))) = [ GblMaybe p (Just a)
                                        , GblMaybe p (Just b) ]
