module Circuit.Interpreted.Array where

import Data.Maybe

import Circuit.Array

swapIf cond a b = if cond a b then return (b,a) else return (a,b)
swapWith f a b = if f a > f b then return (b,a) else return (a,b)

writeSpec :: Monad m => WriteSpecs m elt Int Int (Maybe (Int,elt))
writeSpec = WriteSpecs  { wsConstAddr = return
                        , wsConstSerial = return
                        , wsArrayIndex = swapIf mixCond
                        , wsNoPair = Nothing
                        , wsFromMaybe = return.fromJust
                        , wsToMaybe = return.Just
                        , wsIfEq = (\a b t f -> 
                            return $ if a==b then t else f)
                        , wsSift = swapIf justLater
                        }

writeArray :: Monad m => [elt] -> [(Int,elt)] -> m [elt]
writeArray arr cmd = Circuit.Array.writeArray writeSpec arr cmd

mixCond (a,i,_) (b,j,_) = if a/=b then a>b else i>j

justLater Nothing (Just _) = True
justLater (Just (a,_)) (Just (b,_)) = a>b
justLater _ _ = False


readSpec :: Monad m 
  => ReadSpecs m elt Int Int (Either Int elt) (Maybe (Int,elt))
readSpec = ReadSpecs { rsMixFromValue  = return.Right
                     , rsMixFromSerial = return.Left
                     , rsMixToValue = return.fromRight
                     , rsIfMixIsValue = selectPair
                     , rsConstAddr = return
                     , rsConstSerial = return
                     , rsArrayIndex = swapIf rightLater
                     , rsSift = swapIf justEarlier
                     , rsFromMaybe = return.fromJust
                     , rsToMaybe = return.Just
                     , rsNoPair = Nothing
                     }

readArray :: Monad m => [elt] -> [Int] -> m [elt]
readArray arr cmd = Circuit.Array.readArray readSpec arr cmd

fromRight (Right i) = i
fromRight (Left _) = undefined

rightLater (a,_) (b,_) | a/=b = a>b
rightLater (_,Left _) (_,Right _) = True
rightLater (_,Left i) (_,Left j) = i>j
rightLater (_,Right _) (_,Left _) = False
rightLater (_,Right _) (_,Right _) = undefined

selectPair (Right i) t f = t i
selectPair (Left i) t f = f i

justEarlier (Just _) Nothing = True
justEarlier (Just (i,_)) (Just (j,_)) = i>j
justEarlier _ _ = False
