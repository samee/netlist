module Circuit.Array 
  ( NetArray(..)
  , repeatArray, listArray
  , elems, arraySize, get, put
  , writeListArray
  , Circuit.Array.writeArray, Circuit.Array.readArray, addToArray
  , badReadArray, badWriteArray, badAddToArray
  ) where
-- TODO remove this 'NetArray' data type (and aux functions) if nobody uses it.

import Control.Monad
import qualified Data.Array as A
import Data.List

import qualified Circuit.Sorter as CS
import Circuit.Internal.Array as CA -- TODO comment this out
import Circuit.NetList as NL
import Util

newtype NetArray a = NetArray { elt :: A.Array Int a }

repeatArray :: Monad m => Int -> m a -> m (NetArray a)
repeatArray n eltmaker = liftM listArray $ replicateM n $ eltmaker
-- repeatArray n eltmaker = liftM listArray $ sequence $ replicate n $ eltmaker
-- TODO sifting can now use a stack you know
-- and a stack could use a minsize

listArray :: [a] -> NetArray a
listArray l = NetArray  { elt = A.listArray (0,length l-1) l }

elems :: NetArray a -> [a]
elems arr = A.elems $ elt arr
arraySize arr = (+1) $ snd $ A.bounds $ elt $ arr

get i arr = elt arr A.! i
put i v arr = arr { elt = elt arr A.// [(i,v)] }  

writeArray :: Swappable a 
           => NetArray a -> [(NetUInt,a)] -> NetWriter (NetArray a)
writeArray arr cmd = listArray `liftM` writeListArray (elems arr) cmd

linearPass _ []  = return []
linearPass _ [x] = return [x]
linearPass f (x1:x2:xs) = do (x1,x2) <- f x1 x2
                             (x1:) `liftM` linearPass f (x2:xs)

writeListArray :: Swappable a => [a] -> [(NetUInt,a)] -> NetWriter [a]
writeListArray l cmd = do
  let p1 = zipWith (\i v -> (constInt i,constInt 0,v)) [0..] l
      p2 = zipWith (\p (i,v) -> (i,constInt p,v)) [0..] cmd
  l1 <- CS.merge cswapiv p1 =<< CS.sort cswapiv p2
  l2 <- linearPass markLast $ map (addFlag . dropPad) l1
  (map dropLuggage . drop (length cmd)) `liftM` CS.sort cswapiv l2
  where
  addFlag (i,v) = (netTrue,i,v)
  dropLuggage (_,_,v) = v
  dropPad (i,_,v) = (i,v)
  markLast (_,i1,v1) (_,i2,v2) = do
    neq  <- netNot =<< equal i1 i2
    return ((neq,i1,v1),(netTrue,i2,v2))

ignoreThird (a,b,_) = (a,b)
cswapiv :: (Swappable a, Swappable c, NetOrd a) 
        => (a,NetUInt,c) -> (a,NetUInt,c) 
        -> NetWriter ((a,NetUInt,c),(a,NetUInt,c))
cswapiv = cmpSwapBy ignoreThird
  
           {-
writeArray arr cmd = liftM listArray $ CA.writeArray writeSpecs (elems arr) cmd
  where
  addrw = indexSize $ arraySize arr
  serw  = indexSize $ length cmd
  writeSpecs = CA.WriteSpecs 
    { wsConstAddr = return . constInt
    , wsConstSerial = return . (constInt :: Int -> NetUInt)
    , wsArrayIndex = cmpSwapAddrSerial
    , wsNoPair    = netNoth
    , wsFromMaybe = return . netFromJust
    , wsToMaybe   = return . netJust
    , wsIfEq = \a b t f -> do eq <- equal a b; mux eq f t
    , wsSift = nothingGreater
    }
    -}

-- First compares by nothing, which is placed later. Then compares first
nothingGreater mbA mbB | knownNothing mbB = return (mbA,mbB)
                       | knownNothing mbA = return (mbB,mbA)
                       | otherwise = do
                          anp <- netIsNothing mbA
                          bnp <- netIsNothing mbB
                          let (a,_) = netFromJust mbA; (b,_) = netFromJust mbB
                          c <- greaterThan a b
                          c <- chainGreaterThan c anp bnp
                          condSwap c mbA mbB

cmpSwapAddrSerial a@(aAddr,aSerial,_) b@(bAddr,bSerial,_) = do
  c <- greaterThan aSerial bSerial
  c <- chainGreaterThan c aAddr bAddr
  condSwap c a b

data ReadMix a mix = ReadMix { rmMixFromValue  :: a->NetWriter mix
                             , rmMixFromSerial :: NetUInt->NetWriter mix
                             , rmMixToValue  :: mix->NetWriter a
                             , rmMixToSerial :: mix->NetWriter NetUInt
                             }

readArray :: NetInt a => NetArray a -> [NetUInt] -> NetWriter [a]
readArray arr addrs = readArrayBase rmix arr addrs where
  eltw = maximum $ map intWidth (elems arr)
  serw = indexSize $ length addrs
  mixw = max eltw serw
  mixInt x = bitify =<< extend mixw x
  mixCast w z = liftM intFromBits $ bitTrunc w z
  rmix = ReadMix { rmMixFromValue  = mixInt
                 , rmMixFromSerial = mixInt
                 , rmMixToValue  = mixCast eltw
                 , rmMixToSerial = mixCast serw
                 }

-- I need to have a better way of using arrays of non-integers
readArrayBase :: (Swappable a, Swappable mix)
              => ReadMix a mix -> NetArray a -> [NetUInt] -> NetWriter [a]
readArrayBase rmix arr addrs = CA.readArray readSpecs (elems arr) addrs
  where
  readSpecs = CA.ReadSpecs
    { rsMixFromValue = (\x -> do z <- rmMixFromValue rmix x
                                 return (netFalse,z))
    , rsMixFromSerial= (\x -> do z <- rmMixFromSerial rmix (constInt x)
                                 return (netTrue,z))
    , rsMixToValue   = rmMixToValue rmix . snd
    , rsIfMixIsValue = muxOnEither
    , rsConstAddr    = return . constInt
    , rsConstSerial  = return . constInt
    , rsArrayIndex   = valueBeforeRead
    , rsSift         = swapOnJustRight
    , rsFromMaybe    = return . netFromJust
    , rsToMaybe      = return . netJust
    , rsNoPair       = netNoth
    }
  muxOnEither (tp,bitz) eltRes serialRes = do
    eltRes <- rmMixToValue  rmix bitz >>= eltRes
    serRes <- rmMixToSerial rmix bitz >>= serialRes
    mux tp eltRes serRes

-- First make sure all the Nothing ends up towards left
-- and then among the Just, compare by serial
swapOnJustRight mbA mbB | knownNothing mbA = return (mbA,mbB)
                        | knownNothing mbB = return (mbB,mbA)
                        | otherwise = do
                        ap <- netNot =<< netIsNothing mbA
                        bp <- netNot =<< netIsNothing mbB
                        let  (serA,_) = netFromJust mbA
                             (serB,_) = netFromJust mbB
                        c <- greaterThan serA serB
                        c <- chainGreaterThan c ap bp
                        condSwap c mbA mbB

-- First compares by address, then by type if that fails
-- if mix is value that comes first, if serial, it comes later
valueBeforeRead a@(addrA,(at,_)) b@(addrB,(bt,_)) = do
  c <- greaterThan at bt
  c <- chainGreaterThan c addrA addrB
  condSwap c a b


addToArray :: NetInt i => NetArray i -> [(NetUInt,i)] -> NetWriter (NetArray i)
addToArray arr cmds = do (elts',_,Just(_,last)) <- CA.applyOps opSpecs elts cmds
                         return $ listArray $ init elts' ++ [last]
  where
  elts = elems arr
  opSpecs = OpSpecs { castEltToMix = (\i x -> return (constInt i,x))
                    , castOpToMix  = (\_ x -> return x)
                    , cswpArrayIndex = byAddr
                    , foldInit = Nothing
                    , foldBody = accum
                    , cswpSift = nothingGreater
                    , castMixToElt = return.snd.netFromJust
                    , castMixToResult = return
                    }
  accum Nothing x = return (Just x,netNoth)
  accum (Just (adA,valA)) (adB,valB) = do
    eq <- equal adA adB
    nxtSum <- condAdd eq valB valA
    curOut <- mux eq (netJust(adA,valA)) netNoth
    return (Just(adB,nxtSum),curOut)

byAddr a@(adA,_) b@(adB,_) = do c <- greaterThan adA adB
                                condSwap c a b

------------------------------------ Bad versions ----------------------------

-- TODO change bad* prefix to something more neutral
badReadArray :: Swappable a => NetArray a -> [NetUInt] -> NetWriter [a]
badReadArray arr inds = forM inds (\i -> muxList i (elems arr))

badWriteArray :: Swappable a => NetArray a -> [(NetUInt,a)] 
              -> NetWriter (NetArray a)
badWriteArray arr cmd = foldM (\arr (i,v) -> writeBad i v arr) arr cmd
  where
  writeBad ind val arr = do
    en <- decoderREn netTrue 0 (arraySize arr) ind
    liftM listArray $ forM (zip en $ elems arr) (\(en,elt) -> mux en elt val)
    
badAddToArray arr cmd = foldM (\arr (i,v) -> addBad i v arr) arr cmd
  where
  addBad ind val arr = do
    en <- decoderREn netTrue 0 (arraySize arr) ind
    liftM listArray $ forM (zip en $ elems arr) 
                           (\(en,elt) -> condAdd en elt val)
