module Circuit.Array where

import Control.Monad
import qualified Data.Array as A

import Circuit.Internal.Array as CA
import Circuit.NetList as NL
import Util

newtype NetArray a = NetArray { elt :: A.Array Int a }

repeatArray :: Monad m => Int -> m a -> m (NetArray a)
repeatArray n eltmaker = liftM listArray $ replicateM n $ eltmaker
-- repeatArray n eltmaker = liftM listArray $ sequence $ replicate n $ eltmaker

listArray :: [a] -> NetArray a
listArray l = NetArray  { elt = A.listArray (0,length l-1) l }

elems :: NetArray a -> [a]
elems arr = A.elems $ elt arr
arraySize arr = (+1) $ snd $ A.bounds $ elt $ arr

get i arr = elt arr A.! i
put i v arr = arr { elt = elt arr A.// [(i,v)] }  

writeArray :: Swappable a 
           => NetArray a -> [(NetUInt,a)] -> NetWriter (NetArray a)
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

-- I have to change this later when I want arrays of non-integers
-- Right now I do not have a clean way of doing an Either a b type in circuits
readArray :: NetInt a => NetArray a -> [NetUInt] -> NetWriter [a]
readArray arr addrs = do --elts <- mapM (extend eltw) (elems arr)
                         CA.readArray readSpecs (elems arr) addrs
  where
  eltw = maximum $ map intWidth (elems arr)
  serw  = indexSize $ length addrs
  mixw  = max eltw serw
  unambigLeft = Left :: NetUInt -> Either NetUInt NetUInt
  readSpecs :: NetInt a => 
    ReadSpecs NetWriter a NetUInt NetUInt (NetBool,NetBits) 
                                          (NetMaybe(NetUInt,a))
  -- Convention: Left  == Serial == True
  --             Right == Value  == False
  readSpecs = CA.ReadSpecs
    { rsMixFromValue  = mixFromEither mixw . Right
    , rsMixFromSerial = mixFromEither mixw . unambigLeft . constInt
    , rsMixToValue = mixCast eltw
    , rsIfMixIsValue = muxOnEither
    , rsConstAddr = return . constInt
    , rsConstSerial = return . constInt
    , rsArrayIndex = valueBeforeRead
    , rsSift = swapOnJustRight
    , rsFromMaybe = return . netFromJust
    , rsToMaybe = return . netJust
    , rsNoPair = netNoth
    }
  muxOnEither mix eltRes serialRes = do
    eltRes <- mixCast eltw mix >>= eltRes
    serRes <- mixCast serw mix >>= serialRes
    tp <- mixType mix
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

mixFromEither :: NetInt i => Int -> Either NetUInt i
                          -> NetWriter (NetBool,NetBits)
mixFromEither w eith = case eith of
  Left serial -> do z <- bitify =<< extend w serial; return (netTrue,z)
  Right value -> do z <- bitify =<< extend w value ; return (netFalse,z)

mixCast w (_,mix) = liftM intFromBits $ bitTrunc w mix

mixType = return.fst

-- First compares by address, then by type if that fails
-- if mix is value that comes first, if serial, it comes later
valueBeforeRead a@(addrA,(at,_)) b@(addrB,(bt,_)) = do
  c <- greaterThan at bt
  c <- chainGreaterThan c addrA addrB
  condSwap c a b

------------------------------------ Bad versions ----------------------------

badReadArray :: Swappable a => NetArray a -> [NetUInt] -> NetWriter [a]
badReadArray arr inds = forM inds (\i -> muxList i (elems arr))

badWriteArray :: Swappable a => NetArray a -> [(NetUInt,a)] 
              -> NetWriter (NetArray a)
badWriteArray arr cmd = foldM (\arr (i,v) -> writeBad i v arr) arr cmd
  where
  writeBad ind val arr = do
    en <- decoder ind
    liftM listArray $ forM (zip en $ elems arr) (\(en,elt) -> mux en elt val)
