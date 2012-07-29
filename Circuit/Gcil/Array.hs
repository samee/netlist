module Circuit.Gcil.Array where

import Control.Monad
import qualified Data.Array as A
import Debug.Trace
import Prelude as P -- Me and my laziness

import Circuit.Array as CA
import Circuit.Gcil.Compiler as GC
import Util

-- TODO resize elements entering the array

data GblArray a = GblArray { elt :: A.Array Int a, eltWidth :: Int }

inputArray w party n = liftM (listArray w)
  $ sequence $ replicate n $ GC.newInput w party
listArray :: Garbled g => Int -> [g] -> GblArray g
listArray w l | P.not equalWidths = error "GblArray elements width mismatch"
              | otherwise = GblArray  { elt = A.listArray (0,length l-1) l
                                      , eltWidth = w 
                                      }
  where equalWidths = all ((w==).bitWidth) l

elems :: Garbled g => GblArray g -> [g]
elems arr = A.elems $ elt arr
arraySize arr = (+1) $ snd $ A.bounds $ elt $ arr

get i arr = elt arr A.! i
put i v arr = arr { elt = elt arr A.// [(i,v)] }  

resizeUInt w i | w == t = return i
               | w > t  = zextend w i
               | w < t  = trunc w i
               where t = gblWidth i

-- Addresses are assumed to have gblWidth == indexSize (arraySize arr)
writeArray :: Garbled g => GblArray g -> [(GblInt,g)] -> GcilMonad (GblArray g)
writeArray arr cmd = do
    cmd <- mapM resizeCmd cmd
    newElements <- CA.writeArray writeSpecs (elems arr) cmd
    return $ listArray (eltWidth arr) newElements
  where
  eltw  = eltWidth arr
  addrw = indexSize $ arraySize arr
  serw  = indexSize $ length cmd
  resizeCmd (addr,val) = do addr <- resizeUInt addrw addr; return (addr,val)
  writeSpecs = CA.WriteSpecs 
    { wsConstAddr = return . constArg addrw
    , wsConstSerial = return . constArg serw
    , wsArrayIndex = cmpSwapAddrSerial
    , wsNoPair    = gblMaybe Nothing
    , wsFromMaybe = return . castFromJust
    , wsToMaybe   = return . gblMaybe . Just
    , wsIfEq = ifEqualElse
    , wsSift = nothingGreater
    }

-- At which point you realize that GblInt should be three different types
-- signed (sign extend), unsigned (zero extend), and bits (no resize).
-- Then this could be the generic equality comparison
ifEqualElse :: (Garbled g, Garbled g2)
  => g2 -> g2 -> g -> g -> GcilMonad g
ifEqualElse a b t f = do 
  (a,b) <- equalSize a b
  az <- bitify a
  bz <- bitify b
  c  <- equalU az bz
  mux c f t

nothingGreater a b = do  
  (a@(GblMaybe ap ad),b@(GblMaybe bp bd)) <- equalSize a b
  anp <- bitNot ap
  bnp <- bitNot bp
  c <- greaterByBits (GblMaybe anp ad) (GblMaybe bnp bd)
  condSwap c a b

cmpSwapAddrSerial a@(aAddr,aSerial,_) b@(bAddr,bSerial,_) = do
  c <- greaterByBits (aAddr,aSerial) (bAddr,bSerial)
  condSwap c a b

-- Addresses are assumed to have gblWidth == indexSize (arraySize arr)
readArray :: Garbled g => GblArray g -> [GblInt] -> GcilMonad [g]
readArray arr addrs = mapM resizeAddr addrs >>= 
                      CA.readArray readSpecs (elems arr) 
  where
  eltw = eltWidth arr
  addrw = indexSize $ arraySize arr
  serw  = indexSize $ length addrs
  mixw  = max eltw serw
  sampleElt = get 0 arr
  sampleSer = constArg serw 0
  resizeAddr addr = resizeUInt addrw addr
  readSpecs = CA.ReadSpecs
    { rsMixFromValue  = mixFromEither sampleElt mixw . Right
    , rsMixFromSerial = mixFromEither sampleElt mixw . Left . constArg serw
    , rsMixToValue = mixCast sampleElt eltw
    , rsIfMixIsValue = muxOnEither
    , rsConstAddr = return . constArg addrw
    , rsConstSerial = return . constArg serw
    , rsArrayIndex = valueBeforeRead
    , rsSift = swapOnGreaterByBits
    , rsFromMaybe = return . castFromJust
    , rsToMaybe = return . gblMaybe . Just
    , rsNoPair = gblMaybe Nothing
    }
  muxOnEither mix eltRes serialRes = do
    eltRes <- mixCast sampleElt eltw mix >>= eltRes
    serRes <- mixCast sampleSer serw mix >>= serialRes
    tp <- mixType mix
    mux tp eltRes serRes

swapOnGreaterByBits a b = do c <- greaterByBits a b
                             condSwap c a b

mixFromEither :: Garbled g => g -> Int -> Either GblInt g 
              -> GcilMonad (GblBit,GblInt)
mixFromEither dummy w eith = case eith of
                                  Left serial -> encode bitOne  serial
                                  Right value -> encode bitZero value
  where
  encode tp v = do
    vz <- bitify v
    dt <- GC.concat [vz,constArg (w-bitWidth v) 0]
    return (tp,dt)

mixCast s w (_,mix) = (liftM head $ unconcat [w] mix) >>= unbitify s

mixType = return.fst

-- Fragile code: first compares by address, then by type if that fails
-- if mix is value that comes first, if serial, it comes later
valueBeforeRead a@(addrA,mixA) b@(addrB,mixB) = do
  c <- greaterByBits a b
  condSwap c a b

instance Garbled g => Garbled (GblArray g) where
  bitWidth g = eltWidth g * length (elems g)
  bitify g = do
    zl <- mapM bitify (elems g)
    GC.concat zl
  unbitify s zfull  | fullLen `mod` w /= 0 = undefined
                    | null $ elems s       = undefined
                    | otherwise = do
                        zelt <- unconcat (replicate (fullLen`div`w) w) zfull
                        liftM (listArray w) $ mapM (unbitify (elt s A.! 0)) zelt
                    where
                      fullLen = gblWidth zfull
                      w = eltWidth s
  equalSize as bs | arraySize as /= arraySize bs = undefined
                  | eltWidth as == eltWidth bs   = return (as,bs)
                  | otherwise = do 
                    (as,bs) <- liftM unzip 
                        $ mapM (uncurry equalSize) (zip (elems as) (elems bs))
                    let w = bitWidth (head as)
                    return (listArray w as, listArray w bs)
                    

