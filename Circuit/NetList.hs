module Circuit.NetList
( NetInstr(..), Opcode(..), NetBinOp(..), NetUnOp(..), ExtendType(..)
, NetWriter
, netList
, NetBool
, netFalse
, netTrue
, knownTrue
, knownFalse
, netAnd
, netOr
, netXor
, netNot
, netAnds
, netXors
, NetInt (extend,constInt,intFromBits,intWidth)
, add
, sub
, equal
, condAdd
, NetOrd (chainGreaterThan, greaterThan)
, NetUInt
, NetSInt
, NetBits(..), BitSym(..)
, constBits
, conjureBits
, nextBitId
, newBits -- should normally be used only at the beginning
, muxBits
, newOutput
, lsb
, msb
, splitLsb
, splitMsb
, dropLsb
, dropMsb
, bitRepeat
, BitBunch(bitify)
, bitwiseNot
, bitwiseAnd
, bitwiseXor
, bitSelect
, bitTrunc
, bitConcat
, bitUnconcat
, zextendBits
, sextendBits
, bitwiseGreater
, bitwiseEqual
, Swappable(condSwap,mux)
, ifThenElse
, muxList
, muxListOffset
, decoder
, decoderEn
, decoderREn
, netNoth
, netJust
, netMaybe
, netFromJust
, knownNothing
, netIsNothing
, condZap
, netCaseMaybe
, condModMaybe
) where


-- unexported: newBits width gate

-- Costs will be tracked from NetList.Gcil
-- ignoreAndsUsed will go in NetList.Gcil, where I can create separately
--   create debugging netLists and glue them together. I do not have party
--   info here at all. newInputs will have to go there too. So here I can
--   just come up with new variables and use it, assuming inputs are already
--   created.

{-
Ok so this is how the transition is going to work. First, get the NetWriter
and data types set up here. Copy everything from Circuit.Gcil.Compiler to here.
Make it a drop in replacement. Write up the Gcil backend for this, and test with
some simple circuits (multiply sounds good). Backend :: [Gate] -> IO ()
Ready the SAT backend to make sure we do not have any major design flaws. Test
it with a DIMACS, on 50M gates (stack). Watch out for memory. Do a quick 
benchmarking while you are at it.

With backends ready to go, start the switch. Commit on git, and then change
all the import clauses from Gcil.Compiler to NetList. On test pages, call the
proper backend. Do this for one test at a time, possibly starting with Stack.
Remove/rename Gcil.Compiler. Bye bye!
-}

import Control.Monad.State.Strict
import Control.Monad.Writer
import Data.Tuple

import Util

data NetInstr = AssignResult NetBits Opcode
              | OutputBits NetBits
-- If this changes, so must singleBitOutput
data Opcode   = BinOp NetBinOp NetBits NetBits
              | UnOp NetUnOp NetBits
              | ConcatOp [NetBits]
              | SelectOp Int Int NetBits -- select or trunc
              | ExtendOp ExtendType Int NetBits

data NetBinOp = BitAdd | BitSub | BitOr | BitAnd | BitXor | BitEq | BitGt
data NetUnOp = BitNot | BitNeg | BitAny | BitParityOdd
data ExtendType = SignExtend | ZeroExtend

newtype NetState = NetState { nextSym :: Int }

type NetWriter = WriterT [NetInstr] (State NetState)

netList :: NetWriter a -> Int -> (a,[NetInstr])
netList ckt id = evalState (runWriterT ckt) (NetState id)

newtype NetBool = NetBool { boolValue :: BitSym }

netTrue = NetBool $ ConstMask 1
netFalse = NetBool $ ConstMask 0

knownTrue (NetBool (ConstMask 1)) = True
knownTrue _ = False

knownFalse (NetBool (ConstMask 0)) = True
knownFalse _ = False

boolBinOp :: (NetBits -> NetBits -> NetWriter NetBits) 
          -> NetBool -> NetBool -> NetWriter NetBool
boolBinOp f a b = bind2 f (bitify a) (bitify b) >>= lsb

netAnd a b = boolBinOp bitwiseAnd a b
netOr  a b = boolBinOp bitwiseOr  a b
netXor a b = boolBinOp bitwiseXor a b

netNot :: NetBool -> NetWriter NetBool
netNot a = bind bitwiseNot (bitify a) >>= lsb

netAnds [] = return netTrue
netAnds [x] = return x
netAnds (x1:x2:xs) = netAnd x1 x2 >>= netAnds.(:xs)

netXors [] = return netFalse
netXors [x] = return x
netXors (x1:x2:xs) = netXor x1 x2 >>= netXors.(:xs)

class (Swappable a,BitBunch a) => NetInt a where
  extend :: Int -> a -> NetWriter a
  constInt :: Int -> a
  intFromBits :: NetBits -> a
  intWidth :: a -> Int

extendBy w a = extend (w + intWidth a) a

class NetOrd a where
  chainGreaterThan :: NetBool -> a -> a -> NetWriter NetBool
  greaterThan :: a -> a -> NetWriter NetBool

  greaterThan = chainGreaterThan netFalse

newtype NetUInt = NetUInt { uIntBits :: NetBits }
newtype NetSInt = NetSInt { sIntBits :: NetBits }

instance NetInt NetUInt where
  extend w a = liftM NetUInt $ zextendBits w (uIntBits a)
  constInt x = NetUInt $ NetBits  { bitWidth = valueSize x
                                  , bitValues = ConstMask x }
  intFromBits = NetUInt
  intWidth = bitWidth.uIntBits

instance NetInt NetSInt where
  extend w a = liftM NetSInt $ sextendBits w (sIntBits a)
  constInt x = NetSInt $ NetBits  { bitWidth = 1 + valueSize (abs x)
                                  , bitValues = ConstMask x }
  intFromBits = NetSInt
  intWidth = bitWidth.sIntBits

instance NetOrd NetUInt where
  greaterThan a b = do 
    (a,b) <- fixWidth a b
    lsb =<< emit =<< liftM2 (BinOp BitGt) (bitify a) (bitify b)
  chainGreaterThan r a b = do (a,b) <- fixWidth a b
                              ax <- bitConcat =<< sequence [bitify a,bitify r]
                              bx <- bitConcat.(:[constBits 1 0]) =<< bitify b
                              lsb <=< emit $ BinOp BitGt ax bx

instance NetOrd NetSInt where
  greaterThan a b = do 
    (a',b') <- fixWidth a b
    bind2 signedGreaterByBits (bitify a') (bitify b')
  chainGreaterThan r a b = do
    (a',b') <- fixWidth a b
    rz <- bitify r
    ax <- bitConcat [sIntBits a', rz]
    bx <- bitConcat [sIntBits b', constBits 1 0]
    signedGreaterByBits ax bx

-- Assumes both are already of equal size
signedGreaterByBits :: NetBits -> NetBits -> NetWriter NetBool
signedGreaterByBits a b | aw /= bw = undefined
                        | otherwise = do
  a' <- bitwiseXor a $ constBits aw (2^(aw-1))
  b' <- bitwiseXor b $ constBits bw (2^(aw-1))
  lsb <=< emit $ BinOp BitGt a' b'
  where aw = bitWidth a; bw = bitWidth b

emitIntOp :: NetInt i => NetBinOp -> i -> i -> NetWriter i
emitIntOp op a b = do 
  (a',b') <- fixWidth a b
  liftM2 (BinOp op) (bitify a') (bitify b') >>= emit >>= return.intFromBits

add a b = emitIntOp BitAdd a b
sub a b = emitIntOp BitSub a b
equal a b = emitIntOp BitEq a b >>= bitify >>= lsb

condAdd c a b = do cz <- bitRepeat (intWidth b) c
                   bz <- bitify b
                   add a =<< intFromBits =<< bitwiseAnd bz cz

fixWidth :: NetInt a => a -> a -> NetWriter (a,a)
fixWidth a b | aw > bw = do b' <- extend aw b; return (a,b')
             | aw < bw = do a' <- extend bw a; return (a',b)
             | otherwise = return (a,b)
             where aw = intWidth a; bw = intWidth b

data NetBits = NetBits  { bitWidth :: Int
                        , bitValues :: BitSym
                        }

data BitSym = ConstMask Int | VarId Int

constBits w v = NetBits w (ConstMask v)

conjureBits w id = NetBits { bitWidth = w, bitValues = VarId id }

nextBitId :: NetWriter Int
nextBitId = lift $ gets nextSym

newBits :: Int -> NetWriter NetBits
newBits w = do id <- lift $ state $ \(NetState id) -> (id,NetState $ id+1)
               return $ conjureBits w id

singleBitOutput (BinOp BitEq _ _) = True
singleBitOutput (BinOp BitGt _ _) = True
singleBitOutput (BinOp _ _ _) = False
singleBitOutput (UnOp BitNot _ ) = False
singleBitOutput (UnOp _ _) = True
singleBitOutput _ = False

emit opcode = do v <- newBits $ resultWidth opcode
                 tell $ [AssignResult v opcode]
                 return v

resultWidth (ExtendOp _ w v) = max w $ bitWidth v
resultWidth (SelectOp a b _) = b - a
resultWidth (ConcatOp l) = sum $ map bitWidth l
resultWidth op | singleBitOutput op = 1 
               | otherwise = argWidth op

argWidth (BinOp _ x _) = bitWidth x
argWidth (UnOp _ x) = bitWidth x

checkWidth f a b | bitWidth a == bitWidth b = emit (BinOp f a b)
                 | otherwise = undefined

muxBits :: NetBool -> NetBits -> NetBits -> NetWriter NetBits
muxBits c a b = do x <- bitwiseXor a b
                   cx <- bitRepeat (bitWidth a) c
                   bitwiseXor a =<< bitwiseAnd cx x

newOutput a = tell $ OutputBits a

lsb a | bitWidth a == 1 = return . NetBool . bitValues $ a
      | otherwise       = liftM (NetBool . bitValues) $ bitSelect 0 1 a
msb a | aw == 1   = return . NetBool . bitValues $ a
      | otherwise = liftM (NetBool . bitValues) $ bitSelect (aw-1) aw a
  where aw = bitWidth a

dropLsb a = bitSelect 1 (bitWidth a) a
dropMsb a = bitSelect 0 (bitWidth a-1) a

splitLsb a = liftM2 (,) (lsb a) (dropLsb a)
splitMsb a = liftM2 (,) (msb a) (dropMsb a)

bitRepeat n b = bitify b >>= sextendBits n

class BitBunch a where bitify :: a -> NetWriter NetBits
instance BitBunch NetUInt where bitify = return . uIntBits
instance BitBunch NetSInt where bitify = return . sIntBits
instance BitBunch NetBool where bitify = return . NetBits 1 . boolValue

bitwiseNot = emit . UnOp BitNot 
bitwiseAnd = checkWidth BitAnd
bitwiseOr  = checkWidth BitOr
bitwiseXor = checkWidth BitXor
bitSelect st en a | st>en = undefined
                  | st<0 || st>w = undefined
                  | en<0 || en>w = undefined
                  | st==en = return $ constBits 0 0 
                  | st==0 && en == w = return a
                  | otherwise = emit (SelectOp st en a)
                  where w = bitWidth a
bitTrunc sz a = bitSelect 0 sz a
bitConcat l = emit (ConcatOp l)
bitUnconcat l a = sequence $ reverse theSelects where
  theSelects = map (\(p,q) -> bitSelect p q a) pairlist
  pairlist = zip csum (tail csum)
  csum = scanSum $ reverse l

scanSum l = aux l 0 where
  aux [] init = [init]
  aux (l:ls) init = init : (aux ls $! (l+init))

zextendBits w a | w > bitWidth a = emit (ExtendOp ZeroExtend w a)
                | otherwise = return a
sextendBits w a | w > bitWidth a =  emit (ExtendOp SignExtend w a)
                | otherwise = return a
bitwiseGreater a b = checkWidth BitGt
bitwiseEqual a b = checkWidth BitEq

class Swappable a where
  condSwap :: NetBool -> a -> a -> NetWriter (a,a)
  mux :: NetBool -> a -> a -> NetWriter a

  mux c a b = liftM fst $ condSwap c a b

instance Swappable NetBits where
  mux = muxBits
  condSwap c a b = do x <- bitwiseXor a b
                      cx <- bitwiseAnd x =<< bitRepeat (bitWidth a) c
                      liftM2 (,) (bitwiseXor a cx) (bitwiseXor b cx)

-- This is just retarded!
instance Swappable NetUInt where condSwap = condSwapInt; mux = muxInt
instance Swappable NetSInt where condSwap = condSwapInt; mux = muxInt

condSwapInt c a b = do (a,b) <- fixWidth a b
                       (az,bz) <- bind2 (condSwap c) (bitify a) (bitify b)
                       return (intFromBits az, intFromBits bz)

muxInt c a b = do (a,b) <- fixWidth a b
                  bind2 (mux c) (bitify a) (bitify b) >>= return.intFromBits


instance Swappable NetBool where
  condSwap c a b = do (az,bz) <- bind2 (condSwap c) (bitify a) (bitify b)
                      a' <- lsb az; b' <- lsb bz
                      return (a',b')
  mux c a b = bind2 (mux c) (bitify a) (bitify b) >>= lsb

instance (Swappable a, Swappable b) => Swappable (a,b) where
  condSwap c (a1,b1) (a2,b2) = do (a1',a2') <- condSwap c a1 a2
                                  (b1',b2') <- condSwap c b1 b2
                                  return ((a1',b1'),(a2',b2'))
  mux c (a1,b1) (a2,b2) = do ar <- mux c a1 a2
                             br <- mux c b1 b2
                             return (ar,br)

instance (Swappable a, Swappable b, Swappable c) => Swappable (a,b,c) where
  condSwap cn (a1,b1,c1) (a2,b2,c2) = do 
    (a1',a2') <- condSwap cn a1 a2
    (b1',b2') <- condSwap cn b1 b2
    (c1',c2') <- condSwap cn c1 c2
    return ((a1',b1',c1'),(a2',b2',c2'))

  mux cn (a1,b1,c1) (a2,b2,c2) = do ar <- mux cn a1 a2
                                    br <- mux cn b1 b2
                                    cr <- mux cn c1 c2
                                    return (ar,br,cr)

instance Swappable a => Swappable (NetMaybe a) where
  condSwap _ (NetMaybe _ Nothing) (NetMaybe _ Nothing) 
    = return (netNoth,netNoth)
  condSwap c (NetMaybe p1 (Just x1)) (NetMaybe p2 (Just x2)) = do
    (p1,p2) <- condSwap c p1 p2
    (x1,x2) <- condSwap c x1 x2
    return (NetMaybe p1 (Just x1), NetMaybe p2 (Just x2))
  condSwap c (NetMaybe p1 (Just x)) (NetMaybe p2 Nothing) = do
    (p1,p2) <- condSwap c p1 p2
    return (NetMaybe p1 (Just x), NetMaybe p2 (Just x))
  condSwap c (NetMaybe p1 Nothing) (NetMaybe p2 (Just x)) = do
    (p1,p2) <- condSwap c p1 p2
    return (NetMaybe p1 (Just x), NetMaybe p2 (Just x))


ifThenElse c a b = mux c b a

-- Returns weird elements if i >= len
muxList i l = muxListOffset i 0 l

-- Equivalent to muxList (i-lo) l, but avoid the subtraction
muxListOffset :: Swappable a => NetUInt -> Int -> [a] -> NetWriter a
muxListOffset i lo x = do iz <- bitify i; aux iz lo x
  where 
  aux i lo x | len == 0 = undefined
             | len == 1 || w == 0 = return $ head x
             | otherwise = do
               (b,i') <- splitLsb i
               if w == 1 then mux b (head xe) (head xo)
                         else do re <- aux i' (div (lo+1) 2) xe
                                 ro <- aux i' (div lo 2) xo
                                 mux b re ro
    where len = length x
          (xe,xo) = (if even lo then id else swap) $ splitOddEven x
          w = bitWidth i

-- Returns a list of only (hi-lo) elements, representing outputs [lo,hi)
decoderREn :: NetBool -> Int -> Int -> NetUInt -> NetWriter [NetBool]
decoderREn en lo hi i = bitify i >>= aux en lo hi
  where 
  aux en lo hi i
    | lo>hi = undefined
    | hi <= 0 || imax <= lo = return []
    | w == 0 = return [en]
    | otherwise = do
        (b ,i')   <- splitMsb i
        (en1,en2) <- if hi-lo <= half then return (en,en) else decoderUnit b en
        liftM2 (++) (aux en1 lo hi i') (aux en2 (lo-half) (hi-half) i')
      where
      imax = 2^w
      w = bitWidth i
      half = imax `div` 2

decoderUnit b en = do p <- netAnd b en
                      q <- netXor p en
                      return (q,p)

decoderEn en x = decoderREn en 0 (2^intWidth x) x
decoder x = decoderEn netTrue x

-- Nothing means known to be nothing
-- Just _ means may or may not have data, depending on runtime value of p
data NetMaybe a = NetMaybe NetBool (Maybe a)

netNoth = NetMaybe netFalse Nothing
netJust = NetMaybe netTrue . Just
netMaybe Nothing = netNoth
netMaybe (Just x) = netJust x

-- The most *hated* function in all of existence!
netFromJust p Nothing | knownFalse p = error "netFromJust casting known nothing"
                      | otherwise = error "netMaybe data missing"
netFromJust p (Just x) = x

knownNothing p _ = knownFalse p
netIsNothing p _ = netNot p

condZap c (NetMaybe p mb) = do p' <- netAnd p =<< netNot c
                               return $ NetMaybe p' mb

netCaseMaybe f (NetMaybe _  Nothing) = f Nothing
netCaseMaybe f (NetMaybe p (Just x)) = do
  r1 <- f Nothing
  r2 <- f (Just x)
  mux p r1 r2

condModMaybe :: (Maybe a -> NetBool -> b -> NetWriter b)
             ->  NetMaybe a -> NetBool -> b -> NetWriter b
condModMaybe f (NetMaybe _ Nothing)  c x = f Nothing c x
condModMaybe f (NetMaybe p (Just v)) c x = do
  (c1,c2) <- decoderUnit c p
  f (Just v) c2 =<< f Nothing c1 x
