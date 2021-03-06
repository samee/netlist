module Circuit.NetList
( NetInstr(..), Opcode(..), NetBinOp(..), NetUnOp(..), ExtendType(..)
, NetWriter
, netList
, runNetWriter
, addDeallocs -- Forces entire list to be instantiated. Use for small lists only
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
, NetInt (extend,constInt,constIntW,intFromBits,intWidth)
, extendBy
, add
, sub
, equal
, condAdd
, condSub
, shiftLeft
, NetOrd (chainGreaterThan, greaterThan)
, lessThan
, netMin, netMax
, cmpSwap, cmpSwapBy, cmpSwapByM
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
, zipMux
, muxList
, muxListOffset
, decoder
, decoderEn
, decoderREn
, decoderUnit
, NetMaybe
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

import           Control.Monad.State.Strict
import           Control.Monad.StreamWriter
import qualified Control.Monad.Writer as WM
import           Data.Bits
import           Data.Maybe
import           Data.Tuple
import qualified Data.Set as S

import Util

-- In theory, we should have a different type for Non-const netbits
data NetInstr = AssignResult NetBits Opcode
              | OutputBits NetBits
              | DeallocBits NetBits
-- All BinOp instructions generated by the functions of this module 
--   will have parameters of equal length. The same is expected of any other
--   module. Functions like add, sub etc. have their own extend routines to 
--   make this happen.
-- If this changes, so must singleBitOutput
data Opcode   = BinOp NetBinOp NetBits NetBits
              | UnOp NetUnOp NetBits
              | ConcatOp [NetBits]
              | SelectOp Int Int NetBits -- select or trunc
              | ExtendOp ExtendType Int NetBits
              | MuxOp NetBits NetBits NetBits

-- I do miss a chained greater than command BitGtChain Bool
data NetBinOp = BitAdd | BitSub | BitOr | BitAnd | BitXor | BitEq | BitGt
data NetUnOp = BitNot | BitNeg | BitAny | BitParityOdd
data ExtendType = SignExtend | ZeroExtend

newtype NetState = NetState { nextSym :: Int }

type NetWriter a = StateT NetState (StreamWriter [NetInstr]) a

runNetWriter :: Monad m => (NetInstr -> m()) -> NetWriter a -> Int -> m a
runNetWriter out ckt id = runStreamWriter out' $ evalStateT ckt (NetState id)
  where out' = mapM_ out

-- Do not use this on large NetWriter actions, the output list can get too large
--   to fit in memory. Instead, it's better to stream through the instructions
--   using runNetWriter.
netList :: NetWriter a -> Int -> (a,[NetInstr])
netList ckt id = WM.runWriter $ runNetWriter (WM.tell.(:[])) ckt id

-- Need to remove this function, replace all this with non-monadic solutions
-- ... someday. Till then, it helps save memory space in Circuit.NetList.Dimacs
addDeallocs :: [NetBits] -> [NetInstr] -> [NetInstr]
addDeallocs out = reverse.aux (S.fromList (map varid out))
                         .reverse.filter notDealloc where
  notDealloc (DeallocBits _) = False
  notDealloc _ = True
  aux _ [] = []
  aux visited (instr:rest) | deadCode  = aux visited rest
                           | otherwise = newDeallocs ++ instr:aux visited' rest
    where
    newDeallocs = map DeallocBits newlyUsed
    deadCode = if isAssign then newdef `S.notMember` visited else False
    (isAssign,newdef) = case instr of 
      AssignResult v _ -> (True, varid v) 
      _                -> (False,undefined)
    visited' = S.union (if isAssign then S.delete newdef visited 
                                    else visited) 
                       (S.fromList $ map varid newlyUsed)
    newlyUsed = filter ((`S.notMember` visited).varid) 
              $ filter (isSymbolic) (used instr)
  
  used (OutputBits v)     = [v]
  used (AssignResult _ op) = opUsed op
  opUsed (BinOp _ u v)    = [u,v]
  opUsed (UnOp _ v)       = [v]
  opUsed (ConcatOp vs)    = vs
  opUsed (SelectOp _ _ v) = [v]
  opUsed (ExtendOp _ _ v) = [v]
  opUsed (MuxOp c u v)    = [c,u,v]

varid (NetBits { bitValues = VarId id }) = id
isSymbolic (NetBits { bitValues = VarId _ }) = True
isSymbolic _ = False

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
  constIntW :: Int -> Int -> a
  intFromBits :: NetBits -> a
  intWidth :: a -> Int

extendBy w a = extend (w + intWidth a) a

class NetOrd a where
  chainGreaterThan :: NetBool -> a -> a -> NetWriter NetBool
  greaterThan :: a -> a -> NetWriter NetBool

  greaterThan = chainGreaterThan netFalse

lessThan :: NetOrd a => a -> a -> NetWriter NetBool
lessThan = flip greaterThan

instance (NetOrd p,NetOrd q) => NetOrd (p,q) where
  chainGreaterThan c (p1,q1) (p2,q2) = do
    c <- chainGreaterThan c q1 q2
    chainGreaterThan c p1 p2

  greaterThan (p1,q1) (p2,q2) = do
    c <- greaterThan q1 q2
    chainGreaterThan c p1 p2

instance (NetOrd p,NetOrd q,NetOrd r) => NetOrd (p,q,r) where
  chainGreaterThan c (p1,q1,r1) (p2,q2,r2) = do
    c <- chainGreaterThan c r1 r2
    c <- chainGreaterThan c q1 q2
    chainGreaterThan c p1 p2

  greaterThan (p1,q1,r1) (p2,q2,r2) = do
    c <- greaterThan r1 r2
    c <- chainGreaterThan c q1 q2
    chainGreaterThan c p1 p2

-- Compares non-empties to be greater than empties
-- All empties are equal, non-empties are compared by value parts.
instance NetOrd a => NetOrd (NetMaybe a) where
  chainGreaterThan c (NetMaybe _ Nothing) (NetMaybe _ Nothing) = return c
  chainGreaterThan c (NetMaybe p1 (Just _)) (NetMaybe _ Nothing) = netOr c p1
  chainGreaterThan c (NetMaybe _ Nothing) (NetMaybe p2 (Just _)) = 
    netAnd c =<< netNot p2
  chainGreaterThan c (NetMaybe p1 (Just v1)) (NetMaybe p2 (Just v2)) = do
    bz <- netOr p1 p2
    mux bz c =<< chainGreaterThan c (p1,v1) (p2,v2)

  greaterThan (NetMaybe _ Nothing) _ = return netFalse
  greaterThan (NetMaybe p1 (Just _)) (NetMaybe _ Nothing) = return p1
  greaterThan (NetMaybe p1 (Just v1)) (NetMaybe p2 (Just v2)) = do
    bz <- netOr p1 p2
    netAnd bz =<< greaterThan (p1,v1) (p2,v2)


netMax a b = do c <- greaterThan a b
                mux c b a

netMin a b = do c <- greaterThan a b
                mux c a b

cmpSwap a b = do c <- greaterThan a b
                 condSwap c a b

cmpSwapBy f a b = do
  c <- greaterThan (f a) (f b)
  condSwap c a b

cmpSwapByM f a b = do
  fa <- f a
  fb <- f b
  c <- greaterThan fa fb
  condSwap c a b

newtype NetUInt = NetUInt { uIntBits :: NetBits }
newtype NetSInt = NetSInt { sIntBits :: NetBits }

instance NetInt NetUInt where
  extend w a = liftM NetUInt $ zextendBits w (uIntBits a)
  constIntW w x = NetUInt $ NetBits { bitWidth = w, bitValues = ConstMask x }
  constInt x = NetUInt $ NetBits  { bitWidth = valueSize x
                                  , bitValues = ConstMask x }
  intFromBits = NetUInt
  intWidth = bitWidth.uIntBits

instance NetInt NetSInt where
  extend w a = liftM NetSInt $ sextendBits w (sIntBits a)
  constIntW w x = NetSInt $ NetBits { bitWidth = w, bitValues = ConstMask x }
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

instance NetOrd NetBool where
  chainGreaterThan r a b = do
    ax <- bitConcat =<< sequence [bitify a, bitify r]
    bx <- bitConcat.(:[constBits 1 0]) =<< bitify b
    lsb <=< emit $ BinOp BitGt ax bx

  greaterThan a b = netAnd a =<< netNot b

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

condAdd c a b = add a =<< mux c (constInt 0) b
condSub c a b = sub a =<< mux c (constInt 0) b

shiftLeft :: NetInt a => Int -> a -> NetWriter a
shiftLeft amt x = do z <- bitify x
                     liftM intFromBits $ bitConcat [z,constBits amt 0]

fixWidth :: NetInt a => a -> a -> NetWriter (a,a)
fixWidth a b | aw > bw = do b' <- extend aw b; return (a,b')
             | aw < bw = do a' <- extend bw a; return (a',b)
             | otherwise = return (a,b)
             where aw = intWidth a; bw = intWidth b

data NetBits = NetBits  { bitWidth :: Int
                        , bitValues :: BitSym
                        }

data BitSym = ConstMask Int | VarId Int deriving Show

constBits w v = NetBits w (ConstMask v)

conjureBits w id = NetBits { bitWidth = w, bitValues = VarId id }

nextBitId :: NetWriter Int
nextBitId = gets nextSym

newBits :: Int -> NetWriter NetBits
newBits w = do id <- state $ \(NetState id) -> (id,NetState $ id+1)
               return $ conjureBits w id

singleBitOutput (BinOp BitEq _ _) = True
singleBitOutput (BinOp BitGt _ _) = True
singleBitOutput (BinOp _ _ _) = False
singleBitOutput (UnOp BitNot _ ) = False
singleBitOutput (UnOp _ _) = True
singleBitOutput _ = False

emit opcode = do v <- newBits $ resultWidth opcode
                 lift $ tell $ [AssignResult v opcode]
                 return v

resultWidth (ExtendOp _ w v) = max w $ bitWidth v
resultWidth (SelectOp a b _) = b - a
resultWidth (ConcatOp l) = sum $ map bitWidth l
resultWidth (MuxOp _ u _) = bitWidth u
resultWidth op | singleBitOutput op = 1 
               | otherwise = argWidth op

argWidth (BinOp _ x _) = bitWidth x
argWidth (UnOp _ x) = bitWidth x

checkWidth f a b | bitWidth a /= bitWidth b = undefined
                 | knownConst a && knownConst b 
                    = return $ a { bitValues = ConstMask $ constBinOp f a b }
                 | otherwise =  emit (BinOp f a b)

-- These two functions do evil casting, used only from checkWidth
constBinOp op av bv = case op of BitAnd -> a .&. b
                                 BitOr  -> a .|. b
                                 BitXor -> xor a b
                                 BitEq  -> b2i (a==b)
                                 BitGt  -> b2i (a>b)
                                 BitAdd -> a+b
                                 BitSub -> a-b
  where a = castFromConst av
        b = castFromConst bv
        b2i c = if c then 1 else 0

castFromConst (NetBits { bitValues = ConstMask x }) = x

muxBits :: NetBool -> NetBits -> NetBits -> NetWriter NetBits
{-
-- This version was used before OpCode had a 'MuxOp'
muxBits c a b = do x <- bitwiseXor a b
                   cx <- bitRepeat (bitWidth a) c
                   bitwiseXor a =<< bitwiseAnd cx x
                   -}
muxBits c a b | bitWidth a /= bitWidth b = undefined
              | knownTrue  c = return b
              | knownFalse c = return a
              | otherwise = do c' <- bitify c; emit $ MuxOp c' a b

-- Avoids using bitwiseXor, since that results in constant propagation
-- Returns the ID of the variable output
newOutput :: NetBits -> NetWriter Int
newOutput a = do a' <- if knownConst a 
                          then emit $ BinOp BitXor a (constBits (bitWidth a) 0)
                          else return a
                 lift $ tell [OutputBits a']
                 return $ varid a'

lsb a | bitWidth a == 1 = return . NetBool . bitValues $ a
      | otherwise       = liftM (NetBool . bitValues) $ bitSelect 0 1 a
msb a | aw == 1   = return . NetBool . bitValues $ a
      | otherwise = liftM (NetBool . bitValues) $ bitSelect (aw-1) aw a
  where aw = bitWidth a

dropLsb a = bitSelect 1 (bitWidth a) a
dropMsb a = bitSelect 0 (bitWidth a-1) a

splitLsb a = liftM2 (,) (lsb a) (dropLsb a)
splitMsb a = liftM2 (,) (msb a) (dropMsb a)

bitRepeat :: Int -> NetBool -> NetWriter NetBits
bitRepeat n b = bitify b >>= sextendBits n

class BitBunch a where bitify :: a -> NetWriter NetBits
instance BitBunch NetUInt where bitify = return . uIntBits
instance BitBunch NetSInt where bitify = return . sIntBits
instance BitBunch NetBool where bitify = return . NetBits 1 . boolValue
instance BitBunch NetBits where bitify = return

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

knownConst (NetBits { bitValues = ConstMask _ }) = True
knownConst _ = False

zextendConst (NetBits{bitValues=ConstMask x}) w1 w2 
  | x >=0 = x
  | x < 0 = ((shift 1 w1)-1) .&. x

sextendConst (NetBits{bitValues=ConstMask x}) w1 w2 = topbits .|. bottom where
  topbits = if testBit x (w1-1) 
               then xor ((shift 1 w2)-1) ((shift 1 w1)-1)
               else 0
  bottom = x .&. ((shift 1 w1)-1)

zextendBits w a | w <= w' = return a
                | knownConst a = return $ a {bitWidth = w, bitValues = ex}
                | otherwise = emit $ ExtendOp ZeroExtend w a
                where w' = bitWidth a
                      ex = ConstMask $ zextendConst a w' w
sextendBits w a | w <= w' = return a
                | knownConst a = return $ a {bitWidth = w, bitValues = ex}
                | otherwise = emit $ ExtendOp SignExtend w a
                where w' = bitWidth a
                      ex = ConstMask $ sextendConst a w' w
bitwiseGreater = checkWidth BitGt
bitwiseEqual = checkWidth BitEq

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

zipMux c a b = mapM (uncurry $ mux c) $ zip a b

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
    | hi <= 0 || imax <= lo || lo==hi = return []
    | lo<0 = aux en 0 hi i
    | hi>imax = aux en lo imax i
    | w == 0 || hi-lo == 1  = return [en]
    | otherwise = do
        (b ,i')   <- splitMsb i
        (en1,en2) <- decoderUnit en b
        liftM2 (++) (aux en1 lo hi i') (aux en2 (lo-half) (hi-half) i')
      where
      imax = 2^w
      w = bitWidth i
      half = imax `div` 2

decoderUnit en b = do p <- netAnd b en
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
netFromJust (NetMaybe p Nothing) 
  | knownFalse p = error "netFromJust casting known nothing"
  | otherwise = error "netMaybe data missing"
netFromJust (NetMaybe p (Just x)) = x

knownNothing (NetMaybe p _) = knownFalse p
netIsNothing (NetMaybe p _) = netNot p

condZap c (NetMaybe p mb) = do p' <- netAnd p =<< netNot c
                               return $ NetMaybe p' mb

netCaseMaybe f (NetMaybe _  Nothing) = f Nothing
netCaseMaybe f (NetMaybe p (Just x)) = do
  r1 <- f Nothing
  r2 <- f (Just x)
  mux p r1 r2

condModMaybe :: (NetBool -> b -> NetWriter b)
             -> (a -> NetBool -> b -> NetWriter b)
             ->  NetMaybe a -> NetBool -> b -> NetWriter b
condModMaybe nm _ (NetMaybe _ Nothing) c x = nm c x
condModMaybe nm jm (NetMaybe p (Just v)) c x = do
  (nc,jc) <- decoderUnit c p
  jm v jc =<< nm nc x
