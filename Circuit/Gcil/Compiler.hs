module Circuit.Gcil.Compiler where

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy
--import qualified Data.ByteString.Lazy.Char8 as B
import Data.Tuple
import Debug.Trace
import Prelude as P
import System.IO

import Circuit.Array
import Util

data GcilState = GcilState { nxtIndex :: Int
                           , compileTarget :: Handle
                           , totalAndGates :: !Int
                           }
initState handle = GcilState  { nxtIndex = 1
                              , compileTarget = handle
                              , totalAndGates = 0
                              }

andsUsed i = modify (\s -> s { totalAndGates = totalAndGates s + i })
ignoreAndsUsed x = do c <- gets $ totalAndGates
                      r <- x
                      modify (\s -> s { totalAndGates = c })
                      return r

-- Commands in this module are mostly in the GcilMonad. Meaning that
-- the compiler internal state is just an Int and it writes to a String
type GcilMonad = StateT GcilState IO
putLine s = do h <- gets $ compileTarget; lift $ hPutStrLn h s
--putLine s = tell $ B.pack (s++"\n")

getNxtIndex = state (\s@GcilState { nxtIndex = a } -> (a,s {nxtIndex=a+1}))
varName i = "t"++show i

-- A set of garbled bits. Right now, I am not keeping track of party
newtype GblBool = GblBool { bitName :: String }
data GblInt = GblInt { gblName  :: String
                     , gblWidth :: Int
                     }

intToBit g | gblWidth g /= 1 = error $ (show $ gblWidth g)++"-bit int not bool"
           | otherwise       = GblBool $ gblName g
bitToInt b = GblInt { gblName = bitName b, gblWidth = 1 }
bitRepeat 0 _ = return $ constArg 0 0
bitRepeat 1 b = return $ bitToInt b
bitRepeat n b = sextend n $ bitToInt b
bitZero = intToBit $ constArg 1 0
bitOne  = intToBit $ constArg 1 1
not x = bitwiseNot (bitToInt x) >>= return.intToBit
and x y = bitwiseAnd (bitToInt x) (bitToInt y) >>= return.intToBit
or  x y = gcand x y >>= xorList . (:[x,y])
xor x y = bitwiseXor (bitToInt x) (bitToInt y) >>= return.intToBit

class Garbled g where
  bitWidth :: g -> Int
  bitify   :: g -> GcilMonad GblInt
  unbitify :: g -> GblInt -> GcilMonad g
  equalSize:: g -> g -> GcilMonad (g,g)

instance Garbled GblBool  where
  bitWidth _ = 1
  bitify = return.bitToInt
  unbitify _ i = return $ intToBit i
  equalSize a b = return (a,b) -- seriously, if bit sizes start to differ ...

instance Garbled GblInt where
  bitWidth = gblWidth
  bitify x = return x
  unbitify _ x = return x
  -- I expect users to use zextend or sextend as needed
  equalSize x y | gblWidth x /= gblWidth y = error $ "GblInt sizes differ " ++
                                              (show $ gblWidth x) ++ " " ++
                                              (show $ gblWidth y)
                | otherwise = return (x,y)

instance (Garbled a, Garbled b) => Garbled (a,b) where
  bitWidth (a,b) = bitWidth a + bitWidth b
  bitify (a,b) = sequence [bitify a,bitify b] >>= gcconcat
  unbitify (a,b) z = do [za,zb] <- unconcat [bitWidth a,bitWidth b] z
                        ra <- unbitify a za
                        rb <- unbitify b zb
                        return (ra,rb)
  equalSize (a1,b1) (a2,b2) = do  (a1,a2) <- equalSize a1 a2
                                  (b1,b2) <- equalSize b1 b2
                                  return ((a1,b1),(a2,b2))

instance (Garbled a, Garbled b, Garbled c) => Garbled (a,b,c) where
  bitWidth (a,b,c) = bitWidth a + bitWidth b + bitWidth c
  bitify (a,b,c) = sequence [bitify a,bitify b,bitify c] >>= gcconcat
  unbitify (a,b,c) z = do 
    [za,zb,zc] <- unconcat [bitWidth a,bitWidth b,bitWidth c] z
    ra <- unbitify a za
    rb <- unbitify b zb
    rc <- unbitify c zc
    return (ra,rb,rc)
  equalSize (a1,b1,c1) (a2,b2,c2) = do  (a1,a2) <- equalSize a1 a2
                                        (b1,b2) <- equalSize b1 b2
                                        (c1,c2) <- equalSize c1 c2
                                        return ((a1,b1,c1),(a2,b2,c2))

-- Here Nothing means known to be Nothing, but Just means could be either
-- greaterByBits will compare Nothing to be smaller UNTESTED
data GblMaybe a = GblMaybe GblBool (Maybe a)

instance Garbled a => Garbled (GblMaybe a) where
  bitWidth (GblMaybe p Nothing)  = bitWidth p
  bitWidth (GblMaybe p (Just x)) = bitWidth (p,x)
  bitify (GblMaybe p Nothing)  = bitify p
  bitify (GblMaybe p (Just x)) = bitify (p,x)
  unbitify (GblMaybe p Nothing)  z = do p' <- unbitify p z
                                        return $ GblMaybe p' Nothing
  unbitify (GblMaybe p (Just x)) z = do (p',x') <- unbitify (p,x) z
                                        return $ GblMaybe p' (Just x')
  equalSize v1@(GblMaybe p1 x1) v2@(GblMaybe p2 x2) = case (x1,x2) of
    (Nothing,Nothing) -> return (v1,v2)
    (Nothing,Just x2) -> return (GblMaybe p1 (Just x2),v2)
    (Just x1,Nothing) -> return (v1,GblMaybe p2 (Just x1))
    (Just x1,Just x2) -> do (x1,x2) <- equalSize x1 x2
                            return (GblMaybe p1 (Just x1),
                                    GblMaybe p2 (Just x2))

-- Conditionally converts to Nothing using a single AND gate
-- condNothing True x = gblMaybe Nothing
-- condNothing False x = x
condNothing c (GblMaybe _ Nothing) = return $ gblMaybe Nothing
condNothing c (GblMaybe p x) = do  c' <- gcnot c >>= gcand p
                                   return $ GblMaybe c' x

gblNoth = gblMaybe Nothing
gblJust = gblMaybe.Just

gblMaybe Nothing   = GblMaybe bitZero Nothing
gblMaybe (Just x)  = GblMaybe bitOne (Just x)
castFromJust (GblMaybe _ Nothing) = error "Casting GblMaybe known to be Nothing"
castFromJust (GblMaybe _ (Just x))= x
knownNothing (GblMaybe _ Nothing) = True
knownNothing _ = False

caseGblMaybe  :: (Garbled g,Garbled g') 
              => (Maybe g -> GcilMonad g') -> GblMaybe g 
              -> GcilMonad g'
caseGblMaybe f (GblMaybe  _  Nothing)  = f Nothing
caseGblMaybe f (GblMaybe p (Just x))  = do
  nc <- f Nothing
  jc <- f $ Just x
  mux p nc jc

gblIsNothing (GblMaybe _ Nothing) = return bitOne
gblIsNothing (GblMaybe p _) = gcnot p >>= return

newVariable w lineMaker = do  i <- getNxtIndex
                              putLine $ lineMaker $ varName i
                              return $ GblInt (varName i) w

newInput w party = newVariable w (\vn -> 
  ".input "++vn++" "++show party++" "++show w)
newOutput v = putLine $ ".output "++gblName v
constArg w v = GblInt { gblName = show v++":"++show w, gblWidth = w }
calculate op w args = newVariable w (\vn -> vn++" "++unwords (op:args))
constInt w i = GblInt { gblName = show i++":"++show w, gblWidth = w }

compile = hCompile stdout

hCompile :: Handle -> [Int] -> [Int] -> ([GblInt] -> GcilMonad [GblInt])
            -> IO ((),GcilState)
hCompile handle inputWidths inputParties action = runStateT (do
  inputs  <- forM (zip inputWidths inputParties) (uncurry newInput)
  outputs <- action inputs
  forM_ outputs newOutput) (initState handle)

zextend w a = calculate "zextend" w [gblName a,show w]
sextend w a = calculate "sextend" w [gblName a,show w]

fixWidthS op resSize  a b  | aw < bw = do a' <- sextend bw a; f bw a' b
                           | aw > bw = do b' <- sextend aw b; f aw a b'
                           | otherwise = f aw a b
  where  aw = gblWidth a; bw = gblWidth b
         f w a b = calculate op (resSize w) [gblName a,gblName b]

fixWidthU op resSize  a b  | aw < bw = do a' <- zextend bw a; f bw a' b
                           | aw > bw = do b' <- zextend aw b; f aw a b'
                           | otherwise = f aw a b
  where  aw = gblWidth a; bw = gblWidth b
         f w a b = calculate op (resSize w) [gblName a,gblName b]

rigidWidth op a b | aw /= bw  = undefined
                  | otherwise = calculate op aw [gblName a,gblName b]
                  where aw = gblWidth a; bw = gblWidth b

xorList [] = return bitZero
xorList [x] = return x
xorList (x:xs) = xorList xs >>= gcxor x

andList [] = return bitOne
andList [x] = return x
andList (x:xs) = andList xs >>= gcand x

lsb :: GblInt -> GcilMonad GblBool
lsb i = select 0 1 i >>= return.intToBit

msb i = select (w-1) w i >>= return.intToBit where w = gblWidth i

splitLsb :: GblInt -> GcilMonad (GblBool,GblInt)
splitLsb i = do b <- lsb i
                r <- if gblWidth i > 1 then select 1 (gblWidth i) i
                     else return (constArg 0 0)
                return (b,r)

dropMsb i = select 0 (gblWidth i - 1) i

splitMsb i = do b <- msb i
                r <- if gblWidth i > 1 then select 0 (gblWidth i - 1) i
                     else return (constArg 0 0)
                return (b,r)

zipMux c al bl = forM (zip al bl) $ \(a,b) -> mux c a b

-- Returns weird elements if i value >= len
-- muxListOffset 0 i l
muxList i l | len == 1 || w == 0 = return $ head l
            | len == 0 = undefined
            | otherwise = do  (ih,ir) <- splitLsb i
                              mo <- muxList ir lo
                              me <- muxList ir le
                              mux ih me mo
  where
  len = length l
  w   = gblWidth i
  (le,lo) = splitOddEven l

-- Remove the next two muxes as well TODO
-- untested
decoder x = decoderWithEnable bitOne x

decoderUnit en b = do
  y <- gcand en b
  x <- gcxor en y
  return (x,y)

decoderWithEnable en x = aux en x [] where
  aux en x acc | w == 0 = return (en:acc)
               | otherwise = do
                  (xh,xr) <- splitMsb x
                  b <- gcand xh en
                  a <- gcxor b  en
                  acc <- aux b xr acc
                  aux a xr acc
    where w = gblWidth x

-- Essentially the same as muxList (i-off) l, but avoids the subtraction
muxListOffset :: Garbled v => Int -> GblInt -> [v] -> GcilMonad v
muxListOffset off i l | len == 1 || w == 0 = return $ head l
                      | len == 0 = undefined
                      | otherwise = recur
  where 
  recur = do  (ih,ir) <- splitLsb i
              me <- muxListOffset ((off+1)`div`2) ir le
              mo <- muxListOffset (off`div`2) ir lo
              mux ih me mo
  len = length l
  w = gblWidth i
  (le,lo) = (if even off then id else swap) (splitOddEven l)

bitwiseNot a   = calculate  "not" (gblWidth a) [gblName a]
bitwiseAnd a b = do andsUsed (gblWidth a); rigidWidth "and" a b
bitwiseXor a b = rigidWidth "xor" a b
select st en a = calculate "select" (en-st) [gblName a, show st, show en]
trunc sz a = calculate "trunc" sz [gblName a, show sz] -- select 0 sz a
concat as = calculate "concat" wsum (map gblName as) 
  where wsum = sum $ map gblWidth as
unconcat ls a | lensum > gblWidth a = undefined "unconcat lengths out of range"
              | lensum < gblWidth a = addExtraLen
              | otherwise =  do (_,bs) <- mapAccumM (\st len -> do
                                   let end =st+len
                                   b <- select st end a
                                   return (end,b)) 0 $ reverse ls
                                return $ reverse bs
  where
  lensum = sum ls
  addExtraLen = do res <- unconcat (ls++[gblWidth a-lensum]) a
                   return $ init res


addSubCost a b = andsUsed $ P.max (gblWidth a) (gblWidth b)

-- addU may overflow, addWithCarryU won't but produces results a bit wider
addU a b = do r <- addWithCarryU a b
              trunc (gblWidth r - 1) r

addS a b = do addSubCost a b
              r <- fixWidthS "add" (+1) a b
              trunc (gblWidth r - 1) r

-- Assumes a>=b. Unnecessarily uses an extra AND gate
subU a b = do addSubCost a b; fixWidthU "sub" id a b
              
-- if c then a+b else a
condAddS c a b = do d <- ifThenElse c b $ constArg (gblWidth b) 0
                    addS a d

addWithCarryU a b = do addSubCost a b; fixWidthU "add" (+1) a b

----------------------- Compares and swaps --------------------------------

castSingleBit a = unbitify bitZero a
greaterThanU a b = do addSubCost a b 
                      fixWidthU "gtu" (const 1) a b >>= castSingleBit

max a b = do andsUsed $ 2*P.max (gblWidth a) (gblWidth b)
             fixWidthU "max" id a b
min a b = do andsUsed $ 2*P.max (gblWidth a) (gblWidth b)
             fixWidthU "min" id a b

greaterByBits :: Garbled g => g -> g -> GcilMonad GblBool
greaterByBits a b = do  az <- bitify a
                        bz <- bitify b
                        greaterThanU az bz

equalU a b = do andsUsed $ P.max (gblWidth a) (gblWidth b) - 1
                fixWidthU "equ" (const 1) a b >>= castSingleBit

equalByBits :: Garbled g => g -> g -> GcilMonad GblBool
equalByBits a b = do  az <- bitify a
                      bz <- bitify b
                      equalU az bz

-- Swap if c is true
--condSwap :: Garbled g => GblBool -> g -> g -> GcilMonad (g,g)
condSwap c gA gB = do
  (ga,gb) <- equalSize gA gB
  abits <- bitify ga
  bbits <- bitify gb
  when (gblWidth abits/=gblWidth bbits) undefined
  let w = gblWidth abits
  xr  <- bitwiseXor abits bbits
  c'  <- bitRepeat w c
  sw  <- bitwiseAnd xr c'
  ga' <- bitwiseXor sw abits >>= unbitify ga
  gb' <- bitwiseXor sw bbits >>= unbitify gb
  return (ga',gb')

-- c == 0 -> return ga; c == 1 --> return gb
mux c ga gb = condSwap c ga gb >>= return.fst
ifThenElse c rt rf = mux c rf rt

-- Note: function is currently unused
-- chooseFirstOne c x chooses the x corresponding to the first c that is true
-- The last element in x is chosen by default, even if the corresponding 
-- element in c is False or it doesn't exist. Extra elements towards the end 
-- of the lists are ignored
chooseFirstOne _ [] = error "Nothing to choose from in chooseFirstOne"
chooseFirstOne _ [x] = return x
chooseFirstOne [] (x:_) = return x
chooseFirstOne (c:cs) (x:xs) = do r <- chooseFirstOne cs xs
                                  mux c r x


-- Internal use aliases useful when they collide with Prelude
gcand = Circuit.Gcil.Compiler.and
gcnot = Circuit.Gcil.Compiler.not
gcxor = Circuit.Gcil.Compiler.xor
gcconcat = Circuit.Gcil.Compiler.concat
gcmax = Circuit.Gcil.Compiler.max
