-- Using the same pattern as Circuit.NetList.Gcil, I want this:
-- dimacsList $ do v <- freshInt width
--                 v2 <- freshInt width2
--                 outputs <- liftNet $ awesomeCircuit v v2
--                 dmAssert =<< f output -- assertEq is good enough for cycles
--                 dmShow $ "hello world: "++show outputs
--
-- dimacsShow works with FormatDimacs

{-# LANGUAGE FlexibleInstances #-}

module Circuit.NetList.Dimacs
( freshInt, freshBool, freshBits
, liftNet
, liftBunch
, DmMonad
, dimacsList
, dmAssert
, (-|-)
, dmPutStrLn
, DmShow(..)
, burnSatQuery
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.State.Strict
import Data.Bits
import qualified Data.HashTable as Ht
import Data.List
import Data.Maybe
import Debug.Trace
import System.IO

import Circuit.NetList
import Util

data DimacsInstr = Clause [Int]
                 | ShowString String
                 | ShowBits BitFormat [Int] -- msb first in template, not here

data BitFormat = UIntFormat | SIntFormat | BoolFormat

data DmState = DmState { symbolTable :: Ht.HashTable Int [Int]
                       , nextVar :: !Int
                       , nextNetBits :: !Int
                       }

type DmMonad = WriterT [DimacsInstr] (StateT DmState IO)

-- returns variable count in circuit
dimacsList :: DmMonad a -> IO (Int,[DimacsInstr])
dimacsList ckt = do 
  ht <- Ht.new (==) Ht.hashInt
  (cl,endState) <- runStateT (execWriterT ckt) (init ht)
  return (nextVar endState-1, Clause [1]:cl)
  where init ht = DmState {symbolTable=ht, nextVar=2, nextNetBits=1}

liftNet :: NetWriter a -> DmMonad a
liftNet m = do ((a,endId),l) <- gets $ netList addend . nextNetBits
               mapM_ compileNetInstr l
               modify $ \dmstate -> dmstate { nextNetBits = endId }
               return a
  where addend = do r <- m
                    end <- nextBitId
                    return (r,end)

-- A complete hack! A somewhat more memory-efficient version of liftNet
-- that works only for BitBunch results (great for NetBool)
liftBunch :: BitBunch a => NetWriter a -> DmMonad a
liftBunch m = do ((bz,b,endId),l) <- gets $ netList addend . nextNetBits
                 mapM_ compileNetInstr $ addDeallocs [bz] l
                 modify $ \dmstate -> dmstate { nextNetBits = endId }
                 return b
  where addend = do r <- m
                    end <- nextBitId
                    rz <- bitify r
                    return (rz,r,end)

reindexBits (NetBits { bitValues = VarId id }) l = do
  ht <- gets symbolTable
  liftIO $ Ht.insert ht id l

unindexBits (NetBits { bitValues = VarId id}) = do
  ht <- gets symbolTable
  liftIO $ Ht.delete ht id
unindexBits (NetBits { bitValues = ConstMask _ }) = return ()

netIdPlusPlus s = nxt `seq` (id,s{nextNetBits=nxt}) where id = nextNetBits s
                                                          nxt = id+1
varIdPlusPlus s = nxt `seq` (id,s{nextVar=nxt}) where id = nextVar s
                                                      nxt = id+1

freshBits w = do id <- state netIdPlusPlus
                 let z = conjureBits w id
                 reindexBits z =<< replicateM w (state varIdPlusPlus)
                 return z

freshInt :: NetInt a => Int -> DmMonad a
freshInt = liftM intFromBits . freshBits

freshBool = freshBits 1 >>= liftNet . lsb

freshVar = state varIdPlusPlus

bitList (NetBits { bitValues = VarId id }) 
  = do ht <- gets symbolTable
       liftM fromJust $ liftIO $ Ht.lookup ht id
bitList (NetBits {bitValues = ConstMask x, bitWidth = w})
  = return $ map tovar $ bitsOfInt w x
  where tovar True  = dmOneVar
        tovar False = dmZeroVar

bitsOfInt 0 0 = []
bitsOfInt 0 _ = error "width parameter too small"
bitsOfInt w x = map (\i -> testBit x i) [0..w-1]

dmBitify x = bitList =<< liftNet (bitify x)

dmZeroVar = -1
dmOneVar = 1

putClause = tell.(:[]).Clause

dmBitNot :: Int -> DmMonad Int
dmBitNot x = return (-x)

dmBitAnd x y = do z <- freshVar
                  mapM putClause [[-z,x],[-z,y],[-x,-y,z]]
                  return z
dmBitOr x y = do z <- freshVar
                 mapM putClause [[-x,z],[-y,z],[-z,x,y]]
                 return z
dmBitXor x y = do z <- freshVar
                  mapM putClause [[x,y,-z],[x,-y,z],[-x,y,z],[-x,-y,-z]]
                  return z
dmWideAnd x y = mapM (uncurry dmBitAnd) $ zip x y
dmWideOr  x y = mapM (uncurry dmBitOr ) $ zip x y
dmWideXor x y = mapM (uncurry dmBitXor) $ zip x y
dmAndList x = do z <- freshVar
                 putClause $ z:map negate x
                 mapM_ (putClause.(:[-z])) x
                 return z
dmOrList x = do z <- freshVar
                putClause $ -z:x
                mapM_ (putClause.(:[z]).negate) x
                return z
dmXorList [] = return dmZeroVar
dmXorList [x] = return x
dmXorList (x:xs) = dmBitXor x =<< dmXorList xs
                      
dmAssert b = putClause.(:[]) =<< dmOrList =<< dmBitify b

-- Mechanisms for dmShow to work correctly
data FormatToken = UIntTok NetUInt | SIntTok NetSInt | BoolTok NetBool
                 | StringTok String

class DmShow a where 
  dmShow :: a -> [FormatToken]
  dmShowList :: [a] -> [FormatToken]
  dmShowList l = [StringTok "["] 
               ++ intercalate [StringTok ","] (map dmShow l)
               ++ [StringTok "]"]

instance DmShow FormatToken where dmShow = (:[]); dmShowList = id
instance DmShow Char    where 
  dmShow = (:[]).StringTok.(:[]) 
  dmShowList = (:[]).StringTok
instance DmShow NetUInt where dmShow = (:[]).UIntTok
instance DmShow NetSInt where dmShow = (:[]).SIntTok
instance DmShow NetBool where dmShow = (:[]).BoolTok
instance DmShow a => DmShow [a] where dmShow = dmShowList

infixr 4 -|-
a -|- b = dmShow a ++ dmShow b

-- Okay, so it accepts more than just strings, so what?
dmPutStrLn a = tell =<< mapM compileTok (a-|-"\n")

compileTok :: FormatToken -> DmMonad DimacsInstr
compileTok (StringTok s) = return $ ShowString s
compileTok (UIntTok x) = liftM (ShowBits UIntFormat) $ dmBitify x
compileTok (SIntTok x) = liftM (ShowBits SIntFormat) $ dmBitify x
compileTok (BoolTok x) = liftM (ShowBits BoolFormat) $ dmBitify x

dmNegUnit c b = do c' <- dmBitOr b c
                   x  <- dmBitXor b c
                   return (c',x)

dmAddUnit c x y = do s <- dmXorList [x,y,c]
                     c' <- dmBitXor c =<<
                           bind2 dmBitAnd (dmBitXor c x) 
                                          (dmBitXor c y)
                     return (c',s)

dmSubUnit c x y = do s <- dmXorList [x,y,c]
                     c' <- dmBitXor x =<<
                           bind2 dmBitOr (dmBitXor x y)
                                         (dmBitXor x c)
                     return (c',s)

dmNEqUnit c x y = do c' <- dmBitOr c =<< dmBitXor x y
                     return (c',())

dmGtUnit c x y = do xc <- dmBitXor x c
                    xy <- dmBitXor x y
                    c' <- dmBitXor x =<< dmBitAnd xc =<< dmBitNot xy
                    return (c',())


ripple rippleUnit x = mapAccumM rippleUnit dmZeroVar =<< bitList x

ripple2 :: (Int -> Int -> Int -> DmMonad (Int,d)) 
        -> NetBits -> NetBits -> DmMonad (Int,[d])
ripple2 ripple2Unit x y = mapAccumM (uc ripple2Unit) dmZeroVar =<< pairList
  where
  uc f c (x,y) = f c x y
  pairList = liftM2 zip (bitList x) (bitList y)

isClause (Clause _) = True
isClause _ = False

burnSatQuery caseName (varCount,bytecode) 
  = writeCaseFiles caseName $ \qfile tmplfile -> do
      hPutStrLn qfile $ "p cnf "++show varCount++" "++show clauseCount
      forM_ bytecode $ \bc -> case bc of
        Clause l -> hPutStrLn qfile $ unwords (map show l)++" 0"
        ShowString s -> hPutStr tmplfile s
        ShowBits fmt x -> hPutStr tmplfile $ showBits fmt x
  where
  showBits fmt x = tmplFmt fmt++"["++unwords (map show $ reverse x)++"]"
  clauseCount = sum [1 | bc <- bytecode, isClause bc]
  
compileNetInstr (AssignResult res op) = reindexBits res =<< compileOp op
compileNetInstr (OutputBits x) = dmPutStrLn (intFromBits x :: NetUInt)
compileNetInstr (DeallocBits x) = unindexBits x

compileOp (ConcatOp l) =
  liftM (concat.reverse) $ mapM bitList l
compileOp (SelectOp st en x) =
  liftM (take (en-st).drop st) $ bitList x
compileOp (ExtendOp SignExtend w x) = do
  l <- bitList x
  return $ l ++ replicate (w-length l) (last l)
compileOp (ExtendOp ZeroExtend w x) = do
  l <- bitList x
  return $ l ++ replicate (w-length l) dmZeroVar
compileOp (UnOp BitNot x)       = liftM (map negate) $ bitList x
compileOp (UnOp BitNeg x)       = liftM snd $ ripple dmNegUnit x
compileOp (UnOp BitAny x)       = liftM (:[]) $ dmOrList =<< bitList x
compileOp (UnOp BitParityOdd x) = liftM (:[]) $ dmXorList =<< bitList x
compileOp (BinOp BitOr  x y) = join $ dmWideOr  <$> bitList x <*> bitList y
compileOp (BinOp BitAnd x y) = join $ dmWideAnd <$> bitList x <*> bitList y
compileOp (BinOp BitXor x y) = join $ dmWideXor <$> bitList x <*> bitList y
compileOp (BinOp BitAdd x y) = liftM snd $ ripple2 dmAddUnit x y
compileOp (BinOp BitSub x y) = liftM snd $ ripple2 dmSubUnit x y
compileOp (BinOp BitEq  x y) = mapM dmBitNot.(:[]).fst =<< ripple2 dmNEqUnit x y
compileOp (BinOp BitGt  x y) = liftM ((:[]).fst) $ ripple2 dmGtUnit x y

tmplFmt UIntFormat = "$uint"
tmplFmt SIntFormat = "$sint"
tmplFmt BoolFormat = "$bool"

writeCaseFiles caseName f = withSuff ".dimacs" $ \qf -> withSuff ".tmpl" (f qf)
  where withSuff s = withFile ("dimacsOut/"++caseName++s) WriteMode
