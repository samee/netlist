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
-- , dimacsList
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

-- I really should document the layers a little better
data BitLevel = FreshBits NetBits 
              | NetWrap [NetInstr] 
              | ShowCmd [BitLevelShow] 
              | AssertNZ NetBits

data BitLevelShow = BitShow BitFormat NetBits | BLString String

data DimacsInstr = Clause [Int]
                 | ShowString String
                 | ShowBits BitFormat [Int] -- msb first in template, not here

data BitFormat = UIntFormat | SIntFormat | BoolFormat

data DmState = DmState { -- symbolTable :: Ht.HashTable Int [Int]
                       -- , nextVar :: !Int
                         nextNetBits :: !Int
                       }

type DmMonad = WriterT [BitLevel] (State DmState)

compileStep :: Backend be => (be()->be()) -> DmMonad () -> be ()
compileStep step m = do
  forM_ intlCode $ \ic -> case ic of
    FreshBits z -> reindexBits z =<< replicateM (bitWidth z) freshVar
    NetWrap ni  -> forM_ ni $ step.compileNetInstr
    ShowCmd tkl -> forM_ tkl $ step.compileTok
    AssertNZ z  -> step $ compileAssert z

  where
  intlCode = evalState (execWriterT m) (DmState 0)

-- This is the only way I could count variables and clauses 
--   *before* generating them
class (Monad m,Applicative m) => Backend m where
  putClause :: [Int] -> m ()
  compileTok :: BitLevelShow -> m ()
  freshVar :: m Int
  unindexBits :: NetBits -> m ()
  reindexBits :: NetBits -> [Int] -> m ()
  bitList :: NetBits -> m [Int]
  outputBits :: NetBits -> m ()

type BitCounter = State (Int,Int)
instance Backend BitCounter where
  putClause _  = modify (\(v,c) -> let c'=c+1 in c' `seq` (v,c'))
  compileTok _ = return ()
  freshVar     = state (\(v,c) -> let v'=v+1 in v' `seq` (0,(v',c)))
  unindexBits _ = return ()
  reindexBits _ _ = return ()
  bitList x = return $ replicate (bitWidth x) 0
  outputBits _ = return ()

runCounter :: DmMonad () -> (Int,Int)
runCounter m = execState (compileStep id m) (1,1)

-- Compile one instruction at a time please TODO
type BitBlaster = WriterT [DimacsInstr] (StateT BlastState IO)
data BlastState = BlastState { symbolTable :: Ht.HashTable Int [Int]
                             , nextVar :: !Int
                             }

instance Backend BitBlaster where
  putClause c = tell [Clause c]
  compileTok (BLString s) = tell [ShowString s]
  compileTok (BitShow fmt z) = tell.(:[]).ShowBits fmt =<< bitList z
  freshVar = state varIdPlusPlus
  unindexBits (NetBits { bitValues = VarId id}) = do
    ht <- gets symbolTable
    liftIO $ Ht.delete ht id
  unindexBits (NetBits { bitValues = ConstMask _ }) = return ()
  reindexBits (NetBits { bitValues = VarId id }) l = do
    ht <- gets symbolTable
    liftIO $ Ht.insert ht id l
  bitList (NetBits { bitValues = VarId id }) = do 
    ht <- gets symbolTable
    liftM fromJust $ liftIO $ Ht.lookup ht id
  bitList (NetBits {bitValues = ConstMask x, bitWidth = w})
    = return $ map tovar $ bitsOfInt w x
    where tovar True  = dmOneVar
          tovar False = dmZeroVar
  outputBits x = do xl <- bitList x
                    tell [ShowBits UIntFormat xl,ShowString "\n"]

dimacsList :: DmMonad () -> (DimacsInstr -> IO()) -> IO()
dimacsList m itemWriter = do
  ht <- Ht.new (==) Ht.hashInt
  itemWriter $ Clause [1]
  runStateT (runWriterT $ compileStep coughup m) (BlastState ht 2)
  return ()
  where
  coughup bb = censor (const[]) $ do di <- liftM snd $ listen bb
                                     forM_ di $ liftIO.itemWriter
                                     return ()

{-
-- returns variable count in circuit
dimacsList :: DmMonad a -> IO (Int,[DimacsInstr])
dimacsList ckt = do 
  ht <- Ht.new (==) Ht.hashInt
  (cl,endState) <- runStateT (execWriterT ckt) (init ht)
  return (nextVar endState-1, Clause [1]:cl)
  where init ht = DmState {symbolTable=ht, nextVar=2, nextNetBits=1}
        -}

liftNet :: NetWriter a -> DmMonad a
liftNet m = do ((a,endId),l) <- gets $ netList addend . nextNetBits
               tell [NetWrap l]
               modify $ \dmstate -> dmstate { nextNetBits = endId }
               return a
  where addend = do r <- m
                    end <- nextBitId
                    return (r,end)

-- A complete hack! A somewhat more memory-efficient version of liftNet
-- that works only for BitBunch results (great for NetBool)
liftBunch :: BitBunch a => NetWriter a -> DmMonad a
liftBunch m = do ((bz,b,endId),l) <- gets $ netList addend . nextNetBits
                 tell [NetWrap $ addDeallocs [bz] l]
                 modify $ \dmstate -> dmstate { nextNetBits = endId }
                 return b
  where addend = do r <- m
                    end <- nextBitId
                    rz <- bitify r
                    return (rz,r,end)

netIdPlusPlus s = nxt `seq` (id,s{nextNetBits=nxt}) where id = nextNetBits s
                                                          nxt = id+1
varIdPlusPlus s = nxt `seq` (id,s{nextVar=nxt}) where id = nextVar s
                                                      nxt = id+1

freshBits w = do id <- state netIdPlusPlus
                 let z = conjureBits w id
                 tell [FreshBits z]
                 return z

freshInt :: NetInt a => Int -> DmMonad a
freshInt = liftM intFromBits . freshBits

freshBool = freshBits 1 >>= liftNet . lsb

bitsOfInt 0 0 = []
bitsOfInt 0 _ = error "width parameter too small"
bitsOfInt w x = map (\i -> testBit x i) [0..w-1]

dmZeroVar = -1
dmOneVar = 1

--putClause = tell.(:[]).Clause

dmBitNot :: Backend be => Int -> be Int
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
dmAndList [] = return 1
dmAndList [x] = return x
dmAndList x = do z <- freshVar
                 putClause $ z:map negate x
                 mapM_ (putClause.(:[-z])) x
                 return z
dmOrList [] = return (-1)
dmOrList [x] = return x
dmOrList x = do z <- freshVar
                putClause $ -z:x
                mapM_ (putClause.(:[z]).negate) x
                return z
dmXorList [] = return dmZeroVar
dmXorList [x] = return x
dmXorList (x:xs) = dmBitXor x =<< dmXorList xs
  
dmAssert :: BitBunch a => a -> DmMonad ()
dmAssert b = tell.(:[]).AssertNZ <=< liftBunch $ bitify b

compileAssert :: Backend en => NetBits -> en ()
compileAssert z = putClause.(:[]) =<< dmOrList =<< bitList z

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

bitLevelShow (UIntTok ui) = liftNet $ liftM (BitShow UIntFormat) $ bitify ui
bitLevelShow (SIntTok si) = liftNet $ liftM (BitShow SIntFormat) $ bitify si
bitLevelShow (BoolTok  b) = liftNet $ liftM (BitShow BoolFormat) $ bitify  b
bitLevelShow (StringTok s) = return $ BLString s

-- Okay, so it accepts more than just strings, so what?
dmPutStrLn :: DmShow a => a -> DmMonad ()
dmPutStrLn a = tell.(:[]).ShowCmd =<< mapM bitLevelShow (a-|-"\n")

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

ripple2 :: Backend be => (Int -> Int -> Int -> be (Int,d)) 
        -> NetBits -> NetBits -> be (Int,[d])
ripple2 ripple2Unit x y = mapAccumM (uc ripple2Unit) dmZeroVar =<< pairList
  where
  uc f c (x,y) = f c x y
  pairList = liftM2 zip (bitList x) (bitList y)

isClause (Clause _) = True
isClause _ = False

burnSatQuery :: String -> DmMonad () -> IO ()
burnSatQuery caseName cktmaker
  = writeCaseFiles caseName $ \qfile tmplfile -> do
      hPutStrLn qfile $ "p cnf "++show varCount++" "++show clauseCount
      dimacsList cktmaker $ \bc -> case bc of
        Clause l -> hPutStrLn qfile $ unwords (map show l)++" 0"
        ShowString s -> hPutStr tmplfile s
        ShowBits fmt x -> hPutStr tmplfile $ showBits fmt x
  where
  showBits fmt x = tmplFmt fmt++"["++unwords (map show $ reverse x)++"]"
  (varCount,clauseCount) = runCounter cktmaker
  
compileNetInstr :: Backend be => NetInstr -> be ()
compileNetInstr (AssignResult res op) = reindexBits res =<< compileOp op
compileNetInstr (OutputBits x) = outputBits x
compileNetInstr (DeallocBits x) = unindexBits x

compileOp :: Backend be => Opcode -> be [Int]
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
