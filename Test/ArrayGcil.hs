module Test.ArrayGcil where

import Control.Monad.Identity
import Control.Monad.State.Strict
import Data.Array
import Data.List as L
import Debug.Trace
import System.IO
import System.Random

import qualified Circuit.Array as CA
import Circuit.NetList
import Circuit.NetList.Gcil
import Util

intW = 16     -- 16-bit integers

writeManual a l = elems (arr // l) where
  arr = listArray (0,length a-1) a
writeTest = modifyTest CA.writeArray writeManual
badWriteTest = modifyTest CA.badWriteArray writeManual

addManual a l = elems $ accum (+) arr l where
  arr = listArray (0,length a-1) a
addTest = modifyTest CA.addToArray addManual
badAddTest = modifyTest CA.badAddToArray addManual

type Modify a = CA.NetArray a -> [(NetUInt,a)] -> NetWriter (CA.NetArray a)
type ManualModify a = [a] -> [(Int,a)] -> [a]

modifyTest :: Modify NetUInt -> ManualModify Int -> [Int] -> [(Int,Int)]
           -> GcilMonad NetBool
modifyTest modifyBatch modifyManual init cmds = do
  initV <- liftM CA.listArray $ forM init $ testInt ServerSide intW
  cmdV  <- forM cmds $ \(a,v) -> do a <- testInt ClientSide addrLen a
                                    v <- testInt ClientSide intW v
                                    return (a,v)
  arr <- liftNet $ liftM CA.elems $ modifyBatch initV cmdV
  arr'<- return $ map constInt (modifyManual init cmds)
  ignoreAndsUsed $ liftNet $ netAnds =<< forM (zip arr arr') (uncurry equal)
  where
  addrLen = indexSize (length init)

readBaseTest reader init addrs = do
  initV <- liftM CA.listArray $ forM init $ testInt ServerSide intW
  addrV <- forM addrs $ testInt ClientSide addrLen
  arr <- liftNet $ readBatch initV addrV
  arr'<- return $ map (constInt.(natarr!)) addrs
  ignoreAndsUsed $ liftNet $ netAnds =<< forM (zip arr arr') (uncurry equal)
  where
  natarr = listArray (0,length init-1) init
  addrLen = indexSize (length init)
  readBatch :: CA.NetArray NetUInt -> [NetUInt] 
            -> NetWriter [NetUInt]
  readBatch = reader

readTest = readBaseTest CA.readArray
badReadTest = readBaseTest CA.badReadArray

smallList = [5,3,8,7,2,6,0,2,4,6]
writeCmd  = [(0,2),(5,4),(4,2),(5,10),(8,2),(6,5),(3,1),(7,3)]
readAddrs = [0,9,4,2,7,5,2,3]

randomList _ 0 rgen = ([],rgen)
randomList ulim n rgen = (aux n rgen1, rgen2) where
  (rgen1,rgen2) = System.Random.split rgen
  aux 0 _ = []
  aux n rg = x : aux (n-1) rg' where (x,rg') = randomR (0,ulim-1) rg

randomWriteCmds n cmdn rgen = flip runState rgen $ do
  inds <- replicateM cmdn $ state $ randomR (0,n-1)
  vals <- replicateM cmdn $ state $ randomR (0,(2^intW)-1)
  return $ zip inds vals

sizeOptions = [50,100..1000]
batchOps badop goodop opname makelist makecmd = do
  putStrLn $ "------------- Batch "++opname++" Circuits ---------------"
  putStrLn "n  Naive  Batch"
  forM_ sizeOptions $ \n -> do
    let cmdn = n
    init <- getStdRandom $ makelist n
    cmd  <- getStdRandom $ makecmd n cmdn
    let badstat = countGates $ gcilList $ badop init cmd
        goodstat = countGates $ gcilList $ goodop init cmd
    putStrLn $ show n ++ "  "++show badstat++"  "++show goodstat


initMaker = randomList (2^intW)

countData = do 
  batchOps badReadTest  readTest  "Read"  initMaker randomList
  batchOps badWriteTest writeTest "Write" initMaker randomWriteCmds
  batchOps badAddTest   addTest   "Add"   initMaker randomWriteCmds


shortTests = do burnTestCase "smallwrite" $ writeTest smallList writeCmd
                burnTestCase "smallread"  $ readTest  smallList readAddrs
                burnTestCase "smalladd"   $ addTest smallList writeCmd


longTests = do largeList     <- getStdRandom $ randomList (2^intW) n
               writeCmdLots  <- getStdRandom $ randomWriteCmds n cmdn
               readAddrsLots <- getStdRandom $ randomList n cmdn
               burnTestCase "largewrite" $ writeTest largeList writeCmdLots
               burnTestCase "largeread"  $ readTest  largeList readAddrsLots
               -- FIXME
               burnTestCase "largeadd"   $ addTest largeList writeCmdLots
  where n    = 500
        cmdn = 500
