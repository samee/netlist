module Test.Array where

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

writeTest :: [Int] -> [(Int,Int)] -> GcilMonad ()
writeTest init cmds = do
  initV <- liftM CA.listArray $ forM init $ testInt ServerSide intW
  cmdV  <- forM cmds $ \(a,v) -> do a <- testInt ClientSide addrLen a
                                    v <- testInt ClientSide intW v
                                    return (a,v)
  arr <- liftNet $ liftM CA.elems $ writeBatch initV cmdV
  arr'<- return $ map constInt (writeManual init cmds)
  ignoreAndsUsed $ liftNet $ 
    newOutput =<< bitify =<< netAnds =<< forM (zip arr arr') (uncurry equal)
  where
  addrLen = indexSize (length init)
  writeBatch :: CA.NetArray NetUInt -> [(NetUInt,NetUInt)] 
             -> NetWriter(CA.NetArray NetUInt)
  writeBatch = CA.writeArray

readTest init addrs = do
  initV <- liftM CA.listArray $ forM init $ testInt ServerSide intW
  addrV <- forM addrs $ testInt ClientSide addrLen
  arr <- liftNet $ readBatch initV addrV
  arr'<- return $ map (constInt.(natarr!)) addrs
  ignoreAndsUsed $ liftNet $ 
    newOutput =<< bitify =<< netAnds =<< forM (zip arr arr') (uncurry equal)
  where
  natarr = listArray (0,length init-1) init
  addrLen = indexSize (length init)
  readBatch :: CA.NetArray NetUInt -> [NetUInt] 
            -> NetWriter [NetUInt]
  readBatch = CA.readArray

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

runTests = do burnTestCase "smallwrite" $gcilList$ writeTest smallList writeCmd
              burnTestCase "smallread" $gcilList$ readTest  smallList readAddrs
              let n=500; cmdn=500
              largeList <- getStdRandom $ randomList (2^intW) n
              writeCmdLots <- getStdRandom $ randomWriteCmds n cmdn
              readAddrsLots <- getStdRandom $ randomList n cmdn
              burnTestCase "largewrite" $gcilList
                $ writeTest largeList writeCmdLots
              burnTestCase "largeread" $gcilList
                $ readTest  largeList readAddrsLots
