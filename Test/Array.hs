module Test.Array where

import Control.Monad.Identity
import Control.Monad.State.Strict
import Data.Array
import Data.List as L
import Debug.Trace
import System.IO
import System.Random

import qualified Circuit.Interpreted.Array as IA
import qualified Circuit.Gcil.Array as GA
import Circuit.Gcil.Compiler
import Util

intWidth = 16     -- 16-bit integers

writeManual a l = elems (arr // l) where
  arr = listArray (0,length a-1) a

constFix v = constArg (valueSize v) v
pairName (g1,g2) = (gblName g1,gblName g2)

testWriteGarbled :: String -> [Int] -> [(Int,Int)] -> IO ()
testWriteGarbled testName arr delta = do 
  (arrElts,avpairs) <- withFile ("gcilouts/"++testName++".cir") WriteMode 
                                (evalStateT ckt . initState)
  writeFile ("gcilouts/"++testName++"-server.in") $ initArray arrElts arr
  writeFile ("gcilouts/"++testName++"-client.in") $ cmdPairs avpairs delta
  where
  n = length arr
  deltaN = length delta
  manual = writeManual arr delta
  initArray names arr = L.concat $ intersperse "\n" 
                      $ map vline $ zip names arr
    where vline (n,v) = n++" "++show v
  cmdPairs avpairs delta = L.concat $ intersperse "\n" 
                                    $ map twoline $ zip avpairs delta
    where twoline ((anm,vnm),(a,v)) = 
            anm++" "++show a++"\n"++vnm++" "++show v

  --((arrElts,avpairs),cktS) = runWriter $ evalStateT ckt initState
  ckt = do
    arrPh <- GA.inputArray intWidth 2 n 
    cmdPh <- forM [1..deltaN] (\_ -> do a <- newInput (indexSize n) 1
                                        v <- newInput intWidth 1
                                        return (a,v))
    arr'  <- GA.writeArray arrPh cmdPh
    manPh <- forM manual (return . constArg intWidth)
    match <- GA.ifEqualElse arr' (GA.listArray intWidth manPh) bitOne bitZero
    newOutput $ bitToInt match
    return (map gblName $ GA.elems arrPh, map pairName cmdPh)


testReadGarbled :: String -> [Int] -> [Int] -> IO ()
testReadGarbled testName arr addr = do
  (arrEltNames,addrNames) <- withFile ("gcilouts/"++testName++".cir") WriteMode
                              (evalStateT ckt . initState)
  writeFile ("gcilouts/"++testName++"-server.in") $ initArray arrEltNames arr
  writeFile ("gcilouts/"++testName++"-client.in") $ initArray addrNames addr
  where
  n = length arr
  manual = map (arr!!) addr
  addrN = length addr
  -- TODO get a better name for this initArray
  initArray names arr = L.concat $ intersperse "\n" 
                      $ map vline $ zip names arr
    where vline (n,v) = n++" "++show v
  ckt = do
    arrPh <- GA.inputArray intWidth 2 n
    addrPh <- forM [1..addrN] (\_ -> newInput (indexSize n) 1)
    res <- GA.readArray arrPh addrPh
    manPh <- forM manual (return . constArg intWidth)
    match <- GA.ifEqualElse (GA.listArray intWidth res)
                            (GA.listArray intWidth manPh) bitOne bitZero
    newOutput $ bitToInt match
    return (map gblName $ GA.elems arrPh, map gblName addrPh)

testWriteIntpret arr delta = me == manual where
  me = runIdentity $ IA.writeArray arr delta
  manual = writeManual arr delta

testReadIntpret arr ind = me == manual where
  me = runIdentity $ IA.readArray arr ind
  manual = map (arr!!) ind

smallList = [5,3,8,7,2,6,0,2,4,6]
writeCmd  = [(0,2),(5,4),(4,2),(5,10),(8,2),(6,5),(3,1),(7,3)]
readAddrs = [4,2,7,5,2,3]

randomList _ 0 rgen = ([],rgen)
randomList ulim n rgen = (aux n rgen1, rgen2) where
  (rgen1,rgen2) = System.Random.split rgen
  aux 0 _ = []
  aux n rg = x : aux (n-1) rg' where (x,rg') = randomR (0,ulim-1) rg

testLargeWrite n m = do
  init <- getStdRandom (randomList (2^intWidth) n)
  inds <- getStdRandom (randomList n m)
  newVals <- getStdRandom (randomList (2^intWidth) n)
  testWriteGarbled "largewrite" init $ zip inds newVals

testLargeRead n m = do
  init <- getStdRandom (randomList (2^intWidth) n)
  inds <- getStdRandom (randomList n m)
  testReadGarbled "largeread" init inds

runTests = do putStrLn $ show (testWriteIntpret smallList writeCmd)
                        ++ "   Test.Array.testWriteIntpret"
              putStrLn $ show (testReadIntpret smallList readAddrs)
                        ++ "   Test.Array.testReadIntpret"
              testWriteGarbled "smallwrite" smallList writeCmd
              testReadGarbled "smallread" smallList readAddrs
              testLargeWrite 50 50 
              testLargeRead 50 50 
