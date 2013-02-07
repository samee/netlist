import Control.Monad
import System.IO
import System.Random

import Circuit.NetList.Gcil
import Test.ArrayGcil

sizeOptions = [50,100..1000]
batchOps badop goodop opname makelist makecmd = do
  putStrLn $ "------------- Batch "++opname++" Circuits ---------------"
  putStrLn "n  Naive  Batch"
  forM_ sizeOptions $ \n -> do
    let cmdn = n
    init <- getStdRandom $ makelist n
    cmd  <- getStdRandom $ makecmd n cmdn
    let badstat = countGates $ void $ badop init cmd
        goodstat = countGates $ void $ goodop init cmd
    putStrLn $ show n ++ "  "++show badstat++"  "++show goodstat

initMaker = randomList (2^intW)

countData = do 
  hSetBuffering stdout LineBuffering
  batchOps badReadTest  readTest  "Read"  initMaker randomList
  batchOps badWriteTest writeTest "Write" initMaker randomWriteCmds
  batchOps badAddTest   addTest   "Add"   initMaker randomWriteCmds
  trySizes badReadTest  readTest  "Read"  initMaker randomList
  trySizes badAddTest   addTest   "Add"   initMaker randomWriteCmds

trySizes badop goodop opname makelist makecmd = do
  putStrLn $ "------------- Size Range "++opname++" -------------------"
  forM_ nvalues $ \n -> do
    init <- getStdRandom $ makelist n
    cmd1 <- getStdRandom $ makecmd n 1
    putStrLn $ "sz = "++show n
    putStrLn $ "Naive cost = "++show (snd $ countGates $void$ badop init cmd1)
    putStrLn $ "Batch\tCost"
    forM_ (batchSizes n) $ \k -> do
      cmd <- getStdRandom $ makecmd n k
      putStrLn $ show k ++ "\t" ++ show (batchCost init cmd)
  where
  nvalues = [50,100,400]
  batchCost init cmd = (fromIntegral $ snd $ countGates $void$ goodop init cmd) 
                     / (fromIntegral $ length cmd)
  batchSizes n = [st1,st1+d1..en1]++[st2,st2+d2..en2]
    where st1 = n `div` 5; st2 = 2*n
          d1  = 2*st1    ; d2  = 2*st2
          en1 = 9*st1    ; en2 = 9*st2

main = countData
