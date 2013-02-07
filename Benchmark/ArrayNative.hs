import Control.Monad
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
  batchOps badReadTest  readTest  "Read"  initMaker randomList
  batchOps badWriteTest writeTest "Write" initMaker randomWriteCmds
  batchOps badAddTest   addTest   "Add"   initMaker randomWriteCmds

main = countData
