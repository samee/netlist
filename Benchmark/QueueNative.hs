-- Generates random push/pop on queue circuits and measures circuit size, both for
--   the queue here and the naive queue in Test.Util.Simple. Circuit size ignores
--   xor and not gates as usual
import Control.Monad

import Circuit.NetList.Gcil
import Circuit.Queue
import System.Random
import Test.Util.Simple  -- The two queues to be tested
import Test.QueueGcil    -- Generates random push/pop circuits

main     = do putStrLn "-------------- Queue sizes ------------------"
              putStrLn "n opcount Naive MyQueue"
              forM_ [16,32,64,128,256,512,1024,2048] $ \maxl ->
                forM_ [maxl `div` 2, maxl, maxl*2] $ \opcount -> do
                  acts <- getStdRandom $ randomTest opcount maxl
		  let nckt = compileActs (qEmpty :: SimpleQueue         a) maxl acts
		      mckt = compileActs (qEmpty :: Circuit.Queue.Queue a) maxl acts
                  putStrLn $ show maxl ++ "  " ++ show opcount ++ "  "
                          ++ show (snd $ countGates $ void nckt) ++ "  " 
                          ++ show (snd $ countGates $ void mckt)
