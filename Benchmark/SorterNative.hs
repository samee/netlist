import Control.Monad
import System.Random as R
import System.IO

import Circuit.Sorter

-- The Control.Monad.State.Strict design seemed pretty horrible, so I rolled my
-- own

newtype IntState a = IntState { runIntState :: Int -> (a,Int) }

instance Monad IntState where
  return a = IntState $ \s -> (a,s)
  st >>= f = IntState $ \s -> let (a,s') = runIntState st s in 
                                  s' `seq` runIntState (f a) s'

modify f = IntState $ \x -> ((),f x)

-- Simply counts the number of compare-swaps done in a sorting network
countCompare sorter n = snd $ runIntState (sorter inc dummy) 0 where
  inc () () = modify (+1) >> return ((),())
  dummy = replicate n ()

sampleN = [a*b | b<-[10,100,1000,10000], a<-[1..9]]

pad w s | len >= w = s
        | otherwise = s++replicate (w-len) ' '
        where len = length s

genRShellSort rgen = (shellSort rgen1,rgen2) where (rgen1,rgen2) = R.split rgen

main = do
  hSetBuffering stdout LineBuffering
  rshell <- getStdRandom genRShellSort
  putStrLn "n batcher rshell"
  forM sampleN $ \n -> do
    putStrLn $ pad 6 (show n) ++ show (countCompare batcherSort n)
                      ++"\t"  ++ show (countCompare rshell n)

