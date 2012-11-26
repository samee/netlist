-- TODO separate this into regression and benchmark test
module Test.StackGcil where

import Control.Monad
import Control.Monad.State
import System.Random

import Circuit.NetList as N
import Circuit.NetList.Gcil as NG
import qualified Circuit.Stack as S
import Util
--import Test.Gcil

itemWidth = 16
-- expn = 100
-- maxn = 2*expn

data StackTestAction =  StackPush Int -- value to be pushed
                      | StackPop Int  -- expected value
                      deriving Show

randomTest :: RandomGen g => Int -> Int -> g -> ((Int,[StackTestAction]),g)
randomTest opcount expn rgen = ((maxn,acts),rgen') where
  (acts,rgen') =  aux opcount 0 [] rgen
  aux 0 _ _ rgen = ([],rgen)
  aux opcount len stk rgen = flip runState rgen $ do
    rlen <- state $ randomR (0,maxn)
    let opc =  Prelude.min opcount $ abs $ len-rlen
    if opc == 0 then state $ aux opcount len stk
    else if len < rlen then do
      newvals <- replicateM opc $ state $ randomR vrange
      ops <- state $ aux (opcount-opc) (len+opc) (reverse newvals ++ stk)
      return $ map StackPush newvals ++ ops
    else do
      let (exp,stk') = splitAt opc stk
      ops <- state $ aux (opcount-opc) (len-opc) stk'
      return $ map StackPop exp ++ ops

  vrange = (0,2^itemWidth-1)
  maxn = 2*expn
  -- opcount = 20*expn

splitPushPop [] = ([],[])
splitPushPop (StackPush x:l) = (x:a,b) where (a,b) = splitPushPop l
splitPushPop (StackPop  x:l) = (a,x:b) where (a,b) = splitPushPop l

gcRandomTest (maxn,acts) = do
  pushVars <- mapM (testInt ServerSide itemWidth) pushVals
  popVars  <- mapM (testInt ClientSide itemWidth) popVals
  cktMain pushVars popVars acts netTrue (S.capLength maxn S.empty)
  where
  (pushVals, popVals) = splitPushPop acts

  cktMain :: [NetUInt] -> [NetUInt] -> [StackTestAction] 
          -> NetBool -> S.Stack NetUInt -> GcilMonad ()
  cktMain [] [] [] c stk = gcilOutBits c
  cktMain (var:push) pop (StackPush _:acts) c stk = do
    stk <- liftNet $ S.condPush N.netTrue var stk
    cktMain push pop acts c stk
  cktMain push (exp:pop) (StackPop _:acts) c stk = do
    mb  <- liftNet $ S.top stk
    stk <- liftNet $ S.condPop N.netTrue stk
    c   <- ignoreAndsUsed $ liftNet $ do
              valid <- netNot =<< netIsNothing mb
              eq    <- equal (netFromJust mb) exp
              netAnds [c,valid,eq]
    cktMain push pop acts c stk


-- Testing the test generator
testRandomTest acts = aux [] acts where
  aux stk [] = True
  aux [] (StackPop _:_) = False
  aux (t:stk) (StackPop exp:acts) = (t==exp) && aux stk acts
  aux stk (StackPush x:acts) = aux (x:stk) acts


data SimpleStack a = SimpleStack { ssContent :: [a]
                                 , ssTopPtr :: NetUInt
                                 , ssMaxLen :: Int
                                 }

ssEmpty maxl = SimpleStack { ssContent = []
                           , ssTopPtr = constIntW (indexSize maxl) 0
                           , ssMaxLen = maxl
                           }
ssPush c v stk = do
  let oldlen = length (ssContent stk)
      (newlen,oldbuff) = if ssMaxLen stk == oldlen
                           then (oldlen,ssContent stk)
                           else (oldlen+1,ssContent stk++[v])
  dec <- decoderREn c 0 newlen (ssTopPtr stk)
  newbuff <- forM (zip dec $ oldbuff) $ \(d,old) -> mux d old v
  top <- condAdd c (ssTopPtr stk) (constInt 1)
  return $ stk { ssContent = newbuff, ssTopPtr = top }

ssPop c stk = do
  top <- condSub c (ssTopPtr stk) (constInt 1)
  return $ stk { ssTopPtr = top }

ssTop stk = muxList (ssTopPtr stk) (ssContent stk)

stackCount maxn acts = countGates $ gcilList $ gcRandomTest (maxn,acts)
naiveCount maxn acts = countGates $ gcilList $ do
  pushVars <- mapM (testInt ServerSide itemWidth) pushVals
  popVars  <- mapM (testInt ClientSide itemWidth) popVals
  cktMain pushVars popVars acts (ssEmpty maxn)
  where
  (pushVals, popVals) = splitPushPop acts

  cktMain :: [NetUInt] -> [NetUInt] -> [StackTestAction] -> SimpleStack NetUInt
          -> GcilMonad ()
  cktMain [] [] [] skt = return ()
  cktMain (var:push) pop (StackPush _:acts) stk = do
    stk <- liftNet $ ssPush N.netTrue var stk
    cktMain push pop acts stk
  cktMain push (var:pop) (StackPop _:acts) stk = do
    mb <- liftNet $ ssTop stk
    stk <- liftNet $ ssPop N.netTrue stk
    cktMain push pop acts stk


runTests :: IO ()
{-
runTests = do (maxn,acts) <- getStdRandom $ randomTest 2000 100
              burnTestCase "stacktest" $ gcilList $ gcRandomTest (maxn,acts)
              -}
runTests = do putStrLn "---------- Stack sizes ---------------"
              putStrLn "stackSize  opCount  Naive  MyStack"
              forM_ [8,16,32,64,128,256,512,1024] $ \expn ->
                forM_ [expn, expn*2, expn*4] $ \opcount -> do
                  (maxn,acts) <- getStdRandom $ randomTest opcount expn
                  putStrLn $ show maxn ++ "  " ++ show opcount ++ "  "
                          ++ show (naiveCount maxn acts) ++ "  " 
                          ++ show (stackCount maxn acts)


