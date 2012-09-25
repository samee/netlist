module Test.StackCircuits where

import Control.Monad
import Control.Monad.State
import System.Random

import Circuit.Gcil.Compiler as Gc
import Circuit.Gcil.Stack as Gs
import Test.Gcil

intWidth = 8
expn = 100
maxn = 2*expn

data StackTestAction =  StackPush Int -- value to be pushed
                      | StackPop Int  -- expected value
                      deriving Show

randomTest :: RandomGen g => g -> ([StackTestAction],g)
randomTest rgen = aux opcount 0 [] rgen where
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

  vrange = (0,2^intWidth-1)
  opcount = 20*expn

-- XXX so batch arrays can actually use data interactively, we just cannot
--   use read out data to calculate addresses. But could we put data on stack
--   and pop it out as an address? We could, couldn't we?

splitPushPop [] = ([],[])
splitPushPop (StackPush x:l) = (x:a,b) where (a,b) = splitPushPop l
splitPushPop (StackPop  x:l) = (a,x:b) where (a,b) = splitPushPop l

burnRandomTest acts = writeTestCase "stacktest" ckt fst snd
  where 
  ckt = do
    pushVars <- replicateM pushC $ newInput intWidth 2
    popVars <- replicateM popC $ newInput intWidth 1
    cktMain pushVars popVars acts bitOne (Gs.capLength maxn Gs.empty)
    return (zip (map gblName pushVars) pushVals, 
            zip (map gblName  popVars) popVals)

  (pushVals, popVals) = splitPushPop acts
  pushC = length pushVals
  popC = length popVals

  cktMain :: [GblInt] -> [GblInt] -> [StackTestAction] 
          -> GblBool -> Stack GblInt -> GcilMonad ()
  cktMain [] [] [] c stk = newOutput (bitToInt c)
  cktMain (var:push) pop (StackPush _:acts) c stk = do
    stk <- Gs.condPush Gc.bitOne var stk
    cktMain push pop acts c stk
  cktMain push (exp:pop) (StackPop _:acts) c stk = do
    mb  <- Gs.top stk
    stk <- Gs.condPop Gc.bitOne stk
    c   <- ignoreAndsUsed $ do
              valid <- Gc.not =<< gblIsNothing mb
              eq    <- equalU (castFromJust mb) exp
              Gc.andList [c,valid,eq]
    cktMain push pop acts c stk


-- Testing the test generator
testRandomTest acts = aux [] acts where
  aux stk [] = True
  aux [] (StackPop _:_) = False
  aux (t:stk) (StackPop exp:acts) = (t==exp) && aux stk acts
  aux stk (StackPush x:acts) = aux (x:stk) acts

runTests :: IO ()
runTests = do -- setStdGen $ mkStdGen 1
              acts <- getStdRandom randomTest
              burnRandomTest acts
