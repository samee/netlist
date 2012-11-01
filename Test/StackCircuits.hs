module Test.StackCircuits where

import Control.Monad
import Control.Monad.State
import System.Random

import Circuit.NetList as N
import Circuit.NetList.Gcil as NG
import qualified Circuit.Stack as S
--import Test.Gcil

itemWidth = 8
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

  vrange = (0,2^itemWidth-1)
  opcount = 20*expn

splitPushPop [] = ([],[])
splitPushPop (StackPush x:l) = (x:a,b) where (a,b) = splitPushPop l
splitPushPop (StackPop  x:l) = (a,x:b) where (a,b) = splitPushPop l

-- name == "stacktest" TODO runTests
gcRandomTest acts = do
  pushVars <- mapM (testInt ServerSide itemWidth) pushVals
  popVars  <- mapM (testInt ClientSide itemWidth) popVals
  cktMain pushVars popVars acts netTrue (S.capLength maxn S.empty)
  where
  (pushVals, popVals) = splitPushPop acts
  pushC = length pushVals
  popC = length popVals

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

runTests :: IO ()
runTests = do acts <- getStdRandom randomTest
              burnTestCase "stacktest" $ gcilList $ gcRandomTest acts
