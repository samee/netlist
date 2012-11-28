module Test.StackDimacs where

import Control.Monad

import Circuit.NetList
import Circuit.NetList.Dimacs
import qualified Circuit.Stack as CS
import Util

intW = 16
sumW = 16

sumToZeroFast l = liftM fst $ foldM (\(s,done) v -> do
  done <- netOr done =<< equal (constInt 0) v
  s <- add s =<< mux done v (constInt 0)
  return (s,done)) ((constIntW sumW 0),netFalse) l

sumToZero l = liftM fst $ foldM (\(s,stk) _ -> do
                            mbtop <- CS.top stk
                            if knownNothing mbtop 
                               then return (s,stk)
                               else do
                                 let t = netFromJust mbtop 
                                 c <- netNot =<< equal (constInt 0) t
                                 s <- add s t
                                 stk <- CS.condPop c stk
                                 return (s,stk)
                            ) (constIntW sumW 0, CS.fromList l) [1..n]
  where n = length l

sumToZeroSlow l = liftM fst $ foldM (\(s,done) i -> do
  v <- muxList (constIntW (indexSize n) i) l
  done <- netOr done =<< equal (constInt 0) v
  s <- add s =<< mux done v (constInt 0)
  return (s,done)) ((constIntW sumW 0),netFalse) [0..n-1]
  where n = length l

sumAll [] = return (constIntW sumW 0)
sumAll (x:xs) = do s <- sumAll xs
                   add s x

localSumToZero = sum . takeWhile (/=0)

dmWords l = foldr (\x acc -> x-|-" "-|-acc) (dmShow "") l

sumSolve summer prefLo prefHi fullLo n = do
  inputs <- replicateM n (freshInt intW)
  forM_ inputs $ \x -> dmAssert <=< liftNet $ greaterThan (constInt $ n+1) x
  dmPutStrLn $ dmWords inputs
  dmAssert <=< liftBunch $ do
    prefixSum <- summer (inputs :: [NetUInt])
    fullSum <- sumAll inputs
    c1 <- netNot =<< greaterThan (constInt prefLo) prefixSum
    c2 <- netNot =<< greaterThan prefixSum (constInt prefHi)
    c3 <- netNot =<< greaterThan (constInt fullLo) fullSum
    netAnds [c1,c2,c3]

{-
  Target function:

  #define MAXSIZE 100
  int arr1[MAXSIZE], arr2[MAXSIZE], destarr[MAXSIZE*2];

  int merge(int halfsize)
  {
    int i,j,k;
    if(halfsize>MAX) return -1;
    for(i=1;i<halfsize;++i) if(arr1[i-1]>arr1[i]) return -1;
    for(j=1;j<halfsize;++j) if(arr2[j-1]>arr2[j]) return -1;
    i=j=0;
    for(k=0;k<2*halfsize;++k)
    { if(arr1[i]<arr2[j]) destarr[k]=arr1[i++];
      else destarr[k]=arr2[j++];
    } 
    return 0;
  }

  Symex version:
  int merge(int halfsize)
  {
    int i,j,k;
    int error = 0;
    assert(halfsize<=MAXSIZE);
    for(i=1;i<MAXSIZE;++i) if(i<halfsize) assert(arr1[i-1]<=arr1[i]);
    for(j=1;j<MAXSIZE;++j) if(j<halfsize) assert(arr2[j-1]<=arr2[j]);
    i=j=0;
    stk1=initStack(arr1);
    stk2=initStack(arr2);
    for(k=0;k<2*MAXSIZE;++k) if(k<2*halfsize)
    { 
      error = (error || i>=MAXSIZE);
      error = (error || j>=MAXSIZE);
      if(stk1.top()<stk2.top()) { destarr[k]=stk1.pop(); i++; }
      else { destarr[k]=stk2.pop(); j++; }
    }
    assert(error);
  }
-}

data StackSpec s a = StackSpec { fromList :: [a] -> s
                               , cpop :: NetBool -> s -> NetWriter s
                               , top :: s -> NetWriter (NetMaybe a)
                               }

data SimpleStack a = SimpleStack { ssContent :: [a]
                                 , ssIndex :: NetUInt
                                 }

simpleStack :: Swappable a => StackSpec (SimpleStack a) a
simpleStack = StackSpec { fromList = ssNew
                        , cpop = ssPop
                        , top = ssTop
                        }
ssNew l = SimpleStack { ssContent=l, ssIndex=constIntW (indexSize $ length l) 0 }
ssPop c s = do ni <- condAdd c (ssIndex s) (constInt 1)
               return $ s { ssIndex = ni }
ssTop s = liftM netJust $ muxList (ssIndex s) (ssContent s)

hierStack :: Swappable a => StackSpec (CS.Stack a) a
hierStack = StackSpec { fromList = CS.fromList
                      , cpop = CS.condPop
                      , top = CS.top
                      }

mergeTest stackspec maxsize = do
  halfsize <- freshInt counterW :: DmMonad NetUInt
  arr1 <- replicateM maxsize freshByte
  arr2 <- replicateM maxsize freshByte
  dmPutStrLn halfsize
  dmPutStrLn $ dmWords arr1
  dmPutStrLn $ dmWords arr2
  destArr <- replicateM (2*maxsize) freshByte
  dmPutStrLn $ dmWords destArr
  dmAssert <=< liftBunch $ do
    ac <- greaterThan (constInt $ maxsize+1) halfsize
    ac <- netAnd ac <=< netAnds <=< forM [1..maxsize-1] $ \i -> do
        bind2 netOr (greaterThan (constInt $ i+1) halfsize)
                    (chainGreaterThan netTrue (arr1!!i) (arr1!!(i-1)))
    ac <- netAnd ac <=< netAnds <=< forM [1..maxsize-1] $ \j ->
        bind2 netOr (greaterThan (constInt $ j+1) halfsize)
                    (chainGreaterThan netTrue (arr2!!j) (arr2!!(j-1)))
    fullsize <- shiftLeft 1 halfsize
    (ac,err,_,_,_,_) <- foldM (\(ac,err,i,j,stk1,stk2) k -> do
      en  <- greaterThan fullsize (constInt k)
      err <- netOr err =<< netAnd en =<< greaterThan i (constInt $ maxsize-1)
      err <- netOr err =<< netAnd en =<< greaterThan j (constInt $ maxsize-1)
      tp1 <- liftM netFromJust $ top stackspec stk1
      tp2 <- liftM netFromJust $ top stackspec stk2
      c <- greaterThan tp2 tp1
      c'<- netNot c
      ac <- netAnd ac =<< equal (destArr!!k) =<< mux c tp2 tp1
      stk1 <- cpop stackspec c  stk1
      stk2 <- cpop stackspec c' stk2
      i <- condAdd c  i (constInt 1)
      j <- condAdd c' j (constInt 1)
      return (ac,err,i,j,stk1,stk2)
      ) (ac,netFalse,constZ,constZ,fromList stackspec arr1,fromList stackspec arr2) 
      [0..2*maxsize-1]
    netAnd ac err
  where
  constZ = constIntW counterW 0 :: NetUInt
  freshByte = freshInt 8 :: DmMonad NetUInt
  counterW = 16

mergeTestBatch = forM_ [20,40,60,80,100,200] $ \size -> do
  burnSatQuery ("mergeHierTest"++show size) $ mergeTest hierStack size
  burnSatQuery ("mergeSimpTest"++show size) $ mergeTest simpleStack size

runTests = do --burnSatQuery "sumSolve" $ sumSolve sumToZero 1000 1000 5000 200
              -- burnSatQuery "mergeTest" $ mergeTest simpleStack 30
              mergeTestBatch
