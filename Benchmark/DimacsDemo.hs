module Benchmark.DimacsDemo where

import Control.Monad
import Control.Monad.State
import Debug.Trace

import Circuit.Array
import Circuit.NetList
import Circuit.NetList.Dimacs
import Circuit.Stack as Stk
import Util

{-
Consider the following C program fragment:
#define VMAX 500

unsigned values[VMAX], freqs[VMAX], valueCount;

int nonZeroFreqs(int arr[],int n)
{
  unsigned tempFreqs[VMAX+1] = {}; /* init to zero */
  unsigned i,j;

  for(i=0;i<n;++i) if(arr[i]>VMAX) return -1; else tempFreqs[arr[i]]++;
  for(i=0;i<=VMAX;++i) if(tempFreqs[i]>0)
  { values[j]=i;
    freqs[j]=tempFreqs[i];
    ++j;
  }
  valueCount=j;
  return 0;
}

We will automatically attempt to find an input to this code that makes it fail

i=0; c=1; err=0;
unroll NMAX times: 
  c = (c && i<n);
  if(c)
  { assert(arr[i]<=VMAX);
    resizeToValue(arr[i],VMAX);
    err = err || (arr[i]>=VMAX+1);
    tempFreqs[arr[i]]++;
    i++;
  }
assert(n<=NMAX);
i=0;
unroll VMAX+1 times: 
  err = err || (length values>=VMAX) || (length freqs>=VMAX)
  c = (tempFreqs[i]>0);
  condPush(c,values,i);
  condPush(c,freqs,tempFreqs[i]);
  i++;

assert(err);
-}

uintEmpty = Stk.empty :: Stack NetUInt

listEqual a b | Prelude.length a/=Prelude.length b = undefined
              | otherwise = netAnds =<< mapM (uncurry equal) (zip a b)

nonZeroFreqs vmax nmax = do
  arr       <- replicateM nmax $ freshInt vwidth :: DmMonad [NetUInt]
  n         <- freshInt fwidth                   :: DmMonad NetUInt
  tempFreqs <- return $ replicate (vmax+1) 
             $ constIntW fwidth 0 :: DmMonad [NetUInt]
  dmPutStrLn arr
  dmPutStrLn n
  dmAssert <=< liftBunch $ do
    -- Assuming that i can be known at compile time for simple cases like these
    (c,ac,err,wlist) <- foldM (\(c,ac,err,wlist) i -> do
      c <- netAnd c =<< greaterThan n (constInt i)
      bound <- greaterThan (constInt (vmax+1)) (arr!!i) -- arr[i]<=VMAX
      err <- netOr err =<< netAnd c =<< netNot bound
      ci  <- liftM intFromBits $ bitify c
      ac  <- netAnd ac =<< netOr bound =<< netNot c
      return (c,ac,err,(arr!!i,ci):wlist)
      ) (netTrue, netTrue, netFalse, []) [0..nmax-1]
    -- commit writes
    tempFreqs <- liftM elems $ addToArray (listArray tempFreqs) wlist
    ac <- netAnd ac =<< greaterThan (constInt $ nmax+1) n
    (err,_,_) <- foldM (\(err,freqs,values) (i,tf) -> do
      vl <- Stk.length values
      fl <- Stk.length freqs
      c <- greaterThan tf (constInt 0)
      err <- netOr err <=< netAnd c <=< greaterThan vl $ constInt $ vmax-1
      err <- netOr err <=< netAnd c <=< greaterThan fl $ constInt $ vmax-1
      values <- Stk.condPush c (constInt i) values
      freqs  <- Stk.condPush c tf freqs
      return (err,freqs,values)) (err,Stk.empty,uintEmpty) (zip [0..] tempFreqs)
    netAnd ac err
  where vwidth = valueSize vmax
        fwidth = valueSize nmax

deep n = do
  x <- freshInt 8 :: DmMonad NetUInt
  dmAssert <=< liftNet$bind2 netOr (equal x $ constInt 0) (equal x $ constInt 1)
  dmAssert <=< liftBunch $ equal (constInt 0) 
           =<< foldM (\x _ -> sub (constInt 1) x) x [1..n]

runTests = burnSatQuery "offByOne" $ nonZeroFreqs 500 501
           -- burnSatQuery "deep" <=< dimacsList $ deep 10000
