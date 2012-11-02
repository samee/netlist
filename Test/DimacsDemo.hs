module Test.DimacsDemo where

import Control.Monad
import Control.Monad.State

import Circuit.Arrays
import Circuit.NetList
import Circuit.NetList.Dimacs

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
    err = err || (arr[i]>=VMAX+1);
    tempFreqs[arr[i]]++;
    i++;
  }
i=0;
unroll VMAX+1 times: 
  c = (tempFreqs[i]>0);
  err = err || (length values>=VMAX) || (length freqs>=VMAX)
  condPush(c,values,i);
  condPush(c,freqs,tempFreqs[i]);
  i++;

assert(err);
-}

nonZeroFreqs vmax nmax = do
  arr       <- replicateM nmax $ freshInt vwidth
  n         <- freshInt fwidth
  tempFreqs <- replicateM vmax $ freshInt fwidth
  dmAssert =<< liftBunch $ do
    -- Assuming that i can be known at compile time for simple cases like these
    (c,ac,err,wlist) <- foldM (\(c,ac,err,wlist) i -> do
      c <- netAnd c =<< greaterThan n (constInt i)
      bound <- greaterThan (constInt (vmax+1)) (arr!!i) -- arr[i]<=VMAX
      err <- netOr err =<< netAnd c =<< netNot bound
      ci  <- liftM intFromBits $ bitify c
      ac  <- netAnd ac =<< netOr bound =<< netNot c
      return (c,ac,err,(arr!!i,ci):wlist)
      ) (0, netTrue, netFalse, []) [0..nmax-1]
    tempFreqs <- writeArray tempFreqs wlist             -- commit writes
    (err,_,_) <- foldM (\(err,freqs,values) i -> do
      vl <- Stk.length values
      fl <- Stk.length freqs
      err <- netOr err =<< greaterThan vl $ constInt $ vmax-1
      err <- netOr err =<< greaterThan fl $ constInt $ vmax-1
      c <- greaterThan (tempFreqs!!i) 0
      values <- Stk.condPush c (constInt i) values
      freqs  <- Stk.condPush c (tempFreqs!!i) freqs
      return (err,freqs,values)) (err,Stk.empty,Stk.empty) [0..vmax-1]
    netAnd ac err
