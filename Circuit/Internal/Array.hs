module Circuit.Internal.Array 
( Cast
, OpSpecs(..)
, applyOps
, applyOpsBase

, WriteSpecs(..), ReadSpecs(..)
, writeArray, readArray
) where

import Control.Monad
import Debug.Trace

import Circuit.Sorter (CmpSwap)
import qualified Circuit.Sorter as Sort
import Util

type CastWithIndex m a b = Int -> a -> m b
type Cast m a b = a -> m b

data OpSpecs m elt op mix c mix' result 
  = OpSpecs { castEltToMix    :: CastWithIndex m elt mix
            , castOpToMix     :: CastWithIndex m op  mix
            , cswpArrayIndex  :: CmpSwap m mix
            , foldInit        :: c
            , foldBody        :: c -> mix -> m (c,mix')
            , cswpSift        :: CmpSwap m mix'
            , castMixToElt    :: Cast m mix' elt
            , castMixToResult :: Cast m mix' result
            }

-- Obliviously applies operations to array elements
applyOpsBase opSpecs arr ops = do
  opmix  <- mapWithIndexM (castOpToMix  opSpecs) ops
  eltmix <- mapWithIndexM (castEltToMix opSpecs) arr
  mix    <- sortHalf (cswpArrayIndex opSpecs) 0 (length arr) (eltmix++opmix)
  (foldend,mix') <- mapAccumM (foldBody opSpecs) (foldInit opSpecs) mix
  sifted <- Sort.sort (cswpSift opSpecs) mix'
  let (eltmix',resmix') = splitAt (length arr) sifted
  arr <- mapM (castMixToElt opSpecs) eltmix'
  res <- mapM (castMixToResult opSpecs) resmix'
  return (arr,res,foldend)

-- TODO improve dividing strategies later
-- Operation on the same element will be performed in the order they are
--   provided. However, there are no guarantees about the order of operations
--   among different elements. I mean, that's why it's called a batch operation
applyOps opSpecs arr ops = do
  let opsBlockized = divideList (length ops `ceilDiv` length arr) ops
  ((foldend,arr),resBlockized) <- mapAccumM (\(acc,arr) block -> do
    (arr,result,acc) <- applyOpsBase opSpecs arr block
    return ((acc,arr),result)) (foldInit opSpecs,arr) opsBlockized
  return (arr,concat resBlockized,foldend)

-- Well, not exactly half --- you get to specify a range [a,b) which is assumed
-- to be already sorted. Note that the right endpoint of the range is exclusive
sortHalf cmpSwap a b l | (a>b)          = undefined
                       | len<=1         = return l
                       | a<=0 && b>=len = return l
                       | b<=0 || a>=len = Sort.sort cmpSwap l
                       | otherwise      = do  
                          left  <- sortHalf cmpSwap a b larg
                          right <- sortHalf cmpSwap (a-h) (b-h) rarg
                          Sort.merge cmpSwap left right
  where len = length l
        h = len `div` 2
        (larg,rarg) = splitAt h l

---------------------------------- writeArray --------------------------------

data WriteSpecs m elt addr serial maybePair 
  = WriteSpecs  { wsConstAddr   :: Int -> m addr
                , wsConstSerial :: Int -> m serial
                -- Swap on first comparing by addr, then by serial
                , wsArrayIndex :: CmpSwap m (addr,serial,elt)
                , wsNoPair    :: maybePair
                , wsFromMaybe :: maybePair -> m (addr,elt)
                , wsToMaybe   :: (addr,elt) -> m maybePair
                , wsIfEq  :: addr -> addr -> maybePair -> maybePair 
                          -> m maybePair
                -- Swap such that wsNoPair comes last, and compare addr in rest
                , wsSift :: CmpSwap m maybePair
                }

writeArray :: Monad m => WriteSpecs m elt addr serial maybePair
                      -> [elt] -> [(addr,elt)] -> m [elt]
writeArray _ [] _ = return []
writeArray ws arr cmd
  = do  (arr',_,Just(_,last)) <- applyOps opSpecs arr cmd 
        return $ init arr'++[last]
  where
  opSpecs = OpSpecs { castEltToMix    = attachAddress
                    , castOpToMix     = attachSerial
                    , cswpArrayIndex  = wsArrayIndex ws
                    , foldInit        = Nothing
                    , foldBody        = fb
                    , cswpSift        = wsSift ws
                    , castMixToElt    = wsFromMaybe ws >=> return.snd
                    , castMixToResult = return
                    }
  attachAddress a v = do  ax <- wsConstAddr ws a
                          sx <- wsConstSerial ws 0
                          return (ax, sx, v)
  attachSerial i (a,v) = do ax <- wsConstSerial ws (i+1)
                            return (a, ax, v)
  fb Nothing (addr,_,elt)             = return (Just (addr,elt), wsNoPair ws)
  fb (Just (paddr,pelt)) (addr,_,elt) = do
    box <- wsToMaybe ws (paddr,pelt)
    out <- wsIfEq ws paddr addr (wsNoPair ws) box
    return (Just (addr,elt), out) 


---------------------------------- readArray ---------------------------------

data ReadSpecs m elt addr serial serialOrValue maybePair 
  = ReadSpecs { rsMixFromValue :: elt -> m serialOrValue
              , rsMixFromSerial:: Int -> m serialOrValue
              , rsMixToValue :: serialOrValue -> m elt
              , rsIfMixIsValue :: serialOrValue 
                  -> (elt    -> m (elt,maybePair))
                  -> (serial -> m (elt,maybePair))
                  -> m (elt,maybePair)
              , rsConstAddr   :: Int -> m addr
              , rsConstSerial :: Int -> m serial
              , rsArrayIndex :: CmpSwap m (addr,serialOrValue)
              , rsSift :: CmpSwap m maybePair
              , rsFromMaybe :: maybePair -> m (serial,elt)
              , rsToMaybe :: (serial,elt) -> m maybePair
              , rsNoPair :: maybePair
              }

readArray :: Monad m  => ReadSpecs m elt addr serial serialOrValue maybePair
                      -> [elt] -> [addr] -> m [elt]
readArray _ [] _ = undefined
readArray rs arr cmd = do (_,res,_) <- applyOps opSpecs arr cmd; return res
  where
  opSpecs = OpSpecs { castEltToMix = attachAddress
                    , castOpToMix = attachSerial
                    , cswpArrayIndex = rsArrayIndex rs
                    , foldInit = Nothing
                    , foldBody = fb
                    , cswpSift = rsSift rs
                    , castMixToElt = rsFromMaybe rs >=> return.snd -- dead code
                    , castMixToResult = rsFromMaybe rs >=> return.snd
                    }
  attachAddress a v = do  ax <- rsConstAddr rs a
                          vx <- rsMixFromValue rs v
                          return (ax,vx)
  attachSerial i a = rsMixFromSerial rs i >>= return.((,)a)
  fb Nothing (a,mix) = do v<-rsMixToValue rs mix; return (Just v,rsNoPair rs)
  fb (Just v) (a,mix) = do
    (v,out) <- rsIfMixIsValue rs mix changeValue emitValue
    return (Just v,out)
    where
      changeValue v' = return (v',rsNoPair rs)
      emitValue s    = do p <- rsToMaybe rs (s,v); return (v,p)
