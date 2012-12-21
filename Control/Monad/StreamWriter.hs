-- A version of the Writer monad that is a bit more memory-friendly for
-- streaming use cases. Like the conventional Writer, but doesn't support
-- the listen method directly (although could be implemented in the inner 
-- monad). The pass method is replaced with censor

{-# LANGUAGE PolymorphicComponents #-}
module Control.Monad.StreamWriter 
( StreamWriter (StreamWriter)
, runStreamWriter
, writer, tell, censor
)where

import Control.Monad

newtype StreamWriter w a 
  = StreamWriter { runner :: forall m. Monad m => (w -> m ()) -> m a }

runStreamWriter sink a = runner a sink

instance Monad (StreamWriter w) where
  return x = StreamWriter $ const $ return x
  m >>= f = StreamWriter (\ab -> 
    runStreamWriter ab m >>= runStreamWriter ab . f)
  m1 >> m2 = StreamWriter (\ab -> 
    runStreamWriter ab m1 >> runStreamWriter ab m2)

instance Functor (StreamWriter w) where fmap = liftM

writer (a,w) = StreamWriter (\ab -> ab w >> return a)
tell w = StreamWriter ($ w)

censor :: (w1 -> w2) -> StreamWriter w1 a -> StreamWriter w2 a
censor f wa = StreamWriter $ \ab -> runStreamWriter (ab.f) wa
