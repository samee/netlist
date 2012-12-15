-- A version of the Writer monad that is a bit more memory-friendly for
-- streaming use cases. Like the conventional Writer, but doesn't support
-- the listen method directly (although could be implemented in the inner 
-- monad). The pass method is replaced with censor
module Control.Monad.StreamWriter 
( StreamWriter (StreamWriter)
, runStreamWriter
, writer, tell, censor
)where

import Control.Monad
import Control.Monad.Trans.Class
import Data.Monoid

newtype StreamWriter w m a 
  = StreamWriter { runner :: (w -> m ()) -> m a }

runStreamWriter sink a = runner a sink

instance (Monad m,Monoid w) => Monad (StreamWriter w m) where
  return x = lift $ return x
  m >>= f = StreamWriter (\ab -> 
    runStreamWriter ab m >>= runStreamWriter ab . f)
  m1 >> m2 = StreamWriter (\ab -> 
    runStreamWriter ab m1 >> runStreamWriter ab m2)

instance MonadTrans (StreamWriter w) where
  lift a = StreamWriter $ const a

writer (a,w) = StreamWriter (\ab -> ab w >> return a)
tell w = StreamWriter ($ w)

censor :: (Monad m, Monoid w1, Monoid w2)
       => (w1 -> w2) -> StreamWriter w1 m a -> StreamWriter w2 m a
censor f wa = StreamWriter $ \ab -> runStreamWriter (ab.f) wa
