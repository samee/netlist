module Test.InaneTestDimacs where

import Control.Monad

import Circuit.NetList
import Circuit.NetList.Dimacs
import Test.InaneTestGcil (theOp,theOpLocal,theLittleJohn)

dmTheOp res = do
  x <- freshInt 4
  eq <- liftNet $ do
          y <- theOp x
          equal y (constInt res)
  dmAssert eq
  dmPutStrLn $ "theOp "-|-x-|-" = "++show res

runTests = burnSatQuery "inaneCase" (dmTheOp 8)
