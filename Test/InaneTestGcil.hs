module Test.InaneTestGcil where

import Control.Monad
import Control.Monad.Writer

import Circuit.NetList
import Circuit.NetList.Gcil

theOp :: NetUInt -> NetWriter NetUInt
theOp x = do gt  <- greaterThan x (constInt 5)
             x'  <- condSub gt x (constInt 3)
             shx <- shiftLeft 1 x
             x   <- mux gt shx x'
             return x

theOpLocal x = if x>5 then x-3 else 2*x

gcTheOp v = do
  x <- testInt ServerSide 5 v
  y'<- testInt ClientSide 6 (theOpLocal v)
  y <- liftNet $ theOp x
  ignoreAndsUsed $ liftNet $ equal y y'

theLittleJohn :: NetUInt -> NetWriter NetUInt
theLittleJohn v = do wz <- wideZ; foldM addIfSmall wz [1..2^w] where
  addIfSmall s c = do small <- netNot =<< lessThan v (constInt c)
                      condAdd small s (constInt c)
  wideZ = extend (2*w) (constInt 0)
  w = intWidth v

theLittleJohnLocal x = ((x+1)*x) `div` 2

gcTheLittleJohn x = do
  v <- testInt ServerSide 18 x
  y'<- testInt ClientSide (2*18) (theLittleJohnLocal x)
  y <- liftNet $ theLittleJohn v
  ignoreAndsUsed $ liftNet $ equal y y'

shortTests = burnTestCase "inaneCase" $ gcTheOp 3

longTests  = burnTestCase "littleJohn" $ gcTheLittleJohn 20000
