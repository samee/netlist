module Test.Gcil where

import Control.Monad.State.Strict
import Circuit.Gcil.Array
import Circuit.Gcil.Compiler as GC
import Data.List
import Debug.Trace
import System.IO

-- Fragile tests. Disabled for now
{-
testAplusb = result >>= return.fst
  where
  expected = ".input t1 1 8\n.input t2 2 8\nt3 add t1 t2\n.output t3\n"
  result = compile [8,8] [1,2] (\[a,b] -> addWithCarryU a b >>= return.(:[]))

testConcat = result >>= return.fst
  where
  expected = ".input t1 1 8\n.input t2 2 16\nt3 concat t1 t2\n"
          ++ "t4 select t3 0 16\nt5 select t3 16 24\n.output t5\n.output t4\n"
  result = compile [8,16] [1,2] (\[a,b] -> do
    c <- GC.concat [a,b]
    [a',b'] <- unconcat [gblWidth a, gblWidth b] c
    return [a',b'])
runTests = do putStrLn $ show testAplusb ++ "   Test.Garbled.testAplusb"
              putStrLn $ show testConcat ++ "   Test.Garbled.testConcat"
              -}

writeTestCase ::  String -> GcilMonad a -> 
                  (a -> [(String,Int)]) -> (a -> [(String,Int)]) -> IO ()
writeTestCase testName ckt serverInputs clientInputs = do
  (ins,cost) <- withFile ("gcilouts/"++testName++".cir") WriteMode
                  (evalStateT ckt' . GC.initState)
  writeFile ("gcilouts/"++testName++"-server.in") $ showpair $ serverInputs ins
  writeFile ("gcilouts/"++testName++"-client.in") $ showpair $ clientInputs ins
  putStrLn $ testName ++ " uses "++ show cost ++ " non-free gates"
  where
  ckt' = do ins <- ckt
            cost <- gets totalAndGates
            return (ins,cost)
  showpair l = Prelude.concat $ intersperse "\n" $ map vline l
  vline (n,v) = n ++ " " ++ show v

runTests :: IO ()
runTests = return ()
