-- FIXME these names are NOT cabal friendly. Think of how somebody else
--   would use these packages/run tests etc.
import Test.ArrayGcil
import Test.StackGcil
import Test.StackDimacs
import Test.QueueGcil
import Benchmark.Demo
import Benchmark.Demo2
import Benchmark.DimacsDemo

main = Benchmark.Demo.runTests

{-
main = do Test.DimacsDemo.runTests
          Test.Array.runTests
          Test.StackCircuits.runTests
          Test.StackDimacs.runTests
          Test.QueueCircuits.runTests
          Test.Demo.runTests
          -}
