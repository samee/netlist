import Test.Array
import Test.StackCircuits
import Test.StackDimacs
import Test.QueueCircuits
import Test.Demo

import Circuit.Array

main = do Test.Array.runTests
          Test.StackCircuits.runTests
          Test.StackDimacs.runTests
          Test.QueueCircuits.runTests
          Test.Demo.runTests
