import Test.Gcil
import Test.Sorter
import Test.StableMarriage
import Test.Stack

main = do Test.Sorter.runTests
          Test.Gcil.runTests
          Test.Stack.runTests
          -- :( Test.StableMarriage.runTests
