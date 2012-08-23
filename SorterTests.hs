import Test.Gcil
import Test.Sorter
import Test.StableMarriage

main = do Test.Sorter.runTests
          Test.Gcil.runTests
          Test.StableMarriage.runTests
