module Main

import Test.Golden

%default covering

allTests : TestPool
allTests = MkTestPool "allTests" [] Default
  [ "test001", "test002"
  ]

main : IO ()
main = runner
  [ testPaths "effect" allTests
  ] where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = record { testCases $= map ((dir ++ "/") ++) }
