import Test.Tasty
import Test.Tasty.HUnit

import RefinedAst
import Print

main :: IO ()
main = defaultMain $ testGroup "act"
  [ testGroup "print"
    [ testCase "printExp" $ prettyExp (LitInt 1) @?= "1" ]
  ]

