import Test.Tasty
import Test.Tasty.HUnit

foo x = (x, x)

main :: IO ()
main = defaultMain $ testGroup "act"
  [ testGroup "print"
    [ testCase "printExp" $ 2 + 2 @?= 5 ]
  ]

