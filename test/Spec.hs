module Spec where

import           Test.Hspec

spec :: Spec
spec = do
  describe "system test" $ do
    it "The Matrix is in order" $
      (1 :: Int) `shouldBe` 1
