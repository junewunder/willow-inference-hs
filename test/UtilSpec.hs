module UtilSpec (spec) where

import Import
import Util
import Test.Hspec
import Test.Hspec.QuickCheck

spec :: Spec
spec = do
  describe "capitalize" $ do
    it "capitalizes first letter" $ capitalize "hello" `shouldBe` "Hello"
    it "handles empty string" $ capitalize "" `shouldBe` ""
    it "handles single char" $ capitalize "h" `shouldBe` "H"
