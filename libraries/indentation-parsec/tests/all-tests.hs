{-# LANGUAGE CPP #-}
module Main where

import Test.Tasty (defaultMain, testGroup)
import qualified ParensParsec 

main =
  defaultMain $ testGroup "All tests" $
  [
    ParensParsec.allTests
  ]
