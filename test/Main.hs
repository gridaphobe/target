{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Control.Exception
import           GHC.IO.Handle
import qualified Language.Haskell.TH as TH
import           System.IO
import           Test.Tasty
import           Test.Tasty.HUnit

import           Test.LiquidCheck

import qualified Map
import           List                (List)
import qualified List
import           RBTree              (RBTree)
import qualified RBTree


main = defaultMain tests

tests, pos, neg :: TestTree

tests = testGroup "Tests" [pos, neg]

pos = testGroup "Pos" $
  [ mkSuccess (List.insert :: Int -> List Int -> List Int)
      "List.insert" "test/List.hs" 3
  , mkSuccess (RBTree.add :: Int -> RBTree Int -> RBTree Int)
      "RBTree.add" "test/RBTree.hs" 3
  ] ++ [ mkSuccess f ("Map."++name) "test/Map.hs" 5 | (name, T f) <- Map.liquidTests]

neg = testGroup "Neg" $
  [ mkFailure (List.insert_bad :: Int -> List Int -> List Int)
      "List.insert" "test/List.hs" 3
  , mkFailure (RBTree.add_bad :: Int -> RBTree Int -> RBTree Int)
      "RBTree.add" "test/RBTree.hs" 3
  ] ++ [ mkFailure f ("Map."++name) "test/Map.hs" 5 | (name, T f) <- Map.liquidTests_bad]

mkSuccess :: Testable f => f -> String -> String -> Int -> TestTree
mkSuccess f n fp d
  = testCase (n ++ "/" ++ show d) $ shouldSucceed d f n fp
  -- = do loc <- TH.location
  --      let name = show f
  --          file = TH.loc_filename loc
  --      [| shouldSucceed d $(TH.varE f) $(TH.stringE name) $(TH.stringE file) |]

mkFailure :: Testable f => f -> String -> String -> Int -> TestTree
mkFailure f n fp d
  = testCase (n ++ "/" ++ show d) $ shouldFail d f n fp
  -- = do loc <- TH.location
  --      let name = show f
  --          file = TH.loc_filename loc
  --      [| shouldFail d $(TH.varE f) $(TH.stringE name) $(TH.stringE file) |]

shouldSucceed d f name file
  = do r <- testOne d f name file
       assertString $ case r of
                       Passed _ -> ""
                       Failed s -> "Unexpected counter-example: " ++ s

shouldFail d f name file
  = do r <- testOne d f name file
       assertBool "Expected counter-example" $ case r of
                                               Passed _ -> False
                                               _        -> True

