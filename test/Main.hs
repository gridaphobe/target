{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
module Main where

import           Control.Exception
import           GHC.IO.Handle
-- import qualified Language.Haskell.TH as TH
import           System.IO
import           Test.Tasty
import           Test.Tasty.HUnit

import           Test.LiquidCheck

-- import qualified Data.ByteString.Internal as ByteString
import qualified HOFs
import           List                     (List)
import qualified List
import qualified MapTest                  as Map
import qualified RBTree
import qualified RBTreeTest               as RBTree


main = defaultMain tests

tests, pos, neg :: TestTree

tests = testGroup "Tests" [pos, neg]

pos = testGroup "Pos" $
  [ mkSuccess (List.insert :: Int -> List Int -> List Int)
      "List.insert" "test/List.hs" 3
  -- FIXME: doesn't work with SMT-based checking of post-condition
  -- , mkSuccess (List.mymap) "List.mymap" "test/List.hs" 3
  ]
--  ++ [ mkSuccess f name "test/HOFs.hs" 3 | (name, T f) <- HOFs.liquidTests]
  ++ [ mkSuccess f ("RBTree."++name) "test/RBTree.hs" 5 | (name, T f) <- RBTree.liquidTests]
  ++ [ mkSuccess f ("Map."++name) "test/Map.hs" 4 | (name, T f) <- Map.liquidTests]
  --FIXME: need a better solution for checking equality that respects custom Eq instances
  -- ++ [ mkSuccess f ("Data.ByteString.Internal."++name) "test/Data/ByteString/Internal.hs" 4 | (name, T f) <- ByteString.liquidTests]

neg = testGroup "Neg" $
  [ mkFailure (List.insert_bad :: Int -> List Int -> List Int)
      "List.insert" "test/List.hs" 3
  ]
--  ++ [ mkFailure f name "test/HOFs.hs" 3 | (name, T f) <- HOFs.liquidTests_bad]
  ++ [ mkFailure f ("RBTree."++name) "test/RBTree.hs" 5 | (name, T f) <- RBTree.liquidTests_bad]
  ++ [ mkFailure f ("Map."++name) "test/Map.hs" 4 | (name, T f) <- Map.liquidTests_bad]

mkSuccess :: CanTest f => f -> String -> String -> Int -> TestTree
mkSuccess f n fp d
  = testCase (n ++ "/" ++ show d) $ shouldSucceed d f n fp

mkFailure :: CanTest f => f -> String -> String -> Int -> TestTree
mkFailure f n fp d
  = testCase (n ++ "/" ++ show d) $ shouldFail d f n fp

shouldSucceed d f name file
  = do r <- testOne f name d file
       assertString $ case r of
                       Passed _ -> ""
                       Failed s -> "Unexpected counter-example: " ++ s
                       Errored s -> "Unexpected error: " ++ s

shouldFail d f name file
  = do r <- testOne f name d file
       assertBool "Expected counter-example" $ case r of
                                               Passed _ -> False
                                               _        -> True

