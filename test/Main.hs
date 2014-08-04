{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import           Control.Exception
import           GHC.IO.Handle
-- import qualified Language.Haskell.TH as TH
import           System.IO
import           Test.Tasty
import           Test.Tasty.HUnit

import           Test.LiquidCheck

import qualified Data.ByteString.Internal as ByteString
import qualified Expr
import qualified HOFs
import qualified Map
import           List                (List)
import qualified List
import qualified RBTree


main = defaultMain tests

tests, pos, neg :: TestTree

tests = testGroup "Tests" [pos, neg]

pos = testGroup "Pos" $
  [ mkSuccess (List.insert :: Int -> List Int -> List Int)
      "List.insert" "test/List.hs" 3
  , mkSuccess (List.mymap) "List.mymap" "test/List.hs" 3
  , mkSuccess HOFs.foo "HOFs.foo" "examples/HOFs.hs" 3
  , mkSuccess HOFs.list_foo "HOFs.list_foo" "examples/HOFs.hs" 3
  ]
  ++ [ mkSuccess f ("RBTree."++name) "test/RBTree.hs" 6 | (name, T f) <- RBTree.liquidTests]
  ++ [ mkSuccess f ("Map."++name) "test/Map.hs" 5 | (name, T f) <- Map.liquidTests]
  ++ [ mkSuccess f ("Data.ByteString.Internal."++name) "test/Data/ByteString/Internal.hs" 4 | (name, T f) <- ByteString.liquidTests]
  ++ [ mkSuccess f ("Expr."++name) "test/Expr.hs" 3 | (name, T f) <- Expr.liquidTests]

neg = testGroup "Neg" $
  [ mkFailure (List.insert_bad :: Int -> List Int -> List Int)
      "List.insert" "test/List.hs" 3
  , mkFailure HOFs.foo_bad "HOFs.foo" "examples/HOFs.hs" 3
  , mkFailure HOFs.list_foo_bad "HOFs.list_foo" "examples/HOFs.hs" 3
  ]
  ++ [ mkFailure f ("RBTree."++name) "test/RBTree.hs" 6 | (name, T f) <- RBTree.liquidTests_bad]
  ++ [ mkFailure f ("Map."++name) "test/Map.hs" 5 | (name, T f) <- Map.liquidTests_bad]

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

shouldFail d f name file
  = do r <- testOne f name d file
       assertBool "Expected counter-example" $ case r of
                                               Passed _ -> False
                                               _        -> True

