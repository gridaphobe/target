module HOFs where

import           Test.LiquidCheck

{-@ foo :: (x:Int -> {v:Int | v > x}) -> {v:Int | v > 0} @-}
foo :: (Int -> Int) -> Int
foo f = f 0

foo_bad :: (Int -> Int) -> Int
foo_bad f = f (-1)

{-@ list_foo :: xs:{[Int] | len xs > 0} -> (xs:[Int] -> {v:[Int] | len v < len xs})
             -> {v:[Int] | len v < len xs}
  @-}
list_foo :: [Int] -> ([Int] -> [Int]) -> [Int]
list_foo xs f = f xs

list_foo_bad :: [Int] -> ([Int] -> [Int]) -> [Int]
list_foo_bad xs f = f []

liquidTests, liquidTests_bad :: [(String,Test)]
liquidTests     = [("HOFs.foo", T foo), ("HOFs.list_foo", T list_foo)]
liquidTests_bad = [("HOFs.foo", T foo_bad), ("HOFs.list_foo", T list_foo_bad)]
