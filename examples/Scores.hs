module Scores where

import Data.List (sort)
import Test.LiquidCheck

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NotZero = {v:Int | 0 != v} @-}
{-@ type Rng N = {v:Nat | v <= N} @-}
{-@ type Score = Rng 100 @-}

{-@ rescale :: r1:NotZero -> r2:NotZero -> s:Rng r1 -> Rng r2 @-}
rescale :: Int -> Int -> Int -> Int
rescale r1 r2 s = s * (r2 `div` r1)

{-@ average :: [(Pos, Score)] -> Score @-}
average :: [(Int,Int)] -> Int
average []  = 0
average wxs = tot `div` n
  where
    tot     = sum [w * x | (w, x) <- wxs]
    n       = sum [w     | (w, _) <- wxs]

-- insert  :: Score -> SList Score -> SList Score
-- best    :: k:Nat -> {v: List Score | k <= len v} -> {v:SortedList Score | k = len v}  

{-@ best   :: k:Nat -> [Score] -> {v:[Score] | len v = k} @-}
best :: Int -> [Int] -> [Int]
best k = take k . reverse . sort

-- best k = take k . reverse . sort . (replicate k 0 ++)
