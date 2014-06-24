module Main where

import Test.LiquidCheck
import Test.SmallCheck

import Criterion.Main

import List

main = defaultMain [
     bgroup "List" [ bench "LiquidCheck" $ testModule "bench/List.hs" [liquidCheck mytake "List.mytake" 6]
                   , bench "SmallCheck" $ smallCheck 6 prop_mytake_sorted_sc
                   ]
     ]
