module Main where

import Test.LiquidCheck
import Test.SmallCheck

import Criterion.Main

import JSON
import List
import RBTree
import XMonad.Properties

main = defaultMain [
     bgroup "List.insert" $
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/List.hs" [liquidCheck insert "List.insert" n]
           , bench "SmallCheck" $ smallCheck n prop_insert_sc
           ]
       | n <- [2..5]
       ] ++
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/List.hs" [liquidCheck insert "List.insert" n]
           ]
       | n <- []
       ],
     bgroup "RBTree.add" $
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/RBTree.hs" [liquidCheck (add :: Int -> RBTree Int -> RBTree Int) "RBTree.add" n]
           , bench "SmallCheck" $ smallCheck n prop_add_sc
           ]
       | n <- [2..3]
       ] ++
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/RBTree.hs" [liquidCheck (add :: Int -> RBTree Int -> RBTree Int) "RBTree.add" n]
           ]
       | n <- []
       ],
     bgroup "JSON.inverse" $
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/JSON.hs" [liquidCheck prop_json_inv "JSON.prop_json_inv" n]
           , bench "SmallCheck" $ smallCheck n prop_json_inv
           ]
       | n <- [2..7]
       ],
     bgroup "XMonad.invariant" $
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/XMonad/Properties.hs" [liquidCheck prop_invariant_lc "XMonad.Properties.prop_invariant_lc" n]
           -- , bench "SmallCheck" $ smallCheck n prop_json_inv
           ]
       | n <- [2]
       ],
     bgroup "XMonad.focus_left_master" $
       [ bgroup (show n)
           [ bench "LiquidCheck" $ testModule "bench/XMonad/Properties.hs" [liquidCheck prop_focus_left_master_lc "XMonad.Properties.prop_focus_left_master_lc" n]
           --, bench "SmallCheck" $ smallCheck 6 prop_focus_left_master_sc
           ]
       | n <- [2]
       ]
    ]
