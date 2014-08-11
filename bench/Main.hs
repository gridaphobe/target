{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}
module Main where

import Test.LiquidCheck
import qualified Test.QuickCheck as QC
import qualified Test.SmallCheck as SC
import qualified Test.SmallCheck.Drivers as SC

-- import Criterion.Main
import Control.Concurrent.Timeout
import Data.IORef
import Data.Time.Clock.POSIX
import Data.Timeout

import MapBench (prop_delete_lc, prop_difference_lc,
                 prop_delete_qc, prop_difference_qc,
                 prop_delete_sc, prop_difference_sc)
import JSON
import Expr
import List -- (insert, prop_insert_sc)
import RBTree -- (RBTree, add, prop_add_sc)
import XMonad.Properties

main :: IO ()
main = undefined

myTimeout :: IO a -> IO (Maybe a)
myTimeout = timeout (5 # Minute)

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

mapDifferenceTests
  = do checkLiquid prop_difference_lc "Map.difference" "bench/Map.hs"
       --checkSmall  prop_difference_sc

checkLiquid :: CanTest f => f -> String -> FilePath -> IO ()
checkLiquid = undefined

--checkSmall :: (Monad m, SC.Testable m f) => f -> IO ()
checkSmall = undefined

runTestWithStats :: SC.Testable IO a => SC.Depth -> a
                 -> IO ((Integer,Integer), Maybe SC.PropertyFailure)
runTestWithStats d prop = do
  good <- newIORef 0
  bad <- newIORef 0

  let
    hook SC.GoodTest = modifyIORef' good (+1)
    hook SC.BadTest  = modifyIORef' bad  (+1)

  r <- SC.smallCheckWithHook d hook prop

  goodN <- readIORef good
  badN  <- readIORef bad

  return ((goodN, badN), r)

-- main = defaultMain [
--      bgroup "List.insert" $
--        [ bgroup (show n)
--            [ bench "LiquidCheck" $ myTimeout $ testModule "bench/List.hs" [liquidCheck insert "List.insert" n]
--            -- , bench "SmallCheck" $ smallCheck n prop_insert_sc
--            ]
--        | n <- [2..7]
--        ], --  ++
--        -- [ bgroup (show n)
--        --     [ bench "LiquidCheck" $ testModule "bench/List.hs" [liquidCheck insert "List.insert" n]
--        --     ]
--        -- | n <- [6]
--        -- ],
--      bgroup "RBTree.add" $
--        [ bgroup (show n)
--            [ bench "LiquidCheck" $ myTimeout $ testModule "bench/RBTree.hs" [liquidCheck (add :: Int -> RBTree Int -> RBTree Int) "RBTree.add" n]
--            -- , bench "SmallCheck" $ smallCheck n prop_add_sc
--            ]
--        | n <- [2..5]
--        ], --  ++
--        -- [ bgroup (show n)
--        --     [ bench "LiquidCheck" $ testModule "bench/RBTree.hs" [liquidCheck (add :: Int -> RBTree Int -> RBTree Int) "RBTree.add" n]
--        --     ]
--        -- | n <- [4]
--        -- ],
--      -- bgroup "JSON.inverse" $
--      --   [ bgroup (show n)
--      --       [ bench "LiquidCheck" $ testModule "bench/JSON.hs" [liquidCheck prop_json_inv "JSON.prop_json_inv" n]
--      --       -- , bench "SmallCheck" $ smallCheck n prop_json_inv
--      --       ]
--      --   | n <- [2..7]
--      --   ],
--      bgroup "XMonad.invariant" $
--        [ bgroup (show n)
--            [ bench "LiquidCheck" $ myTimeout $ testModule "bench/XMonad/Properties.hs" [liquidCheck prop_invariant_lc "XMonad.Properties.prop_invariant_lc" n]
--            ]
--        | n <- [2..4]
--        ],
--      bgroup "XMonad.focus_left_master" $
--        [ bgroup (show n)
--            [ bench "LiquidCheck" $ myTimeout $ testModule "bench/XMonad/Properties.hs" [liquidCheck prop_focus_left_master_lc "XMonad.Properties.prop_focus_left_master_lc" n]
--            --, bench "SmallCheck" $ smallCheck 6 prop_focus_left_master_sc
--            ]
--        | n <- [2..3]
--        ],
--      bgroup "Data.Map" 
--        [ bgroup name
--          [ bgroup (show n)
--            [ bench "LiquidCheck" $ myTimeout $ testModule "bench/Map.hs" [liquidCheck f ("Map."++name) n] ]
--          | n <- [2..7]
--          ]
--        | (name, T f) <- Map.liquidTests
--        ],
--      bgroup "Expr" 
--        [ bgroup name
--          [ bgroup (show n)
--            [ bench "LiquidCheck" $ myTimeout $ testModule "bench/Expr.hs" [liquidCheck f ("Expr."++name) n] ]
--          | n <- [2..4]
--          ]
--        | (name, T f) <- Expr.liquidTests
--        ]
--     ]
