{-@ LIQUID "-g-package-db" @-}
{-@ LIQUID "-g.cabal-sandbox/x86_64-osx-ghc-7.6.3-packages.conf.d" @-}
{-@ LIQUID "-g-no-user-package-db" @-}

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import GHC.Generics
import LiquidSMT

{-@ type SortedList a = [a]<{\x y -> x < y}> @-}

{-@ mytake :: n:Nat -> xs:SortedList Nat
           -> {v:SortedList Nat | (Min (len v) n (len xs))} @-}
mytake :: Int -> [Int] -> [Int]
mytake 0 xs     = []
mytake _ []     = []
mytake n (x:xs) = x : mytake (n-1) xs


-- insert :: Int -> [Int] -> [Int]
-- insert x [] = [x]
-- insert x (y:ys) | x < y    = x : y : ys
--                 | otherwise = y : insert x ys

tests = [ testFun mytake "Main.mytake" 2
        -- , testFun insert "Main.insert" 2
        ]

main = testModule "List.hs" tests
