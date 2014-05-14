{-@ LIQUID "-g-package-db" @-}
{-@ LIQUID "-g.cabal-sandbox/x86_64-osx-ghc-7.6.3-packages.conf.d" @-}
{-@ LIQUID "-g-no-user-package-db" @-}

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import GHC.Generics
import LiquidSMT

{-@ mytake :: n:Nat -> xs:[Nat]<{\x y -> x < y}>
           -> {v:[Nat]<{\x y -> x < y}> | (Min (len v) n (len xs))} @-}
mytake :: Int -> [Int] -> [Int]
mytake 0 xs     = []
mytake _ []     = []
mytake n (x:xs) = x : mytake (n-1) xs


tests = [ testFun mytake "Main.mytake" 1 ]

main = testModule "List.hs" tests
