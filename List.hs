{-@ LIQUID "-g-package-db" @-}
{-@ LIQUID "-g.cabal-sandbox/x86_64-osx-ghc-7.6.3-packages.conf.d" @-}
{-@ LIQUID "-g-no-user-package-db" @-}
{- LIQUID "-g-hide-package" @-}
{- LIQUID "-gmonads-tf" @-}

{- LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import LiquidSMT

{-@ mytake :: n:Nat -> xs:[Nat] -> {v:[Nat] | (Min (len v) n (len xs))} @-}
mytake :: Int -> [Int] -> [Int]
mytake 0 xs     = []
mytake _ []     = []
mytake n (x:xs) = x : mytake (n-1) xs



main = testOne (mytake) ("Main.mytake") "List.hs"
-- main = $(mkTest 'mytake)
