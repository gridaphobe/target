{-@ LIQUID "-g-package-db" @-}
{-@ LIQUID "-g.cabal-sandbox/x86_64-osx-ghc-7.6.3-packages.conf.d" @-}
{-@ LIQUID "-g-no-user-package-db" @-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
module Main where

import GHC.Generics
import LiquidSMT

data List a = Nil | Cons a (List a) deriving (Generic, Show)
instance Constrain a => Constrain (List a)
{-@ data List a <p:: a -> a -> Prop> = Nil | Cons (zoo::a) (zoog::List <p> (a<p zoo>)) @-}
{-@ measure llen :: List a -> Int
    llen(Nil) = 0
    llen(Cons x xs) = 1 + llen(xs)
  @-}

{-@ type SortedList a = List <{\x y -> x < y}> a @-}

{-@ mytake :: n:Nat -> xs:SortedList Nat
           -> {v:SortedList Nat | (Min (llen v) n (llen xs))} @-}
mytake :: Int -> List Int -> List Int
mytake 0 xs     = Nil
mytake _ Nil     = Nil
mytake n (Cons x xs) = Cons x (mytake (n-1) xs)


-- insert :: Int -> [Int] -> [Int]
-- insert x [] = [x]
-- insert x (y:ys) | x < y    = x : y : ys
--                 | otherwise = y : insert x ys

tests = [ testFun mytake "Main.mytake" 2
        -- , testFun insert "Main.insert" 2
        ]

main = testModule "List.hs" tests
