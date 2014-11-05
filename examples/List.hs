{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module List where

import           GHC.Generics
import           Test.Target

--------------------------------------------------------------------------------
--- Code
--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a) deriving (Generic, Show)
infixr `Cons`

insert :: Int -> List Int -> List Int
insert x ys = insert' x ys

insert' x Nil
  = Cons x Nil
insert' x (y `Cons` ys)
  | x < y
  = x `Cons` y `Cons` ys
  | x == y
  = y `Cons` ys
  | otherwise
  = y `Cons` insert' x ys

insert_bad :: Int -> List Int -> List Int
insert_bad x Nil
  = Cons x Nil
insert_bad x (y `Cons` ys)
  | x < y
  = x `Cons` y `Cons` ys
  | otherwise
  = y `Cons` insert_bad x ys

mytake :: Int -> List Int -> List Int
mytake 0 xs          = Nil
mytake _ Nil         = Nil
mytake n (Cons x xs) = x `Cons` mytake (n-1) xs

{-@ mymap :: (Int -> Int) -> x:List Int -> {v:List Int | (llen v) = (llen x)} @-}
mymap :: (Int -> Int) -> List Int -> List Int
mymap f Nil         = Nil
mymap f (Cons x xs) = Cons (f x) (mymap f xs)

--------------------------------------------------------------------------------
--- Target
--------------------------------------------------------------------------------
instance Targetable a => Targetable (List a)

{-@ data List a <p:: a -> a -> Prop> =
      Nil | Cons (zoo::a) (zoog::List <p> (a<p zoo>))
  @-}

{-@ measure llen :: List a -> Int
    llen(Nil) = 0
    llen(Cons x xs) = 1 + llen(xs)
  @-}

{-@ type SortedList a = List <{\x y -> x < y}> a @-}

{-@ mytake :: n:Nat -> xs:SortedList Nat
           -> {v:SortedList Nat | (Min (llen v) n (llen xs))} @-}

{-@ insert :: n:Int -> xs:SortedList Int -> SortedList Int @-}

