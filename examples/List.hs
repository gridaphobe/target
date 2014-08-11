{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module List where

import           Control.Monad
import           GHC.Generics
import           Test.LiquidCheck
import qualified Test.QuickCheck        as QC
import qualified Test.SmallCheck        as SC
import qualified Test.SmallCheck.Series as SC

import           Data.Proxy
import           Debug.Trace

--------------------------------------------------------------------------------
--- Code
--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a) deriving (Generic, Show)
infixr `Cons`

insert :: Int -> List Int -> List Int
insert x Nil
  = Cons x Nil
insert x (y `Cons` ys)
  | x < y
  = x `Cons` y `Cons` ys
  | x == y
  = y `Cons` ys
  | otherwise
  = y `Cons` insert x ys

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
--- LiquidCheck
--------------------------------------------------------------------------------
instance Constrain a => Constrain (List a)

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

--------------------------------------------------------------------------------
--- QuickCheck
--------------------------------------------------------------------------------
instance QC.Arbitrary a => QC.Arbitrary (List a) where
  arbitrary = QC.sized gen
    where
      gen n
        | n <= 0    = return Nil
        | otherwise = do x  <- QC.arbitrary
                         xs <- gen (n-1)
                         return $ Cons x xs

llen Nil         = 0
llen (Cons x xs) = 1 + llen xs

sorted Nil  = True
sorted (Cons x Nil) = True
sorted (Cons x (Cons y zs))
 | x < y && sorted (Cons y zs) = True
 | otherwise                   = False

prop_insert_qc x ys = sorted ys QC.==> sorted (insert x ys)

prop_mytake_sorted_qc n xs = sorted xs && n >= 0 && aall (>=0) xs && llen xs >= 1
  QC.==> sorted zs && mmin (llen zs) n (llen xs)
  where
    zs = mytake n xs

mmin v x y
  | x < y     = v == x
  | otherwise = v == y

aall p Nil           = True
aall p (Cons x xs)
  | p x && aall p xs = True
  | otherwise       = False

--------------------------------------------------------------------------------
--- SmallCheck
--------------------------------------------------------------------------------
instance SC.Serial m a => SC.Serial m (List a)

prop_mytake_sorted_sc n xs = sorted xs && n >= 0 && aall (>=0) xs
  SC.==> sorted zs && mmin (llen zs) n (llen xs)
  where
    zs = mytake n xs

prop_insert_sc x ys = sorted ys SC.==> sorted (insert x ys)

-- insert :: Int -> [Int] -> [Int]
-- insert x [] = [x]
-- insert x (y:ys) | x < y    = x : y : ys
--                 | otherwise = y : insert x ys

tests = [ liquidCheck insert "List.insert" 2
        ]

--main = testModule "examples/List.hs" tests
