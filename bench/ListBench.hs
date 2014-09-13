{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ListBench where

import           List

import           Test.LiquidCheck
import qualified Test.QuickCheck        as QC
import qualified Test.SmallCheck        as SC
import qualified Test.SmallCheck.Series as SC

import qualified LazySmallCheck as LSC

import Debug.Trace

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

instance LSC.Serial a => LSC.Serial (List a) where
  series = LSC.cons0 Nil LSC.\/ LSC.cons2 Cons

prop_insert_lsc d x ys = (llen ys == d && sorted ys) LSC.==> sorted (insert x ys)
