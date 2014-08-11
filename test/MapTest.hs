{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module MapTest where

import Map

import Control.Applicative
import qualified Data.List as L

import Test.LiquidCheck

--------------------------------------------------------------------
-- LiquidCheck
--------------------------------------------------------------------

-- The values aren't interesting in terms of the properties we want to check,
-- so treat the Map as a Set to reduce the search space
type K = Char
type V = ()
type M = Map Char ()

prop_difference_lc :: M -> M -> M
prop_difference_lc = difference

prop_delete_lc :: K -> M -> M
prop_delete_lc = delete

liquidTests :: [(String, Test)]
liquidTests = [ ("insert",       T (insert :: K -> V -> M -> M))
              , ("delete",       T (delete :: K -> M -> M))
              , ("union",        T (union :: M -> M -> M))
              , ("difference",   T (difference :: M -> M -> M))
              , ("intersection", T (intersection :: M -> M -> M))
              ]


liquidTests_bad :: [(String, Test)]
liquidTests_bad = [ ("insert",       T (insert_bad :: K -> V -> M -> M))
                  , ("delete",       T (delete_bad :: K -> M -> M))
                  , ("union",        T (union_bad :: M -> M -> M))
                  , ("difference",   T (difference_bad :: M -> M -> M))
                  , ("intersection", T (intersection_bad :: M -> M -> M))
                  ]


insert_bad = go
  where
    go :: Ord k => k -> a -> Map k a -> Map k a
    go kx x Tip = singleton kx x
    go kx x (Bin sz ky y l r) =
        case compare kx ky of
                  -- Bin ky y (go kx x l) r 
            --LIQUID: swapped balanceL and balanceR to inject bug
            LT -> balanceR ky y (go kx x l) r
            GT -> balanceL ky y l (go kx x r)
            EQ -> Bin sz kx x l r


delete_bad = go
  where
    go :: Ord k => k -> Map k a -> Map k a
    go _ Tip = Tip
    go k (Bin _ kx x l r) =
        case compare k kx of
            --LIQUID: swapped balanceL and balanceR to inject bug
            LT -> balanceL kx x (go k l) r
            GT -> balanceR kx x l (go k r)
            EQ -> glue kx l r

--LIQUID: having trouble injecting bugs here..
glue_bad :: k -> Map k a -> Map k a -> Map k a
glue_bad _    Tip r = r
glue_bad _    l Tip = l
glue_bad kcut l r
  | size l > size r = let (km, m, l') = deleteFindMax l in balanceR km m l' r
  | otherwise       = let (km, m, r') = deleteFindMin r in balanceL km m l r'


union_bad :: Ord k => Map k a -> Map k a -> Map k a
union_bad Tip t2  = t2
union_bad t1 Tip  = t1
union_bad t1 t2 = hedgeUnion_bad NothingS NothingS t1 t2

hedgeUnion_bad :: Ord a => MaybeS a -> MaybeS a -> Map a b -> Map a b -> Map a b
hedgeUnion_bad _   _   t1  Tip = t1
--LIQUID: injected bug in join'
hedgeUnion_bad blo bhi Tip (Bin _ kx x l r) = join'_bad kx x (filterGt blo l) (filterLt bhi r)
hedgeUnion_bad _   _   t1  (Bin _ kx x Tip Tip) = insertR kx x t1 -- According to benchmarks, this special case increases
                                                              -- performance up to 30%. It does not help in difference or intersection.
hedgeUnion_bad blo bhi (Bin _ kx x l r) t2 = join'_bad kx x (hedgeUnion_bad blo bmi l (trim blo bmi t2))
                                                   (hedgeUnion_bad bmi bhi r (trim bmi bhi t2))
  where bmi = JustS kx

join'_bad kx x Tip r  = insertMin kx x r
join'_bad kx x l Tip  = insertMax kx x l
join'_bad kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  --LIQUID changed both < to > to inject bug
  | delta*sizeL > sizeR  = balanceL kz z (join'_bad kx x l lz) rz
  | delta*sizeR > sizeL  = balanceR ky y ly (join'_bad kx x ry r)
  | otherwise            = bin kx x l r


difference_bad :: Ord k => Map k a -> Map k b -> Map k a
difference_bad Tip _   = Tip
difference_bad t1 Tip  = t1
difference_bad t1 t2   = hedgeDiff_bad NothingS NothingS t1 t2

hedgeDiff_bad :: Ord a => MaybeS a -> MaybeS a -> Map a b -> Map a c -> Map a b
hedgeDiff_bad _  _   Tip _                  = Tip
hedgeDiff_bad blo bhi (Bin _ kx x l r) Tip  = join'_bad kx x (filterGt blo l) (filterLt bhi r)
hedgeDiff_bad blo bhi t (Bin _ kx _ l r)    = merge_bad kx (hedgeDiff_bad blo bmi (trim_bad blo bmi t) l)
                                                   (hedgeDiff_bad bmi bhi (trim_bad bmi bhi t) r)
  where bmi = JustS kx

--LIQUID: having trouble injecting bug here
merge_bad _   Tip r   = r
merge_bad _   l Tip   = l
merge_bad kcut l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  | delta*sizeL > sizeR = balanceL ky y (merge_bad kcut l ly) ry
  | delta*sizeR > sizeL = balanceR kx x lx (merge_bad kcut rx r)
  | otherwise           = glue kcut l r


intersection_bad :: Ord k => Map k a -> Map k b -> Map k a
intersection_bad Tip _ = Tip
intersection_bad _ Tip = Tip
intersection_bad t1 t2 = hedgeInt_bad NothingS NothingS t1 t2

hedgeInt_bad :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k b -> Map k a
hedgeInt_bad _ _ _   Tip = Tip
hedgeInt_bad _ _ Tip _   = Tip
hedgeInt_bad blo bhi (Bin _ kx x l r) t2 = let l' = hedgeInt_bad blo bmi l (trim_bad blo bmi t2)
                                               r' = hedgeInt_bad bmi bhi r (trim_bad bmi bhi t2)
                                           in if kx `member` t2 then join' kx x l' r' else merge kx l' r'
  where bmi = JustS kx

trim_bad :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k a
trim_bad NothingS   NothingS   t = t
trim_bad (JustS lk) NothingS   t = greater lk t 

                                     --LIQUID: change <= to >=
  where greater lo t@(Bin _ k _ _ r) | k >= lo      = greater lo r
                                     | otherwise    = t
        greater _  t'@Tip                           = t'

trim_bad NothingS   (JustS hk) t = lesser hk t 

                                      --LIQUID: change >= to <=
  where lesser  hi t'@(Bin _ k _ l _) | k <= hi     = lesser  hi l
                                      | otherwise   = t'
        lesser  _  t'@Tip                           = t'
trim_bad (JustS lk) (JustS hk) t = middle lk hk t  
  where middle lo hi t'@(Bin _ k _ l r) | k <= lo   = middle lo hi r
                                        | k >= hi   = middle lo hi l
                                        | otherwise = t'
        middle _ _ t'@Tip = t'  

