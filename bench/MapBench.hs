{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module MapBench where

import           Map

import           Control.Applicative
import qualified Data.List              as L

import           Test.LiquidCheck
import qualified Test.QuickCheck        as QC
import qualified Test.SmallCheck        as SC
import qualified Test.SmallCheck.Series as SC

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}
-- | /O(n)/. Test if the internal map structure is valid.
--
-- > valid (fromAscList [(3,"b"), (5,"a")]) == True
-- > valid (fromAscList [(5,"a"), (3,"b")]) == False

valid :: Ord k => Map k a -> Bool
valid t
 = balanced t && ordered t && validsize t

ordered :: Ord a => Map a b -> Bool
ordered t
 = bounded (const True) (const True) t
 where
   bounded lo hi t'
     = case t' of
         Tip              -> True
         Bin _ kx _ l r  -> (lo kx) && (hi kx) && bounded lo (<kx) l && bounded (>kx) hi r

balanced :: Map k a -> Bool
balanced t
 = case t of
     Tip            -> True
     Bin _ _ _ l r  -> (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                       balanced l && balanced r

validsize :: Map a b -> Bool
validsize t
 = (realsize t == Just (size t))
 where
   realsize t'
     = case t' of
         Tip            -> Just 0
         Bin sz _ _ l r -> case (realsize l,realsize r) of
                           (Just n,Just m)  | n+m+1 == sz  -> Just sz
                           _                               -> Nothing


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

--------------------------------------------------------------------------------
--- SmallCheck
--------------------------------------------------------------------------------
instance (Monad m, SC.Serial m k, SC.Serial m a) => SC.Serial m (Map k a)

prop_difference_sc :: Monad m => M -> M -> SC.Property m
prop_difference_sc x y = valid x && valid y SC.==> valid z && keys z == (keys x L.\\ keys y)
  where z = difference x y

prop_delete_sc :: Monad m => K -> M -> SC.Property m
prop_delete_sc x y = valid y SC.==> valid z && keys z == (keys y L.\\ [x])
  where z = delete x y

--------------------------------------------------------------------------------
--- QuickCheck
--------------------------------------------------------------------------------
instance (Enum k,QC.Arbitrary a) => QC.Arbitrary (Map k a) where
  arbitrary = QC.sized (arbtree 0 maxkey)
    where maxkey = 10^5
          -- NOTE: modified from actual definition to generate "truly arbitrary" trees
          arbtree :: (Enum k, QC.Arbitrary a) => Int -> Int -> Int -> QC.Gen (Map k a)
          arbtree lo hi n = do t <- gentree lo hi n
                               if balanced t then return t else arbtree lo hi n
            where gentree lo hi n
                    | n <= 0        = return Tip
                    | lo >= hi      = return Tip
                    | otherwise     = do{ x  <- QC.arbitrary
                                        ; i  <- QC.choose (lo,hi)
                                        ; l  <- gentree lo hi (n `div` 2)
                                        ; r  <- gentree lo hi (n `div` 2)
                                        ; return (bin (toEnum i) x l r)
                                        }

prop_difference_qc :: M -> M -> QC.Property
prop_difference_qc x y = valid x && valid y QC.==> valid z && keys z == (keys x L.\\ keys y)
  where z = difference x y

prop_delete_qc :: K -> M -> QC.Property
prop_delete_qc x y = valid y QC.==> valid z && keys z == (keys y L.\\ [x])
  where z = delete x y
