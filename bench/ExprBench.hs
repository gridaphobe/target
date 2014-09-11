{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ExprBench where

import           Expr

import           Control.Applicative
import qualified Data.Set               as Set

import           Test.LiquidCheck
import qualified Test.QuickCheck        as QC
import qualified Test.SmallCheck        as SC
import qualified Test.SmallCheck.Series as SC
import qualified LazySmallCheck         as LSC

--------------------------------------------------------------------------------
--- SmallCheck
--------------------------------------------------------------------------------
instance Monad m => SC.Serial m Expr

prop_subst_sc e1 n e2 = closed e1 && closed e2 SC.==>
                        if Set.member n fv_e2
                        then fv_e == Set.union (Set.delete n fv_e2) fv_e1
                        else fv_e == fv_e2
  where
    e     = subst e1 n e2
    fv_e  = freeVars e
    fv_e1 = freeVars e1
    fv_e2 = freeVars e2

instance LSC.Serial Expr where
  series = LSC.cons1 Var LSC.\/ LSC.cons2 App LSC.\/ LSC.cons2 Lam

prop_subst_lsc e1 n e2 = closed e1 && closed e2 LSC.==>
                         if Set.member n fv_e2
                         then fv_e == Set.union (Set.delete n fv_e2) fv_e1
                         else fv_e == fv_e2
  where
    e     = subst e1 n e2
    fv_e  = freeVars e
    fv_e1 = freeVars e1
    fv_e2 = freeVars e2

--------------------------------------------------------------------------------
--- QuickCheck
--------------------------------------------------------------------------------
instance QC.Arbitrary Expr where
  arbitrary = QC.sized gen
    where
      gen n
        | n <= 0    = Var <$> QC.arbitrary
        | otherwise = QC.oneof [mkLam, mkApp]
        where
          mkLam = do x  <- QC.arbitrary
                     n' <- QC.choose (0, n-1)
                     e  <- gen n'
                     return $ Lam x e
          mkApp = do nx <- QC.choose (0, n `div` 2)
                     ny <- QC.choose (0, n `div` 2)
                     x  <- gen nx
                     y  <- gen ny
                     return $ App x y

prop_subst_qc e1 n e2 = closed e1 && closed e2 QC.==>
                        if Set.member n fv_e2
                        then fv_e == Set.union (Set.delete n fv_e2) fv_e1
                        else fv_e == fv_e2
  where
    e     = subst e1 n e2
    fv_e  = freeVars e
    fv_e1 = freeVars e1
    fv_e2 = freeVars e2
