{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ExprBench where

import           Expr

import           Control.Applicative
import qualified Data.Set               as Set

import           Test.Target
import qualified Test.QuickCheck        as QC
import qualified Test.SmallCheck        as SC
import qualified Test.SmallCheck.Series as SC
import qualified LazySmallCheck         as LSC

import System.IO.Unsafe

--------------------------------------------------------------------------------
--- SmallCheck
--------------------------------------------------------------------------------
instance Monad m => SC.Serial m Expr

prop_subst_sc d e1 n e2 
  = (hasDepth d e1 || hasDepth d e2) && closed e1 && closed e2 SC.==> closed e
  where
    e     = subst e1 n e2

instance LSC.Serial Expr where
  series = LSC.cons1 Var LSC.\/ LSC.cons2 App LSC.\/ LSC.cons2 Lam

prop_subst_lsc d e1 n e2 
  = (hasDepth d e1 || hasDepth d e2) && closed e1 && closed e2 LSC.==>
    (unsafePerformIO $ case closed e of
                         True -> LSC.decValidCounter >> return True
                         False -> return False
    )
  where
    e     = subst e1 n e2

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

prop_subst_qc e1 n e2 = closed e1 && closed e2 QC.==> closed e
  where
    e     = subst e1 n e2
