{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE ViewPatterns         #-}
module Test.LiquidCheck.Testable where

import           Control.Applicative
import           Control.Arrow                 (second)
import           Control.Exception             (SomeException, evaluate, try)
import           Control.Monad
import           Control.Monad.State
import qualified Data.HashMap.Strict           as M
import           Data.Proxy
import           Text.Printf

import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types (RType (..), SpecType, bkClass,
                                                bkUniv, bkArrowDeep)

import           Test.LiquidCheck.Constrain
import           Test.LiquidCheck.Driver
import           Test.LiquidCheck.Eval
import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util

type family Args a where
  Args (a -> b -> c -> d -> e) = (a,b,c,d)
  Args (a -> b -> c -> d) = (a,b,c)
  Args (a -> b -> c) = (a,b)
  Args (a -> b) = a

type family Res a where
  Res (a -> b -> c -> d -> e) = e
  Res (a -> b -> c -> d) = d
  Res (a -> b -> c) = c
  Res (a -> b) = b

type CanTest f = (Testable f, Show (Args f), Constrain (Res f))

test :: CanTest f => f -> Int -> SpecType -> Gen Result
test f d t 
  = do xs <- genArgs f d t
       cts <- gets freesyms
       vals <- allSat $ map symbol xs
       let (xs, tis, to) = bkArrowDeep $ stripQuals t
       process d f vals cts (zip xs tis) to

process :: CanTest f 
        => Int -> f -> [[Value]] -> [(Symbol,Symbol)] -> [(Symbol,SpecType)] -> SpecType
        -> Gen Result
process d f vs cts xts to = go vs 0
  where
    go []       !n = return $ Passed n
    go (vs:vss) !n = do
      when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
      setValues vs
      xs <- stitchArgs f d (map snd xts)
      whenVerbose $ io $ print xs
      er <- io $ try $ evaluate (apply f xs)
      whenVerbose $ io $ print er
      case er of
        Left (e :: SomeException) -> return $ Failed $ show xs
        Right r -> do
          let env = map (second (`app` [])) cts ++ mkExprs f (map fst xts) xs
          sat <- evalType (M.fromList env) to (toExpr r)
          case sat of
            False -> return $ Failed $ show xs
            True -> go vss (n+1)

class Testable f where
  genArgs    :: f -> Int -> SpecType -> Gen [Variable]
  stitchArgs :: f -> Int -> [SpecType] -> Gen (Args f)
  apply      :: f -> Args f -> Res f
  mkExprs    :: f -> [Symbol] -> Args f -> [(Symbol,Expr)]

instance ( Constrain a, Constrain b
         , Args (a -> b) ~ a
         , Res (a -> b) ~ b)
  => Testable (a -> b) where
  genArgs _ d (stripQuals -> (RFun x i o _))
    = (:[]) <$> gen (Proxy :: Proxy a) d i
  stitchArgs _ d [t] 
    = stitch d t
  apply f a 
    = f a
  mkExprs _ [x] a 
    = [(x,toExpr a)]

instance ( Constrain a, Constrain b, Constrain c
         , Args (a -> b -> c) ~ (a,b)
         , Res (a -> b -> c) ~ c)
  => Testable (a -> b -> c) where
  genArgs _ d (stripQuals -> (RFun xa ta (RFun xb tb to _) _))
    = do a <- gen (Proxy :: Proxy a) d ta
         let tb' = subst (mkSubst [(xa, var a)]) tb
         b <- gen (Proxy :: Proxy b) d tb'
         return [a,b]
  stitchArgs _ d [ta,tb]
    = do b <- stitch d tb
         a <- stitch d ta
         return (a,b)
  apply f (a,b) 
    = f a b
  mkExprs _ [xa,xb] (a,b) 
    = [(xa,toExpr a), (xb,toExpr b)]

instance ( Constrain a, Constrain b, Constrain c, Constrain d
         , Args (a -> b -> c -> d) ~ (a,b,c)
         , Res (a -> b -> c -> d) ~ d)
  => Testable (a -> b -> c -> d) where
  genArgs _ d (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc to _) _) _))
    = do a <- gen (Proxy :: Proxy a) d ta
         let tb' = subst (mkSubst [(xa, var a)]) tb
         b <- gen (Proxy :: Proxy b) d tb'
         let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
         c <- gen (Proxy :: Proxy c) d tc'
         return [a,b,c]
  stitchArgs _ d [ta,tb,tc]
    = do c <- stitch d tc
         b <- stitch d tb
         a <- stitch d ta
         return (a,b,c)
  apply f (a,b,c) 
    = f a b c
  mkExprs _ [xa,xb,xc] (a,b,c) 
    = [(xa,toExpr a), (xb,toExpr b), (xc,toExpr c)]

instance ( Constrain a, Constrain b, Constrain c, Constrain d, Constrain e
         , Args (a -> b -> c -> d -> e) ~ (a,b,c,d)
         , Res (a -> b -> c -> d -> e) ~ e)
  => Testable (a -> b -> c -> d -> e) where
  genArgs _ d (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc (RFun xd td to _) _) _)_))
    = do a <- gen (Proxy :: Proxy a) d ta
         let tb' = subst (mkSubst [(xa, var a)]) tb
         b <- gen (Proxy :: Proxy b) d tb'
         let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
         c <- gen (Proxy :: Proxy c) d tc'
         let td' = subst (mkSubst [(xa, var a), (xb, var b), (xc, var c)]) td
         d <- gen (Proxy :: Proxy d) d td'
         return [a,b,c,d]
  stitchArgs _ sz [ta,tb,tc,td]
    = do d <- stitch sz td
         c <- stitch sz tc
         b <- stitch sz tb
         a <- stitch sz ta
         return (a,b,c,d)
  apply f (a,b,c,d) 
    = f a b c d
  mkExprs _ [xa,xb,xc,xd] (a,b,c,d)
    = [(xa,toExpr a), (xb,toExpr b), (xc,toExpr c), (xd,toExpr d)]

