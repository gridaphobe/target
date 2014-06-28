{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE ViewPatterns         #-}
module Test.LiquidCheck.Testable where

import           Control.Arrow                 (second)
import           Control.Exception             (evaluate)
import           Control.Monad
import           Control.Monad.State
import qualified Data.HashMap.Strict           as M
import           Data.Proxy

import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types (RType (..), SpecType, bkClass,
                                                bkUniv)

import           Test.LiquidCheck.Constrain
import           Test.LiquidCheck.Driver
import           Test.LiquidCheck.Eval
import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util


class Testable a where
  test :: a -> Int -> SpecType -> Gen Result

instance (Constrain a, Constrain b) => Testable (a -> b) where
  test f d (stripQuals -> (RFun x i o _)) = do
    a <- gen (Proxy :: Proxy a) d i
    cts <- gets freesyms
    vals <- allSat [a]
    process1 d f vals cts x o
    -- build up the haskell value
    --(xvs :: [a]) <- forM vals $ \ vs -> do
    --  setValues vs
    --  stitch d
    --foldM (\case
    --          r@(Failed _) -> const $ return r
    --          (Passed n) -> \a -> do
    --            io $ print a
    --            r <- io $ evaluate (f a)
    --            let env = map (second (`app` [])) cts ++ [(x, toExpr a)]
    --            sat <- evalType (M.fromList env) o (toExpr r)
    --            case sat of
    --              False -> return $ Failed $ show a
    --              True  -> return $ Passed (n+1))
    --  (Passed 0) xvs
  test f d t = error $ show t

process1 d f vs cts x to = go vs 0
  where
    go []       !n = return $ Passed n
    go (vs:vss) !n =
      do setValues vs
         a <- stitch d
         io $ print a
         r <- io $ evaluate (f a)
         let env = map (second (`app` [])) cts
                ++ [(x, toExpr a)]
         sat <- evalType (M.fromList env) to (toExpr r)
         case sat of
           False -> return $ Failed $ show a
           True  -> go vss (n+1) -- return $ Passed (n+1))

fourth4 (_,_,_,d) = d

stripQuals = snd . bkClass . fourth4 . bkUniv

instance (Constrain a, Constrain b, Constrain c) => Testable (a -> b -> c) where
  test f d (stripQuals -> (RFun xa ta (RFun xb tb to _) _)) = do
    a <- gen (Proxy :: Proxy a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (Proxy :: Proxy b) d tb'
    cts <- gets freesyms
    vals <- allSat [a, b]
    -- -- build up the haskell value
    -- (xvs :: [(a,b)]) <- forM vals $ \ vs -> do
    --   setValues vs
    --   !b <- stitch d
    --   !a <- stitch d
    --   io $ print (a,b)
    --   return (a,b)
    process d f vals cts xa xb to
    -- foldM (\case
    --           r@(Failed _) -> const $ return r
    --           (Passed n) -> \vs -> do
    --             setValues vs
    --             b <- stitch d
    --             a <- stitch d
    --             -- io $ print (a,b)
    --             r <- io $ evaluate (f a b)
    --             let env = map (second (`app` [])) cts
    --                    ++ [(show xa, toExpr a),(show xb, toExpr b)]
    --             sat <- evalType (M.fromList env) to (toExpr r)
    --             case sat of
    --               False -> return $ Failed $ show (a, b)
    --               True  -> return $ Passed (n+1))
    --   (Passed 0) vals
  test f d t = error $ show t

process d f vs cts xa xb to = go vs 0
  where
    go []       !n = return $ Passed n
    go (vs:vss) !n =
      do setValues vs
         b <- stitch d
         a <- stitch d
         -- io $ print (a,b)
         r <- io $ evaluate (f a b)
         let env = map (second (`app` [])) cts
                ++ [(xa, toExpr a),(xb, toExpr b)]
         sat <- evalType (M.fromList env) to (toExpr r)
         case sat of
           False -> return $ Failed $ show (a, b)
           True  -> go vss (n+1) -- return $ Passed (n+1))

instance (Constrain a, Constrain b, Constrain c, Constrain d)
         => Testable (a -> b -> c -> d) where
  test f d (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc to _) _) _)) = do
    a <- gen (Proxy :: Proxy a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (Proxy :: Proxy b) d tb'
    let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
    c <- gen (Proxy :: Proxy c) d tc'
    cts <- gets freesyms
    vals <- allSat [a, b, c]
    -- build up the haskell value
    (xvs :: [(a,b,c)]) <- forM vals $ \ vs -> do
      setValues vs
      !c <- stitch d
      !b <- stitch d
      !a <- stitch d
      return (a,b,c)
    foldM (\case
              r@(Failed _) -> const $ return r
              (Passed n) -> \(a,b,c) -> do
                r <- io $ evaluate (f a b c)
                let env = map (second (`app` [])) cts
                       ++ [(xa, toExpr a),(xb, toExpr b),(xc, toExpr c)]
                sat <- evalType (M.fromList env) to (toExpr r)
                case sat of
                  False -> return $ Failed $ show (a, b, c)
                  True  -> return $ Passed (n+1))
      (Passed 0) xvs
  test f d t = error $ show t
