{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE IncoherentInstances  #-}
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

-- test :: (Testable f, Show (Args f), Constrain (Res f)) => f -> Int -> SpecType -> Gen Result
-- test f d t 
--   = do xs <- genArgs f d t
--        cts <- gets freesyms
--        vals <- allSat $ map symbol xs
--        let (xs, tis, to) = bkArrowDeep t
--        process d f vals cts (zip xs tis) to

-- process :: (Testable f, Show (Args f), Constrain (Res f)) => Int -> f -> [[Value]] -> [(Symbol,Symbol)] -> [(Symbol,SpecType)] -> SpecType 
--         -> Gen Result
-- process d f vs cts xts to = go vs 0
--   where
--     go []       !n = return $ Passed n
--     go (vs:vss) !n = do
--       when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
--       setValues vs
--       xs <- stitchArgs f d (map snd xts)
--       whenVerbose $ io $ print xs
--       er <- io $ try $ evaluate (apply f xs)
--       case er of
--         Left (e :: SomeException) -> return $ Failed $ show xs
--         Right r -> do
--           let env = map (second (`app` [])) cts ++ mkExprs f (map fst xts) xs
--           sat <- evalType (M.fromList env) to (toExpr r)
--           case sat of
--             False -> return $ Failed $ show xs
--             True -> go vss (n+1)

class Testable f where
  genArgs :: f -> Int -> SpecType -> Gen [Variable]
  stitchArgs :: f -> Int -> [SpecType] -> Gen (Args f)
  apply :: f -> Args f -> Res f
  mkExprs :: f -> [Symbol] -> Args f -> [(Symbol,Expr)]

instance (Constrain a, Constrain b) => Testable (a -> b) where
  genArgs _ d (stripQuals -> (RFun x i o _)) = (:[]) <$> gen (Proxy :: Proxy a) d i
  stitchArgs _ d [t] = stitch d t
  apply f a = f a
  mkExprs _ [x] a = [(x,toExpr a)]

-- instance (Constrain a, Constrain b, Constrain c) => Testable (a -> b -> c) where
--   test f d (stripQuals -> (RFun xa ta (RFun xb tb to _) _)) = do
--     a <- gen (Proxy :: Proxy a) d ta
--     let tb' = subst (mkSubst [(xa, var a)]) tb
--     b <- gen (Proxy :: Proxy b) d tb'
--     cts <- gets freesyms
--     vals <- allSat [symbol a, symbol b]
--     -- -- build up the haskell value
--     -- (xvs :: [(a,b)]) <- forM vals $ \ vs -> do
--     --   setValues vs
--     --   !b <- stitch d
--     --   !a <- stitch d
--     --   io $ print (a,b)
--     --   return (a,b)
--     process2 d f vals cts (xa,ta) (xb,tb) to
--     -- foldM (\case
--     --           r@(Failed _) -> const $ return r
--     --           (Passed n) -> \vs -> do
--     --             setValues vs
--     --             b <- stitch d
--     --             a <- stitch d
--     --             -- io $ print (a,b)
--     --             r <- io $ evaluate (f a b)
--     --             let env = map (second (`app` [])) cts
--     --                    ++ [(show xa, toExpr a),(show xb, toExpr b)]
--     --             sat <- evalType (M.fromList env) to (toExpr r)
--     --             case sat of
--     --               False -> return $ Failed $ show (a, b)
--     --               True  -> return $ Passed (n+1))
--     --   (Passed 0) vals
--   test f d t = error $ show t

-- process2 d f vs cts (xa,ta) (xb,tb) to = go vs 0
--   where
--     go []       !n = return $ Passed n
--     go (vs:vss) !n =
--       do when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
--          setValues vs
--          b <- stitch d tb
--          a <- stitch d ta
--          -- io $ print (a,b)
--          er <- io $ try $ evaluate (f a b)
--          case er of
--            Left (e::SomeException) -> return $ Failed $ show (a, b)
--            Right r -> do
--              let env = map (second (`app` [])) cts
--                     ++ [(xa, toExpr a),(xb, toExpr b)]
--              sat <- evalType (M.fromList env) to (toExpr r)
--              case sat of
--                False -> return $ Failed $ show (a, b)
--                True  -> go vss (n+1) -- return $ Passed (n+1))

-- instance (Constrain a, Constrain b, Constrain c, Constrain d)
--          => Testable (a -> b -> c -> d) where
--   test f d (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc to _) _) _)) = do
--     a <- gen (Proxy :: Proxy a) d ta
--     let tb' = subst (mkSubst [(xa, var a)]) tb
--     b <- gen (Proxy :: Proxy b) d tb'
--     let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
--     c <- gen (Proxy :: Proxy c) d tc'
--     cts <- gets freesyms
--     vals <- allSat [symbol a, symbol b, symbol c]
--     process3 d f vals cts (xa, ta) (xb, tb) (xc, tc) to
--     -- build up the haskell value
--     -- (xvs :: [(a,b,c)]) <- forM vals $ \ vs -> do
--     --   setValues vs
--     --   !c <- stitch d
--     --   !b <- stitch d
--     --   !a <- stitch d
--     --   return (a,b,c)
--     -- foldM (\case
--     --           r@(Failed _) -> const $ return r
--     --           (Passed n) -> \(a,b,c) -> do
--     --             r <- io $ evaluate (f a b c)
--     --             let env = map (second (`app` [])) cts
--     --                    ++ [(xa, toExpr a),(xb, toExpr b),(xc, toExpr c)]
--     --             sat <- evalType (M.fromList env) to (toExpr r)
--     --             case sat of
--     --               False -> return $ Failed $ show (a, b, c)
--     --               True  -> return $ Passed (n+1))
--     --   (Passed 0) xvs
--   test f d t = error $ show t

-- process3 d f vs cts (xa, ta) (xb, tb) (xc, tc) to = go vs 0
--   where
--     go []       !n = return $ Passed n
--     go (vs:vss) !n =
--       do when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
--          setValues vs
--          c <- stitch d tc
--          b <- stitch d tb
--          a <- stitch d ta
--          -- io $ print (a,b,c)
--          er <- io $ try $ evaluate (f a b c)
--          case er of
--            Left (e::SomeException) -> return $ Failed $ show (a, b, c)
--            Right r -> do
--              let env = map (second (`app` [])) cts
--                     ++ [(xa, toExpr a),(xb, toExpr b),(xc, toExpr c)]
--              sat <- evalType (M.fromList env) to (toExpr r)
--              case sat of
--                False -> return $ Failed $ show (a, b, c)
--                True  -> go vss (n+1) -- return $ Passed (n+1))


-- instance (Constrain a, Constrain b, Constrain c, Constrain d, Constrain e)
--          => Testable (a -> b -> c -> d -> e) where
--   test f sz (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc (RFun xd td to _) _) _) _)) = do
--     a <- gen (Proxy :: Proxy a) sz ta
--     let tb' = subst (mkSubst [(xa, var a)]) tb
--     b <- gen (Proxy :: Proxy b) sz tb'
--     let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
--     c <- gen (Proxy :: Proxy c) sz tc'
--     let td' = subst (mkSubst [(xa, var a), (xb, var b), (xc, var c)]) td
--     d <- gen (Proxy :: Proxy d) sz td'
--     cts <- gets freesyms
--     vals <- allSat [symbol a, symbol b, symbol c, symbol d]
--     process4 sz f vals cts (xa,ta) (xb,tb) (xc,tc) (xd,td) to
--     -- build up the haskell value
--     -- (xvs :: [(a,b,c,d)]) <- forM vals $ \ vs -> do
--     --   setValues vs
--     --   !d <- stitch sz
--     --   !c <- stitch sz
--     --   !b <- stitch sz
--     --   !a <- stitch sz
--     --   return (a,b,c,d)
--     -- foldM (\case
--     --           r@(Failed _) -> const $ return r
--     --           (Passed n) -> \(a,b,c,d) -> do
--     --             io $ print (a,b,c,d)
--     --             r <- io $ evaluate (f a b c d)
--     --             let env = map (second (`app` [])) cts
--     --                    ++ [(xa, toExpr a),(xb, toExpr b),(xc, toExpr c)]
--     --             sat <- evalType (M.fromList env) to (toExpr r)
--     --             case sat of
--     --               False -> return $ Failed $ show (a, b, c, d)
--     --               True  -> return $ Passed (n+1))
--     --   (Passed 0) xvs
--   test f d t = error $ show t

-- process4 sz f vs cts (xa,ta) (xb,tb) (xc,tc) (xd,td) to = go vs 0
--   where
--     go []       !n = return $ Passed n
--     go (vs:vss) !n =
--       do when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
--          setValues vs
--          d <- stitch sz td
--          c <- stitch sz tc
--          b <- stitch sz tb
--          a <- stitch sz ta
--          --io $ print (a,b,c,d)
--          er <- io $ try $ evaluate (f a b c d)
--          case er of
--            Left (e::SomeException) -> return $ Failed $ show (a, b, c, d)
--            Right r -> do
--              let env = map (second (`app` [])) cts
--                     ++ [(xa, toExpr a),(xb, toExpr b),(xc, toExpr c),(xd, toExpr d)]
--              sat <- evalType (M.fromList env) to (toExpr r)
--              case sat of
--                False -> return $ Failed $ show (a, b, c, d)
--                True  -> go vss (n+1) -- return $ Passed (n+1))
