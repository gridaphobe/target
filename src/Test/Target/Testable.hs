{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ParallelListComp     #-}
{-# LANGUAGE ViewPatterns         #-}
module Test.Target.Testable where

import           Control.Applicative
import           Control.Arrow              hiding (app)
import           Control.Exception          (AsyncException, evaluate)
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.State
import qualified Data.HashMap.Strict        as M
import qualified Data.HashSet               as S
import           Data.Proxy
import qualified Data.Text                  as T
import           Data.Text.Format           hiding (print)
import qualified Data.Text.Lazy             as LT
import qualified Data.Vector                     as V
import           Text.Printf

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types hiding (Result (..), env, var)

import           Test.Target.Targetable hiding (apply)
-- import           Test.Target.Driver
import           Test.Target.Eval
import           Test.Target.Expr
import           Test.Target.Gen
import           Test.Target.Types
import           Test.Target.Util

import Debug.Trace

type CanTest f = (Testable f, Show (Args f), Targetable (Res f))

test :: CanTest f => f -> Int -> SpecType -> Gen Result
test f d t
  = do vs <- genArgs f d t
       setup
       cts <- gets freesyms
       -- vals <- allSat $ map symbol vs
       vars <- gets variables
       let interps = [FInt, boolsort, choicesort]
       let real = [v | (v,t) <- vars, t `elem` interps]
       let (xs, tis, to) = bkArrowDeep $ stripQuals t
       -- let su = mkSubst [(x, var v) | (v,_) <- vs | x <- xs]
       -- let to' = subst su to
       -- let to' = to
       -- traceShowM to'
       ctx <- gets smtContext
       try (process d f ctx vs real cts (zip xs tis) to) >>= \case
         Left  (e :: TargetException) -> return $ Errored $ show e
         Right r                      -> return r

process :: CanTest f
        => Int -> f -> Context -> [Variable] -> [Symbol] -> [(Symbol,Symbol)] -> [(Symbol,SpecType)] -> SpecType
        -> Gen Result
process d f ctx vs real cts xts to = go 0 =<< io (command ctx CheckSat)
  where
    go !n Unsat    = return $ Passed n
    go _  (Error e)= throwM $ SmtError $ T.unpack e
    go !n Sat      = do
      when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
      let n' = n + 1
      xs <- decodeArgs f (map fst vs) (map snd xts)
      whenVerbose $ io $ print xs
      er <- io $ try $ evaluate (apply f xs)
      whenVerbose $ io $ print er
      case er of
        Left (e :: SomeException)
          -- DON'T catch AsyncExceptions since they are used by @timeout@
          | Just (e :: AsyncException) <- fromException e -> throwM e
          | Just e@(SmtError _) <- fromException e -> throwM e
          | Just e@(ExpectedValues _) <- fromException e -> throwM e
          | otherwise -> mbKeepGoing xs n
        Right r -> do
          real <- gets realized
          modify $ \s@(GS {..}) -> s { realized = [] }
          io $ command ctx $ Assert Nothing $ PNot $ pAnd
            [ var x `eq` ESym (SL v) | (x,v) <- real ]
          -- sat <- check r to
          let env = map (second (`app` [])) cts ++ mkExprs f (map fst xts) xs
          sat <- evalType (M.fromList env) to (toExpr r)
          case sat of
            False -> mbKeepGoing xs n'
            True -> do
              max <- gets maxSuccess
              case max of
                Nothing -> go n' =<< io (command ctx CheckSat)
                Just m | m == n' -> return $ Passed m
                       | otherwise -> go n' =<< io (command ctx CheckSat)
    mbKeepGoing xs n = do
      kg <- gets keepGoing
      if kg
        then go n =<< io (command ctx CheckSat)
        else return (Failed $ show xs)

class Testable f where
  genArgs    :: f -> Int -> SpecType -> Gen [Variable]
  -- stitchArgs :: f -> Int -> [SpecType] -> Gen (Args f)
  decodeArgs :: f -> [Symbol] -> [SpecType] -> Gen (Args f)
  apply      :: f -> Args f -> Res f
  mkExprs    :: f -> [Symbol] -> Args f -> [(Symbol,Expr)]

instance ( Targetable a, Targetable b
         , Args (a -> b) ~ a
         , Res (a -> b) ~ b)
  => Testable (a -> b) where
  genArgs _ d (stripQuals -> (RFun x i o _))
    = (:[]) <$> gen (Proxy :: Proxy a) d i
  -- stitchArgs _ d [t]
  --   = stitch d t
  decodeArgs _ [v] [t]
    = decode v t
  apply f a
    = f a
  mkExprs _ [x] a
    = [(x,toExpr a)]

instance ( Targetable a, Targetable b, Targetable c
         , Args (a -> b -> c) ~ (a,b)
         , Res (a -> b -> c) ~ c)
  => Testable (a -> b -> c) where
  genArgs _ d (stripQuals -> (RFun xa ta (RFun xb tb to _) _))
    = do a <- gen (Proxy :: Proxy a) d ta
         let tb' = subst (mkSubst [(xa, var a)]) tb
         b <- gen (Proxy :: Proxy b) d tb'
         return [a,b]
  -- stitchArgs _ d [ta,tb]
  --   = do b <- stitch d tb
  --        a <- stitch d ta
  --        return (a,b)
  decodeArgs _ [va,vb] [ta,tb]
    = do a <- decode va ta
         b <- decode vb tb
         return (a,b)
  apply f (a,b)
    = f a b
  mkExprs _ [xa,xb] (a,b)
    = [(xa,toExpr a), (xb,toExpr b)]

instance ( Targetable a, Targetable b, Targetable c, Targetable d
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
  -- stitchArgs _ d [ta,tb,tc]
  --   = do c <- stitch d tc
  --        b <- stitch d tb
  --        a <- stitch d ta
  --        return (a,b,c)
  decodeArgs _ [va,vb,vc] [ta,tb,tc]
    = do a <- decode va ta
         b <- decode vb tb
         c <- decode vc tc
         return (a,b,c)
  apply f (a,b,c)
    = f a b c
  mkExprs _ [xa,xb,xc] (a,b,c)
    = [(xa,toExpr a), (xb,toExpr b), (xc,toExpr c)]

instance ( Targetable a, Targetable b, Targetable c, Targetable d, Targetable e
         , Args (a -> b -> c -> d -> e) ~ (a,b,c,d)
         , Res (a -> b -> c -> d -> e) ~ e)
  => Testable (a -> b -> c -> d -> e) where
  genArgs _ sz (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc (RFun xd td to _) _) _) _))
    = do a <- gen (Proxy :: Proxy a) sz ta
         let tb' = subst (mkSubst [(xa, var a)]) tb
         b <- gen (Proxy :: Proxy b) sz tb'
         let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
         c <- gen (Proxy :: Proxy c) sz tc'
         let td' = subst (mkSubst [(xa, var a), (xb, var b), (xc, var c)]) td
         d <- gen (Proxy :: Proxy d) sz td'
         return [a,b,c,d]
  -- stitchArgs _ sz [ta,tb,tc,td]
  --   = do d <- stitch sz td
  --        c <- stitch sz tc
  --        b <- stitch sz tb
  --        a <- stitch sz ta
  --        return (a,b,c,d)
  decodeArgs _ [va,vb,vc,vd] [ta,tb,tc,td]
    = do a <- decode va ta
         b <- decode vb tb
         c <- decode vc tc
         d <- decode vd td
         return (a,b,c,d)
  apply f (a,b,c,d)
    = f a b c d
  mkExprs _ [xa,xb,xc,xd] (a,b,c,d)
    = [(xa,toExpr a), (xb,toExpr b), (xc,toExpr c), (xd,toExpr d)]

instance ( Targetable a, Targetable b, Targetable c, Targetable d, Targetable e, Targetable f
         , Args (a -> b -> c -> d -> e -> f) ~ (a,b,c,d,e)
         , Res (a -> b -> c -> d -> e -> f) ~ f)
  => Testable (a -> b -> c -> d -> e -> f) where
  genArgs _ sz (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc (RFun xd td (RFun xe te to _) _) _) _) _))
    = do a <- gen (Proxy :: Proxy a) sz ta
         let tb' = subst (mkSubst [(xa, var a)]) tb
         b <- gen (Proxy :: Proxy b) sz tb'
         let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
         c <- gen (Proxy :: Proxy c) sz tc'
         let td' = subst (mkSubst [(xa, var a), (xb, var b), (xc, var c)]) td
         d <- gen (Proxy :: Proxy d) sz td'
         let te' = subst (mkSubst [(xa, var a), (xb, var b), (xc, var c), (xd, var d)]) te
         e <- gen (Proxy :: Proxy e) sz te'
         return [a,b,c,d,e]
  -- stitchArgs _ sz [ta,tb,tc,td,te]
  --   = do e <- stitch sz te
  --        d <- stitch sz td
  --        c <- stitch sz tc
  --        b <- stitch sz tb
  --        a <- stitch sz ta
  --        return (a,b,c,d,e)
  decodeArgs _ [va,vb,vc,vd,ve] [ta,tb,tc,td,te]
    = do a <- decode va ta
         b <- decode vb tb
         c <- decode vc tc
         d <- decode vd td
         e <- decode ve te
         return (a,b,c,d,e)
  apply f (a,b,c,d,e)
    = f a b c d e
  mkExprs _ [xa,xb,xc,xd,xe] (a,b,c,d,e)
    = [(xa,toExpr a), (xb,toExpr b), (xc,toExpr c), (xd,toExpr d), (xe,toExpr e)]


-- check :: Targetable a => a -> SpecType -> Gen Bool
-- check v t = do
--   state' <- get
--   let state = state' { variables = [], choices = [], constraints = []
--                      , deps = [], constructors = [] }
--   put state
--   ctx <- gets smtContext
--   io $ command ctx Push

--   void $ encode v t
--   vs <- gets variables
--   mapM_ (\x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
--   cs <- gets constraints
--   mapM_ (\c -> io . command ctx $ Assert Nothing c) cs
--   resp <- io $ command ctx CheckSat

--   io $ command ctx Pop
--   put state'
--   return (resp == Sat)
  

makeDecl :: Symbol -> Sort -> Command
-- FIXME: hack..
makeDecl x _ | x `M.member` smt_set_funs = Assert Nothing PTrue
makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

func (FFunc _ _) = True
func _           = False

setup :: Gen ()
setup = {-# SCC "setup" #-} do
   ctx <- gets smtContext
   emb <- gets embEnv
   -- declare sorts
   ss  <- S.toList <$> gets sorts
   let defSort b e = io $ smtWrite ctx (format "(define-sort {} () {})" (b,e))
   -- FIXME: combine this with the code in `fresh`
   forM_ ss $ \case
     FObj "Int" -> return ()
     FInt       -> return ()
     FObj "GHC.Types.Bool"   -> defSort ("GHC.Types.Bool" :: T.Text) ("Bool" :: T.Text)
     FObj "CHOICE" -> defSort ("CHOICE" :: T.Text) ("Bool" :: T.Text)
     s        -> defSort (LT.toStrict $ smt2 s) ("Int" :: T.Text)
   -- declare constructors
   cts <- gets constructors
   mapM_ (\ (c,t) -> io . command ctx $ makeDecl (symbol c) t) cts
   let nullary = [var c | (c,t) <- cts, not (func t)]
   unless (null nullary) $
     void $ io $ command ctx $ Distinct nullary
   -- declare variables
   vs <- gets variables
   mapM_ (\ x -> io . command ctx $ Declare (symbol x) [] (arrowize $ snd x)) vs
   -- declare measures
   ms <- gets measEnv
   mapM_ (\m -> io . command ctx $ makeDecl (val $ name m) (rTypeSort emb $ sort m)) ms
   -- assert constraints
   cs <- gets constraints
   --mapM_ (\c -> do {i <- gets seed; modify $ \s@(GS {..}) -> s { seed = seed + 1 };
   --                 io . command ctx $ Assert (Just i) c})
   --  cs
   mapM_ (\c -> io . command ctx $ Assert Nothing c) cs
   -- deps <- V.fromList . map (symbol *** symbol) <$> gets deps
   -- io $ generateDepGraph "deps" deps cs
   -- return (ctx,vs,deps)
