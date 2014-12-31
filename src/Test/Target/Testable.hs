{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
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
{-# LANGUAGE ViewPatterns         #-}
module Test.Target.Testable where

import           Control.Applicative
import           Control.Exception               (AsyncException, evaluate)
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.HashMap.Strict             as M
import qualified Data.HashSet                    as S
import           Data.Proxy
import qualified Data.Text                       as T
import           Data.Text.Format                hiding (print)
import qualified Data.Text.Lazy                  as LT
import           Text.Printf

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types   hiding (Result (..), env, var)

import           Test.Target.Targetable          hiding (apply)
-- import           Test.Target.Eval
import           Test.Target.Expr
import           Test.Target.Monad
import           Test.Target.Types
import           Test.Target.Util

-- import Debug.Trace

type CanTest f = (Testable f, AllHave Show (Args f), Targetable (Res f))

test :: CanTest f => f -> Int -> SpecType -> Target Result
test f d t
  = do vs <- queryArgs f d t
       setup
       let (xs, tis, to) = bkArrowDeep $ stripQuals t
       ctx <- gets smtContext
       try (process f ctx vs (zip xs tis) to) >>= \case
         Left  (e :: TargetException) -> return $ Errored $ show e
         Right r                      -> return r

process :: CanTest f
        => f -> Context -> [Symbol] -> [(Symbol,SpecType)] -> SpecType
        -> Target Result
process f ctx vs xts to = go 0 =<< io (command ctx CheckSat)
  where
    go !n Unsat    = return $ Passed n
    go _  (Error e)= throwM $ SmtError $ T.unpack e
    go !n Sat      = do
      when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
      let n' = n + 1
      xs <- decodeArgs f vs (map snd xts)
      whenVerbose $ io $ print xs
      er <- io $ try $ evaluate (apply f xs)
      -- whenVerbose $ io $ print er
      case er of
        Left (e :: SomeException)
          -- DON'T catch AsyncExceptions since they are used by @timeout@
          | Just (_ :: AsyncException) <- fromException e -> throwM e
          | Just (SmtError _) <- fromException e -> throwM e
          | Just (ExpectedValues _) <- fromException e -> throwM e
          | otherwise -> mbKeepGoing xs n
        Right r -> do
          real <- gets realized
          modify $ \s@(TargetState {..}) -> s { realized = [] }
          let su = mkSubst $ mkExprs f (map fst xts) xs
          (sat, _) <- check r (subst su to)

          -- refute model *after* checking output in case we have HOFs, which
          -- need to query the solver. if this is the last set of inputs, e.g.
          -- refuting the current model forces the solver to return unsat next
          -- time, the solver will return unsat when the HOF queries for an output,
          -- causing us to return a spurious error
          io $ command ctx $ Assert Nothing $ PNot $ pAnd
            [ ESym (SL $ symbolText x) `eq` ESym (SL v) | (x,v) <- real ]
          -- let env = map (second (`app` [])) cts ++ mkExprs f (map fst xts) xs
          -- sat <- evalType (M.fromList env) to (toExpr r)
          case sat of
            False -> mbKeepGoing xs n'
            True ->
              asks maxSuccess >>= \case
                Nothing -> go n' =<< io (command ctx CheckSat)
                Just m | m == n' -> return $ Passed m
                       | otherwise -> go n' =<< io (command ctx CheckSat)
    mbKeepGoing xs n = do
      kg <- asks keepGoing
      if kg
        then go n =<< io (command ctx CheckSat)
        else return (Failed $ show xs)

class Testable f where
  queryArgs  :: f -> Int -> SpecType -> Target [Symbol]
  decodeArgs :: f -> [Symbol] -> [SpecType] -> Target (HList (Args f))
  apply      :: f -> HList (Args f) -> Res f
  mkExprs    :: f -> [Symbol] -> HList (Args f) -> [(Symbol,Expr)]

instance (Targetable a, Testable b) => Testable (a -> b) where
  queryArgs f d (stripQuals -> (RFun _ i o _))
    = liftM2 (:) (query (Proxy :: Proxy a) d i) (queryArgs (f undefined) d o)
  decodeArgs f (v:vs) (t:ts)
    = liftM2 (:::) (decode v t) (decodeArgs (f undefined) vs ts)
  apply f (x ::: xs)
    = apply (f x) xs
  mkExprs f (v:vs) (x ::: xs)
    = (v, toExpr x) : mkExprs (f undefined) vs xs

instance (Targetable a, Args a ~ '[], Res a ~ a) => Testable a where
  queryArgs _ _ _  = return []
  decodeArgs _ _ _ = return Nil
  apply f Nil      = f
  mkExprs _ _ _    = []


makeDecl :: Symbol -> Sort -> Command
-- FIXME: hack..
makeDecl x _ | x `M.member` smt_set_funs = Assert Nothing PTrue
makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

func :: Sort -> Bool
func (FFunc _ _) = True
func _           = False

setup :: Target ()
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

sortTys :: Sort -> [Sort]
sortTys (FFunc _ ts) = concatMap sortTys ts
sortTys t            = [t]

arrowize :: Sort -> Sort
arrowize = FObj . symbol . LT.intercalate "->" . map (LT.fromStrict . symbolText . unObj) . sortTys

unObj :: Sort -> Symbol
unObj FInt     = "Int"
unObj (FObj s) = s
unObj s        = error $ "unObj: " ++ show s
