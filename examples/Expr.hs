{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-@ LIQUID "--idirs=../src" @-}
module Expr where

import           Data.Set                         (Set, (\\))
import qualified Data.Set                         as Set
import           GHC.Generics

import           Test.LiquidCheck
import           Test.LiquidCheck.Eval            (setSym)
import           Test.LiquidCheck.Expr            (app)

import           BasicTypes                       (TupleSort (..))
import           Control.Applicative
import           Control.Monad.State
import qualified Data.HashMap.Strict              as HM
import qualified Data.Map                         as M
import           Data.Monoid
import           Data.Proxy
import           Language.Fixpoint.Types          (Sort (..))
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.Types    (RType (..))
import           Test.LiquidCheck
import           Test.LiquidCheck.Gen             (GenState (..))
import           Test.LiquidCheck.Util
import           TysWiredIn                       (listTyCon, tupleTyCon)

data Expr = Var Char
          | Lam Char Expr
          | App Expr Expr
          deriving (Generic, Show)

hasDepth d (Var c)   = d == 1
hasDepth d (Lam c e) = hasDepth (d-1) e
hasDepth d (App f e) = hasDepth (d-1) f || hasDepth (d-1) e

{-@ measure freeVars :: Expr -> (Set Char)
    freeVars (Var v)   = (Set_sng v)
    freeVars (Lam v e) = (Set_dif (freeVars e) (Set_sng v))
    freeVars (App x y) = (Set_cup (freeVars x) (freeVars y))
  @-}

{-@ measure isLam :: Expr -> Prop
    isLam (Var v)   = false
    isLam (Lam v e) = true
    isLam (App x y) = false
  @-}

{-@ data Expr = Var (x1 :: Char)
              | Lam (x2 :: Char) (x3 :: Expr)
              | App (x4 :: Expr) (x5 :: Expr)
  @-}

{-@ type Closed = {v:Expr | (Set_emp (freeVars v))} @-}

instance Constrain Expr

{-@ measure prop :: Bool -> Prop
    prop (True)  = true
    prop (False) = false
  @-}
{-@ type Valid = {v:Bool | (prop v)} @-}

freeVars (Var v)   = Set.singleton v
freeVars (Lam v e) = freeVars e \\ Set.singleton v
freeVars (App x y) = freeVars x `Set.union` freeVars y

{-@ inv :: Closed -> Valid @-}
inv e = Set.null $ freeVars e 

closed = inv

{-@ subst :: e1:Closed -> n:Char -> e2:Closed
          -> {v:Closed | (if (Set_mem n (freeVars e2))
                          then (freeVars v) = (Set_cup (Set_dif (freeVars e2)
                                                                (Set_sng n))
                                                       (freeVars e1))
                          else (freeVars v) = (freeVars e2))}
  @-}
subst :: Expr -> Char -> Expr -> Expr
subst e1 v e2@(Var v')
  = if v == v' then e1 else e2
subst e1 v e2@(Lam v' e')
  | v == v'            = e2 -- I can't read.. :P -- subst e1 v (freshen e2) -- BUGGY in ICFP14 paper: e1
  | v `Set.member` fvs = subst e1 v (freshen e2)
  | otherwise          = Lam v' (subst e1 v e')
  where
    fvs = freeVars e1
subst e v (App e1 e2)
  = App e1' e2'
  where
    e1' = subst e v e1
    e2' = subst e v e2

{-@ freshen :: e:{Expr | (isLam e)} -> {v:Expr | (freeVars v) = (freeVars e)} @-}
freshen (Lam v e) = Lam v' (subst (Var v') v e)
  where
    v' = fresh v (freeVars e)

{-@ fresh :: n:Char -> ns:Set Char -> {v:Char | not (v == n || (Set_mem v ns))} @-}
fresh :: Char -> Set Char -> Char
fresh v vs = succ $ Set.findMax (Set.insert v vs)

instance (Ord a, Constrain a) => Constrain (Set a) where
  getType _ = FObj "Data.Set.Base.Set"
  gen p d (RApp c ts ps r)
    = do tyi <- gets tyconInfo
         let listRTyCon  = tyi HM.! listTyCon
         gen (Proxy :: Proxy [a]) d (RApp listRTyCon ts [] mempty)
  stitch  d t = stitch d t >>= \(xs :: [a]) -> return $ Set.fromList xs
  toExpr  s = app setSym [toExpr x | x <- Set.toList s]

liquidTests :: [(String, Test)]
liquidTests = [ ("inv",     T inv)
              , ("freshen", T freshen)
              , ("fresh",   T fresh)
              , ("subst",   T subst)]
