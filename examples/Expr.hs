{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--idirs=../src" @-}
module Expr where

import Data.Set (Set, (\\))
import qualified Data.Set as Set
import GHC.Generics

import Test.LiquidCheck
import Test.LiquidCheck.Eval (setSym)
import Test.LiquidCheck.Expr (app)

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import Data.Monoid
import Data.Proxy
import Test.LiquidCheck
import Test.LiquidCheck.Gen (GenState(..))
import Test.LiquidCheck.Util
import Language.Fixpoint.Types (Sort(..))
import Language.Haskell.Liquid.PredType
import Language.Haskell.Liquid.Types (RType(..))
import BasicTypes (TupleSort(..))
import TysWiredIn (listTyCon, tupleTyCon)

data Expr = Var Int
          | Lam Int Expr
          | App Expr Expr
          deriving (Generic, Show)

{-@ measure freeVars :: Expr -> (Set Int)
    freeVars (Var v)   = (Set_sng v)
    freeVars (Lam v e) = (Set_dif (freeVars e) (Set_sng v))
    freeVars (App x y) = (Set_cup (freeVars x) (freeVars y))
  @-}

{-@ measure isLam :: Expr -> Prop
    isLam (Var v)   = false
    isLam (Lam v e) = true
    isLam (App x y) = false
  @-}

{-@ data Expr <p :: Int -> Prop> = Var (x1 :: Nat)
              | Lam (x2 :: Nat<p>) (x3 :: Expr<{\i -> true}>)
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
inv e = freeVars e == Set.empty

{-@ subst :: e1:Closed -> n:Nat -> e2:Closed
          -> {v:Closed | (if (Set_mem n (freeVars e2))
                          then (freeVars v) = (Set_cup (Set_dif (freeVars e2)
                                                                (Set_sng n))
                                                       (freeVars e1))
                          else (freeVars v) = (freeVars e2))}
  @-}
subst :: Expr -> Int -> Expr -> Expr
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

{-@ fresh :: n:Nat -> ns:Set Nat -> {v:Nat | not (v == n || (Set_mem v ns))} @-}
fresh :: Int -> Set Int -> Int
fresh v vs = 1 + Set.findMax (Set.insert v vs)

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
