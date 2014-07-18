{-# LANGUAGE DeriveGeneric #-}
module Expr where

import Data.Set (Set, (\\))
import qualified Data.Set as Set
import GHC.Generics

import Test.LiquidCheck


data Expr = Var Int
          | Lam Int Expr
          | App Expr Expr
          deriving (Generic, Show)

{-@ measure freeVars :: Expr -> (Set Int)
    freeVars (Var i)   = (Set_sng i)
    freeVars (Lam i e) = (Set_dif (freeVars e) (Set_sng i))
    freeVars (App x y) = (Set_cup (freeVars x) (freeVars y))
  @-}

{-@ data Expr = Var (x1 :: Nat)
              | Lam (x2 :: Nat) (x3 :: Expr)
              | App (x4 :: Expr) (x5 :: Expr)
  @-}

{-@ type Closed = {v:Expr | (Set_emp (freeVars v))} @-}

instance Constrain Expr

{-@ measure prop :: Bool -> Prop
    prop (True)  = true
    prop (False) = false
  @-}
{-@ type Valid = {v:Bool | (prop v)} @-}

freeVars (Var i)   = Set.singleton i
freeVars (Lam i e) = freeVars e \\ Set.singleton i
freeVars (App x y) = freeVars x `Set.union` freeVars y

{-@ inv :: Closed -> Valid @-}
inv e = freeVars e == Set.empty

tests = testModule "examples/Expr.hs" [ liquidCheck inv "Expr.inv" 3 ]
