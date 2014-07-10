{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Test.LiquidCheck.Eval where

import           Control.Applicative
import           Control.Monad.State
import           Data.Function
import qualified Data.HashMap.Strict             as M
import           Data.List
import           Text.Printf

import           GHC
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types         hiding (R)
import           Language.Haskell.Liquid.Measure
import           Language.Haskell.Liquid.RefType (expandRApp)
import           Language.Haskell.Liquid.Types   hiding (var)

import           Test.LiquidCheck.Constrain
import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Util


-- evalType :: Env -> RApp -> Expr -> Gen Bool
evalType :: M.HashMap Symbol Expr -> SpecType -> Expr -> Gen Bool
evalType m t e@(EApp c xs)
  = do dcp <- (safeFromJust "evalType" . lookup (val c))
              <$> gets ctorEnv
       tyi <- gets tyconInfo
       vts <- freshen $ applyPreds (expandRApp M.empty tyi t) dcp
       liftM2 (&&) (evalReft m (toReft $ rt_reft t) e) (evalTypes m vts xs)
evalType m t e
  = evalReft m (toReft $ rt_reft t) e

freshen [] = return []
freshen ((v,t):vts)
  = do n <- gets seed
       modify $ \s@ (GS {..}) -> s { seed = seed + 1 }
       let v' = symbol . (++show n) . symbolString $ v
           su = mkSubst [(v,var v')]
           t' = subst su t
       vts' <- freshen $ subst su vts
       return ((v',t'):vts')

evalTypes m []         []     = return True
evalTypes m ((v,t):ts) (x:xs)
  = liftM2 (&&) (evalType m' t x) (evalTypes m' ts xs)
  where
    m' = M.insert v x m


evalReft :: M.HashMap Symbol Expr -> Reft -> Expr -> Gen Bool
evalReft m r@(Reft (v, rs)) x
  = and <$> sequence [ evalPred p (M.insert v x m) | RConc p <- rs ]

evalPred PTrue           m = return True
evalPred PFalse          m = return False
evalPred (PAnd ps)       m = and <$> sequence [evalPred p m | p <- ps]
evalPred (POr ps)        m = or  <$> sequence [evalPred p m | p <- ps]
evalPred (PNot p)        m = not <$> evalPred p m
evalPred (PImp p q)      m = do pv <- evalPred p m
                                if pv
                                   then evalPred q m
                                   else return True
evalPred (PIff p q)      m = and <$> sequence [ evalPred (p `imp` q) m
                                              , evalPred (q `imp` p) m
                                              ]
evalPred (PAtom b e1 e2) m = evalBrel b <$> evalExpr e1 m <*> evalExpr e2 m
evalPred (PBexp e)       m = (==0) <$> evalExpr e m
evalPred p               m = error $ "evalPred: " ++ show p
-- evalPred (PBexp e)       m = undefined -- ofExpr e
-- evalPred (PAll ss p)     m = undefined
-- evalPred PTop            m = undefined

evalBrel Eq = (==)
evalBrel Ne = (/=)
evalBrel Gt = (>)
evalBrel Ge = (>=)
evalBrel Lt = (<)
evalBrel Le = (<=)

applyMeasure :: Measure SpecType DataCon -> Expr -> M.HashMap Symbol Expr -> Gen Expr
applyMeasure m (EApp c xs) env = evalBody eq xs env
  where
    ct = case symbolString $ val c of
      "GHC.Types.[]" -> "[]"
      "GHC.Types.:"  -> ":"
      c -> c
    eq = safeFromJust ("applyMeasure: " ++ ct)
       $ find ((==ct) . show . ctor) $ eqns m
applyMeasure m e           env = error $ printf "applyMeasure(%s, %s)" (showpp m) (showpp e)

setSym :: Symbol
setSym = "LC_SET"

nubSort = nub . Data.List.sort

mkSet = app setSym . nubSort

evalSet "Set_emp" [e] env
  = return $ if e == app setSym [] then 0 else 1
evalSet "Set_sng" [e] env
  = return $ mkSet [e]
evalSet "Set_add" [e1, EApp _ e2] env
  = return $ mkSet $ e1:e2
evalSet "Set_cap" [EApp _ e1, EApp _ e2] env
  = return $ mkSet $ intersect e1 e2
evalSet "Set_cup" [EApp _ e1, EApp _ e2] env
  = return $ mkSet $ e1 ++ e2
evalSet "Set_dif" [EApp _ e1, EApp _ e2] env
  = return $ mkSet $ e1 \\ e2
evalSet "Set_sub" [EApp _ e1, EApp _ e2] env
  = return $ if e1 \\ e2 == [] then 0 else 1

evalBody eq xs env = go $ body eq
  where
    go (E e) = evalExpr (subst su e) env
    go (P p) = evalPred (subst su p) env >>= \b -> return $ if b then 0 else 1
    go (R v (PBexp (EApp f e))) | val f == "Set_emp" = return $ app setSym []
    su = mkSubst $ zip (binds eq) xs


evalExpr :: Expr -> M.HashMap Symbol Expr -> Gen Expr
evalExpr (ECon i)       m = return $ ECon i
evalExpr (EVar x)       m = return $ m M.! x
evalExpr (ESym s)       m = return $ ESym s
evalExpr (EBin b e1 e2) m = evalBop b <$> evalExpr e1 m <*> evalExpr e2 m
evalExpr (EApp f es)    m
  | val f == "Set_emp" || val f == "Set_sng" || val f `M.member` smt_set_funs
  = mapM (`evalExpr` m) es >>= \es' -> evalSet (val f) es' m
  | otherwise
  = do ms <- find ((==f) . name) <$> gets measEnv
       case ms of
         Nothing -> EApp f <$> mapM (`evalExpr` m) es
         Just ms -> do e' <- evalExpr (head es) m
                       --io $ print $ M.toList smt_set_funs
                       applyMeasure ms e' m
evalExpr (EIte p e1 e2) m
  = do b <- evalPred p m
       if b
         then evalExpr e1 m
         else evalExpr e2 m
evalExpr e              m = error $ printf "evalExpr(%s)" (show e)

evalBop Plus  (ECon (I x)) (ECon (I y)) = ECon . I $ x + y
evalBop Minus (ECon (I x)) (ECon (I y)) = ECon . I $ x - y
evalBop Times (ECon (I x)) (ECon (I y)) = ECon . I $ x * y
evalBop Div   (ECon (I x)) (ECon (I y)) = ECon . I $ x `div` y
evalBop Mod   (ECon (I x)) (ECon (I y)) = ECon . I $ x `mod` y
evalBop b     e1           e2           = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)
