{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.Target.Eval where

import           Control.Applicative
import           Control.Monad.Catch
import           Control.Monad.State
import           Data.Bifunctor
import qualified Data.HashMap.Strict             as M
import           Data.List
import           Data.Maybe
import           Text.Printf

import           GHC
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types         hiding (R)
import           Language.Haskell.Liquid.RefType (addTyConInfo)
import           Language.Haskell.Liquid.Types   hiding (var)

import           Test.Target.Expr
import           Test.Target.Monad
import           Test.Target.Types
import           Test.Target.Util

-- import           Debug.Trace

evalType :: M.HashMap Symbol Expr -> SpecType -> Expr -> Gen Bool
evalType m t e@(EApp c xs)
  = do dcp <- lookupCtor (val c)
       tyi <- gets tyconInfo
       vts <- freshen $ applyPreds (addTyConInfo M.empty tyi t) dcp
       liftM2 (&&) (evalReft m (toReft $ rt_reft t) e) (evalTypes m vts xs)
evalType m t e
  = evalReft m (toReft $ rt_reft t) e

freshen :: [(Symbol, SpecType)] -> Gen [(Symbol, SpecType)]
freshen [] = return []
freshen ((v,t):vts)
  = do n <- freshInt
       let v' = symbol . (++show n) . symbolString $ v
           su = mkSubst [(v,var v')]
           t' = subst su t
       vts' <- freshen $ subst su vts
       return ((v',t'):vts')

evalTypes
  :: M.HashMap Symbol Expr
     -> [(Symbol, SpecType)] -> [Expr] -> Gen Bool
evalTypes _ []         []     = return True
evalTypes m ((v,t):ts) (x:xs)
  = liftM2 (&&) (evalType m' t x) (evalTypes m' ts xs)
  where
    m' = M.insert v x m

eval :: Expr -> Reft -> Gen Bool
eval e r = do
  cts <- gets freesyms
  evalReft (M.fromList $ map (second (`app` [])) cts) r e

evalReft :: M.HashMap Symbol Expr -> Reft -> Expr -> Gen Bool
evalReft m (Reft (v, rs)) x
  = and <$> sequence [ evalPred p (M.insert v x m) | RConc p <- rs ]

evalPred :: Pred -> M.HashMap Symbol Expr -> Gen Bool
evalPred PTrue           _ = return True
evalPred PFalse          _ = return False
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
evalPred p               _ = throwM $ EvalError $ "evalPred: " ++ show p
-- evalPred (PAll ss p)     m = undefined
-- evalPred PTop            m = undefined

evalBrel :: Brel -> Expr -> Expr -> Bool
evalBrel Eq = (==)
evalBrel Ne = (/=)
evalBrel Gt = (>)
evalBrel Ge = (>=)
evalBrel Lt = (<)
evalBrel Le = (<=)

applyMeasure :: Measure SpecType DataCon -> Expr -> M.HashMap Symbol Expr -> Gen Expr
applyMeasure m (EApp c xs) env
  = meq >>= \eq -> evalBody eq xs env
  where
    ct = symbolString $ case val c of
      "GHC.Types.[]" -> "[]"
      "GHC.Types.:"  -> ":"
      "GHC.Tuple.(,)" -> "(,)"
      "GHC.Tuple.(,,)" -> "(,,)"
      "GHC.Tuple.(,,,)" -> "(,,,)"
      "GHC.Tuple.(,,,,)" -> "(,,,,)"
      x -> x
    meq = case find ((==ct) . show . ctor) $ eqns m of
           Nothing -> throwM $ EvalError $ printf "applyMeasure(%s): no equation for %s" (show m) (show ct)
           Just x -> return x

applyMeasure m e           _
  = throwM $ EvalError $ printf "applyMeasure(%s, %s)" (showpp m) (showpp e)

setSym :: Symbol
setSym = "LC_SET"

nubSort :: [Expr] -> [Expr]
nubSort = nub . Data.List.sort

mkSet :: [Expr] -> Expr
mkSet = app setSym . nubSort

evalSet :: Symbol -> [Expr] -> Gen Expr
evalSet "Set_emp" [e]
  = return $ if e == app setSym [] then 0 else 1
evalSet "Set_sng" [e]
  = return $ mkSet [e]
evalSet "Set_add" [e1, EApp _ e2]
  = return $ mkSet $ e1:e2
evalSet "Set_cap" [EApp _ e1, EApp _ e2]
  = return $ mkSet $ intersect e1 e2
evalSet "Set_cup" [EApp _ e1, EApp _ e2]
  = return $ mkSet $ e1 ++ e2
evalSet "Set_dif" [EApp _ e1, EApp _ e2]
  = return $ mkSet $ e1 \\ e2
evalSet "Set_sub" [EApp _ e1, EApp _ e2]
  = return $ if null (e1 \\ e2) then 0 else 1
evalSet "Set_mem" [e1, EApp f e2] | val f == setSym
  = return $ if e1 `elem` e2 then 0 else 1
evalSet f es = throwM $ EvalError $ printf "evalSet(%s, %s)" (show f) (show es)

evalBody
  :: Language.Haskell.Liquid.Types.Def ctor
     -> [Expr] -> M.HashMap Symbol Expr -> Gen Expr
evalBody eq xs env = go $ body eq
  where
    go (E e) = evalExpr (subst su e) env
    go (P p) = evalPred (subst su p) env >>= \b -> return $ if b then 0 else 1
    go (R v p) = do e <- evalRel v (subst su p) env
                    case e of
                      Nothing -> throwM $ EvalError $ "evalBody can't handle: " ++ show (R v p)
                      Just e  -> return e
    --go (R v (PBexp (EApp f e))) | val f == "Set_emp" = return $ app setSym []
    ----FIXME: figure out how to handle the general case..
    --go (R v p) = return (ECon (I 0))
    su = mkSubst $ zip (binds eq) xs

evalRel :: Symbol -> Pred -> M.HashMap Symbol Expr -> Gen (Maybe Expr)
evalRel v (PAnd ps)       m = Just . head . catMaybes <$> sequence [evalRel v p m | p <- ps]
evalRel v (PImp p q)      m = do pv <- evalPred p m
                                 if pv
                                    then evalRel v q m
                                    else return Nothing
evalRel v (PAtom Eq (EVar v') e2) m
  | v == v'
  = Just <$> evalExpr e2 m
evalRel v (PBexp (EApp f [EVar v'])) _
  | v == v' && val f == "Set_emp"
  = return $ Just $ app setSym []
evalRel _ p               _
  = throwM $ EvalError $ "evalRel: " ++ show p

evalExpr :: Expr -> M.HashMap Symbol Expr -> Gen Expr
evalExpr (ECon i)       _ = return $ ECon i
evalExpr (EVar x)       m = return $ m M.! x
evalExpr (ESym s)       _ = return $ ESym s
evalExpr (EBin b e1 e2) m = evalBop b <$> evalExpr e1 m <*> evalExpr e2 m
evalExpr (EApp f es)    m
  | val f == "Set_emp" || val f == "Set_sng" || val f `M.member` smt_set_funs
  = mapM (`evalExpr` m) es >>= \es' -> evalSet (val f) es'
  | otherwise
  = find ((==f) . name) <$> gets measEnv >>= \case
      Nothing -> EApp f <$> mapM (`evalExpr` m) es
                    --FIXME: should really extend this to multi-param measures..
      Just ms -> do e' <- evalExpr (head es) m
                    applyMeasure ms e' m
evalExpr (EIte p e1 e2) m
  = do b <- evalPred p m
       if b
         then evalExpr e1 m
         else evalExpr e2 m
evalExpr e              _ = throwM $ EvalError $ printf "evalExpr(%s)" (show e)

evalBop :: Bop -> Expr -> Expr -> Expr
evalBop Plus  (ECon (I x)) (ECon (I y)) = ECon . I $ x + y
evalBop Minus (ECon (I x)) (ECon (I y)) = ECon . I $ x - y
evalBop Times (ECon (I x)) (ECon (I y)) = ECon . I $ x * y
evalBop Div   (ECon (I x)) (ECon (I y)) = ECon . I $ x `div` y
evalBop Mod   (ECon (I x)) (ECon (I y)) = ECon . I $ x `mod` y
evalBop b     e1           e2           = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)
