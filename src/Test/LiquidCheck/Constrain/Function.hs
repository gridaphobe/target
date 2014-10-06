{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ViewPatterns         #-}
module Test.LiquidCheck.Constrain.Function where

import           Control.Applicative
import           Control.Arrow                   (first, second)
import           Control.Monad
import qualified Control.Monad.Catch             as Ex
import           Control.Monad.State
import           Data.Char
import qualified Data.HashMap.Strict             as M
import           Data.IORef
import           Data.Monoid
import           Data.Proxy
import qualified Data.Text                       as T
import qualified GHC
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types         hiding (ofReft)
import           Language.Haskell.Liquid.GhcMisc (qualifiedNameSymbol)
import           Language.Haskell.Liquid.RefType (rTypeSort)
import           Language.Haskell.Liquid.Tidy    (tidySymbol)
import           Language.Haskell.Liquid.Types   hiding (var)
import           System.IO.Unsafe
import           Text.Printf

import           Test.LiquidCheck.Constrain
import           Test.LiquidCheck.Eval
import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util


getCtors :: SpecType -> [GHC.DataCon]
getCtors (RApp c _ _ _) = GHC.tyConDataCons $ rtc_tc c
getCtors (RAppTy t _ _) = getCtors t
getCtors (RFun _ i o _) = getCtors i ++ getCtors o
getCtors (RVar _ _)     = []
getCtors t              = error $ "getCtors: " ++ showpp t

dataConSymbol_noUnique :: GHC.DataCon -> Symbol
dataConSymbol_noUnique = qualifiedNameSymbol . GHC.getName

genFun p d (stripQuals -> t)
  = do forM_ (getCtors t) $ \dc -> do
         let c = dataConSymbol_noUnique dc
         t <- lookupCtor c
         addConstructor (c, rTypeSort mempty t)
       fresh (getType p)

stitchFun :: forall f. (Constrain (Res f))
          => Proxy f -> Int -> SpecType -> Gen ([Expr] -> Res f)
stitchFun _ d (bkArrowDeep . stripQuals -> (vs, tis, to))
  = do mref <- io $ newIORef []
       state' <- get
       let state = state' { variables = [], choices = [], constraints = []
                          , values = [], deps = [], constructors = [] }
       return $ \es -> unsafePerformIO $ evalGen state $ do
         -- let es = map toExpr xs
         mv <- lookup es <$> io (readIORef mref)
         case mv of
           Just v  -> return v
           Nothing -> do
             cts <- gets freesyms
             let env = map (second (`app` [])) cts
             bs <- zipWithM (\e t -> evalType (M.fromList env) t e) es tis
             case and bs of
               --FIXME: better error message
               False -> Ex.throwM $ PreconditionCheckFailed $ show $ zip es tis
               True  -> do
                 ctx <- gets smtContext
                 io $ command ctx Push
                 xes <- mapM genExpr es
                 let su = mkSubst $ zipWith (\v e -> (v, var e)) vs xes
                 xo <- gen (Proxy :: Proxy (Res f)) d (subst su to)
                 vs <- gets variables
                 mapM_ (\x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
                 cs <- gets constraints
                 mapM_ (\c -> io . command ctx $ Assert Nothing c) cs
                 resp <- io $ command ctx CheckSat
                 when (resp == Unsat) $ Ex.throwM SmtFailedToProduceOutput
                 let real = [symbol v | (v,t) <- vs, t `elem` [FInt, choicesort, boolsort]]
                 Values model <- if null real then return $ Values []
                                 else ensureValues $ io $ command ctx (GetValue real)
                 setValues (map snd model)
                 o  <- stitch d to
                 whenVerbose $ io $ printf "%s -> %s\n" (show es) (show o)
                 io (modifyIORef mref ((es,o):))
                 io $ command ctx Pop
                 return o
    
genExpr :: Expr -> Gen Variable
genExpr (EApp (val -> c) es)
  = do xes <- mapM genExpr es
       (xs, _, to) <- bkArrowDeep . stripQuals <$> lookupCtor c
       let su  = mkSubst $ zip xs $ map (var . fst) xes
           to' = subst su to
       x <- fresh $ FObj $ symbol $ rtc_tc $ rt_tycon to'
       addConstraint $ ofReft x (toReft $ rt_reft to')
       return x
genExpr (ECon (I i))
  = do x <- fresh FInt
       addConstraint $ var x `eq` expr i
       return x
genExpr (ESym (SL s)) | T.length s == 1
  -- This is a Char, so encode it as an Int
  = do x <- fresh FInt
       addConstraint $ var x `eq` expr (ord $ T.head s)
       return x
genExpr e = error $ "genExpr: " ++ show e


instance (Constrain a, Constrain b, b ~ Res (a -> b))
  => Constrain (a -> b) where
  getType _ = FFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)]
  gen = genFun
  stitch d t
    = do f <- stitchFun (Proxy :: Proxy (a -> b)) d t
         return $ \a -> f [toExpr a]
  toExpr  f = var ("FUNCTION" :: Symbol)
  encode _ _ = error "can't encode a function!"

instance (Constrain a, Constrain b, Constrain c, c ~ Res (a -> b -> c))
  => Constrain (a -> b -> c) where
  getType _ = FFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)
                      ,getType (Proxy :: Proxy c)]
  gen = genFun
  stitch d t
    = do f <- stitchFun (Proxy :: Proxy (a -> b -> c)) d t
         return $ \a b -> f [toExpr a, toExpr b]
  toExpr  f = var ("FUNCTION" :: Symbol)
  encode _ _ = error "can't encode a function!"

instance (Constrain a, Constrain b, Constrain c, Constrain d, d ~ Res (a -> b -> c -> d))
  => Constrain (a -> b -> c -> d) where
  getType _ = FFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)
                      ,getType (Proxy :: Proxy c), getType (Proxy :: Proxy d)]
  gen = genFun
  stitch sz t
    = do f <- stitchFun (Proxy :: Proxy (a -> b -> c -> d)) sz t
         return $ \a b c -> f [toExpr a, toExpr b, toExpr c]
  toExpr  f = var ("FUNCTION" :: Symbol)
  encode _ _ = error "can't encode a function!"
