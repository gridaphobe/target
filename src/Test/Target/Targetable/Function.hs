{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ViewPatterns         #-}
module Test.Target.Targetable.Function where

import           Control.Applicative
import           Control.Arrow                   (first, second)
import           Control.Monad
import qualified Control.Monad.Catch             as Ex
import           Control.Monad.Reader
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

import           Test.Target.Targetable
import           Test.Target.Eval
import           Test.Target.Expr
import           Test.Target.Monad
import           Test.Target.Types
import           Test.Target.Util


getCtors :: SpecType -> [GHC.DataCon]
getCtors (RApp c _ _ _) = GHC.tyConDataCons $ rtc_tc c
getCtors (RAppTy t _ _) = getCtors t
getCtors (RFun _ i o _) = getCtors i ++ getCtors o
getCtors (RVar _ _)     = []
getCtors t              = error $ "getCtors: " ++ showpp t

dataConSymbol_noUnique :: GHC.DataCon -> Symbol
dataConSymbol_noUnique = qualifiedNameSymbol . GHC.getName

genFun :: Targetable a => Proxy a -> t -> SpecType -> Gen Symbol
genFun p _ (stripQuals -> t)
  = do forM_ (getCtors t) $ \dc -> do
         let c = dataConSymbol_noUnique dc
         t <- lookupCtor c
         addConstructor (c, rTypeSort mempty t)
       fresh (getType p)

stitchFun :: forall f. (Targetable (Res f))
          => Proxy f -> SpecType -> Gen ([Expr] -> Res f)
stitchFun _ (bkArrowDeep . stripQuals -> (vs, tis, to))
  = do mref <- io $ newIORef []
       d <- asks depth
       state' <- get
       opts   <- ask
       let st = state' { variables = [], choices = [], constraints = []
                       , deps = mempty, constructors = [] }
       return $ \es -> unsafePerformIO $ evalGen opts st $ do
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
                 xo <- query (Proxy :: Proxy (Res f)) d (subst su to)
                 vs <- gets variables
                 mapM_ (\x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
                 cs <- gets constraints
                 mapM_ (\c -> io . command ctx $ Assert Nothing c) cs

                 resp <- io $ command ctx CheckSat
                 when (resp == Unsat) $ Ex.throwM SmtFailedToProduceOutput

                 o <- decode xo to
                 -- whenVerbose $ io $ printf "%s -> %s\n" (show es) (show o)
                 io (modifyIORef' mref ((es,o):))
                 io $ command ctx Pop
                 return o
    
genExpr :: Expr -> Gen Symbol
genExpr (EApp (val -> c) es)
  = do xes <- mapM genExpr es
       (xs, _, to) <- bkArrowDeep . stripQuals <$> lookupCtor c
       let su  = mkSubst $ zip xs $ map var xes
           to' = subst su to
       x <- fresh $ FObj $ symbol $ rtc_tc $ rt_tycon to'
       addConstraint $ ofReft (var x) (toReft $ rt_reft to')
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


instance (Targetable a, Targetable b, b ~ Res (a -> b))
  => Targetable (a -> b) where
  getType _ = FFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)]
  query = genFun
  decode _ t
    = do f <- stitchFun (Proxy :: Proxy (a -> b)) t
         return $ \a -> f [toExpr a]
  toExpr  _ = var ("FUNCTION" :: Symbol)
  check _ _ = error "can't check a function!"

instance (Targetable a, Targetable b, Targetable c, c ~ Res (a -> b -> c))
  => Targetable (a -> b -> c) where
  getType _ = FFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)
                      ,getType (Proxy :: Proxy c)]
  query = genFun
  decode _ t
    = do f <- stitchFun (Proxy :: Proxy (a -> b -> c)) t
         return $ \a b -> f [toExpr a, toExpr b]
  toExpr  _ = var ("FUNCTION" :: Symbol)
  check _ _ = error "can't check a function!"

instance (Targetable a, Targetable b, Targetable c, Targetable d, d ~ Res (a -> b -> c -> d))
  => Targetable (a -> b -> c -> d) where
  getType _ = FFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)
                      ,getType (Proxy :: Proxy c), getType (Proxy :: Proxy d)]
  query = genFun
  decode _ t
    = do f <- stitchFun (Proxy :: Proxy (a -> b -> c -> d)) t
         return $ \a b c -> f [toExpr a, toExpr b, toExpr c]
  toExpr  _ = var ("FUNCTION" :: Symbol)
  check _ _ = error "can't check a function!"
