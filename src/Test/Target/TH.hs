{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.Target.TH where

import Control.Monad
import qualified Language.Haskell.TH as TH

----------------------------------------------------------------------
-- Testing Polymorphic Functions (courtesy of QuickCheck)
----------------------------------------------------------------------

type Error = forall a. String -> a

-- | Monomorphise an arbitrary property by defaulting all type variables to 'Integer'.
--
-- For example, if @f@ has type @'Ord' a => [a] -> [a]@
-- then @$('monomorphic' 'f)@ has type @['Integer'] -> ['Integer']@.
--
-- If you want to use 'monomorphic' in the same file where you defined the
-- property, the same scoping problems pop up as in 'quickCheckAll':
-- see the note there about @return []@.
monomorphic :: TH.Name -> TH.ExpQ
monomorphic t = do
  ty0 <- fmap infoType (TH.reify t)
  let err msg = error $ msg ++ ": " ++ TH.pprint ty0
  (polys, ctx, ty) <- deconstructType err ty0
  case polys of
    [] -> return (TH.VarE t)
    _ -> do
      integer <- [t| Integer |]
      ty' <- monomorphiseType err integer ty
      return (TH.SigE (TH.VarE t) ty')

infoType :: TH.Info -> TH.Type
infoType (TH.ClassOpI _ ty _ _) = ty
infoType (TH.DataConI _ ty _ _) = ty
infoType (TH.VarI _ ty _ _) = ty

deconstructType :: Error -> TH.Type -> TH.Q ([TH.Name], TH.Cxt, TH.Type)
deconstructType err ty0@(TH.ForallT xs ctx ty) = do
  let plain (TH.PlainTV  _)          = True
-- NOTE: this is a poor proxy for template-haskell >= 2.8
#if __GLASGOW_HASKELL__ >= 710
      plain (TH.KindedTV _ TH.StarT) = True
#else
      plain (TH.KindedTV _ TH.StarK) = True
#endif
      plain _                        = False
  unless (all plain xs) $ err "Higher-kinded type variables in type"
  return (map (\(TH.PlainTV x) -> x) xs, ctx, ty)
deconstructType _ ty = return ([], [], ty)

monomorphiseType :: Error -> TH.Type -> TH.Type -> TH.TypeQ
monomorphiseType err mono ty@(TH.VarT n) = return mono
monomorphiseType err mono (TH.AppT t1 t2) = liftM2 TH.AppT (monomorphiseType err mono t1) (monomorphiseType err mono t2)
monomorphiseType err mono ty@(TH.ForallT _ _ _) = err $ "Higher-ranked type"
monomorphiseType err mono ty = return ty
