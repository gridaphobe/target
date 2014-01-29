{-# LANGUAGE ScopedTypeVariables #-}
module LiquidGen where

import Control.Applicative
import Control.Monad.Reader
import qualified Data.Map as M
import Data.SBV
import Language.Fixpoint.Parse
import Language.Fixpoint.Types hiding (Symbolic)
import Language.Haskell.Liquid.Parse ()
import Language.Haskell.Liquid.Types

test s = sat $ runReaderT (genT (rr s :: BareType)) M.empty

genT :: BareType -> Convert SBool
genT (RApp c as ps r)
  = gen $ toReft r
genT (RFun (S x) i o r)
  = do x' <- lift $ sInteger x
       local (M.insert x x') $ do
         lift . constrain =<< genT i
         genT o

-- blah = sat $ do x <- sInteger "x"
--                 solve [x .== 100]
--                 v <- sInteger "v"
--                 return $ v .== x + 1

gen :: Reft -> Convert SBool
gen (Reft (S v, rs))
  = do mv <- asks $ M.lookup v
       case mv of
         Nothing -> do
           v' <- lift $ sInteger v
           local (M.insert v v') go
         Just _ -> go
  where
    go = bAnd <$> mapM (ofPred . toPred) rs

toPred (RConc p) = p

type Convert = ReaderT (M.Map String SInteger) Symbolic

ofPred :: Pred -> Convert SBool
ofPred PTrue           = return true
ofPred PFalse          = return false
ofPred (PAnd ps)       = bAnd <$> mapM ofPred ps --foldr (\x y -> ofPred x &&& y) true ps
ofPred (POr ps)        = bOr  <$> mapM ofPred ps --foldr (\x y -> ofPred x ||| y) false ps
ofPred (PNot p)        = bnot <$> ofPred p
ofPred (PImp p q)      = (==>) <$> ofPred p <*> ofPred q
ofPred (PIff p q)      = (<=>) <$> ofPred p <*> ofPred q
ofPred (PBexp e)       = undefined -- ofExpr e
ofPred (PAtom b e1 e2) = ofBrel b <$> ofExpr e1 <*> ofExpr e2
ofPred (PAll ss p)     = undefined
ofPred PTop            = undefined

ofBrel Eq = (.==)
ofBrel Ne = (./=)
ofBrel Gt = (.>)
ofBrel Ge = (.>=)
ofBrel Lt = (.<)
ofBrel Le = (.<=)

ofExpr :: Expr -> Convert SInteger
ofExpr (EVar (S s))   = asks (M.! s)
ofExpr (EBin b e1 e2) = ofBop b <$> ofExpr e1 <*> ofExpr e2
ofExpr (ECon (I i))   = return $ literal i

ofBop :: Bop -> SInteger -> SInteger -> SInteger
ofBop Plus  = (+)
ofBop Minus = (-)
ofBop Times = (*)
ofBop Div   = sDiv
ofBop Mod   = sMod


--------------------------------------------------------------------------------
--- STUPID Functor -> Applicative -> Monad NONSENSE
--------------------------------------------------------------------------------

instance Applicative Symbolic where
  pure  = return
  f <*> x = do f <- f
               x <- x
               return $ f x
