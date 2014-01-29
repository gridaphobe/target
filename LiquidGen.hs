{-# LANGUAGE ScopedTypeVariables #-}
module LiquidGen where

import Control.Applicative
import Control.Monad.Reader
import Data.SBV
import Language.Fixpoint.Parse
import Language.Fixpoint.Types hiding (Symbolic)
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types

-- foo :: SpecType -> Symbolic a
-- foo (RApp c [] [] r)
--   = do (v :: SInteger) <- exists "v"
--        undefined

test s = sat $ gen $ toReft $ rt_reft (rr s :: BareType)


gen :: Reft -> Symbolic SBool
gen (Reft ((S v), rs))
  = do (v :: SInteger) <- exists v
       solve $ map (flip runReader v . ofPred . toPred) rs

gen' :: Refa -> Symbolic a
gen' (RConc p) = gen'' p

gen'' :: Pred -> Symbolic a
gen'' = undefined


toPred (RConc p) = p

type Convert = Reader SInteger

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

-- ofExpr :: Expr -> Convert SBool
ofExpr (EVar (S s))   = ask
ofExpr (EBin b e1 e2) = ofBop b <$> ofExpr e1 <*> ofExpr e2
ofExpr (ECon (I i))   = return $ literal i

-- ofBop :: Bop -> SInteger -> SInteger -> SInteger
ofBop Plus  = (+)
ofBop Minus = (-)
ofBop Times = (*)
ofBop Div   = sDiv
ofBop Mod   = sMod
