module Test.LiquidCheck.Expr where

import Language.Fixpoint.Types


infix 4 `eq`
eq  = PAtom Eq
infix 5 `ge`
ge  = PAtom Ge
infix 5 `le`
le  = PAtom Le
infix 3 `iff`
iff = PIff
infix 3 `imp`
imp = PImp


app :: Symbolic a => a -> [Expr] -> Expr
app f es = EApp (dummyLoc $ symbol f) es

var :: Symbolic a => a -> Expr
var = EVar . symbol

prop :: Symbolic a => a -> Pred
prop = PBexp . EVar . symbol

instance Num Expr where
  fromInteger = ECon . I . fromInteger
  (+) = EBin Plus
  (-) = EBin Minus
  (*) = EBin Times
  abs = error "abs of Liquid.Fixpoint.Types.Expr"
  signum = error "signum of Liquid.Fixpoint.Types.Expr"

instance Real Expr where
  toRational (ECon (I i)) = fromIntegral i

instance Enum Expr where
  toEnum = ECon . I . fromIntegral
  fromEnum (ECon (I i)) = fromInteger i

instance Integral Expr where
  div = EBin Div
  mod = EBin Mod
  quotRem x y = (x `div` y, x `mod` y)
  toInteger (ECon (I i)) = i
