module Test.Target.Expr where

import Language.Fixpoint.Types


eq :: Expr -> Expr -> Pred
eq  = PAtom Eq
infix 4 `eq`

ge :: Expr -> Expr -> Pred
ge  = PAtom Ge
infix 5 `ge`

le :: Expr -> Expr -> Pred
le  = PAtom Le
infix 5 `le`

gt :: Expr -> Expr -> Pred
gt  = PAtom Gt
infix 5 `gt`

lt :: Expr -> Expr -> Pred
lt  = PAtom Lt
infix 5 `lt`

iff :: Pred -> Pred -> Pred
iff = PIff
infix 3 `iff`

imp :: Pred -> Pred -> Pred
imp = PImp
infix 3 `imp`


app :: Symbolic a => a -> [Expr] -> Expr
app f es = EApp (dummyLoc $ symbol f) es

var :: Symbolic a => a -> Expr
var = EVar . symbol

-- prop :: Symbolic a => a -> Pred
-- prop = PBexp . EVar . symbol
prop :: Expr -> Pred
prop = PBexp

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
