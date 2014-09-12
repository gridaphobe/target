{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module List where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import           Data.List
import           Data.Monoid
import           GHC.Generics

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types          hiding (prop, ofReft)
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Tidy     (tidySymbol)
import           Language.Haskell.Liquid.Types    hiding (var)

import           Test.LiquidCheck.Constrain hiding (make,make',make2,ofReft,constrain,choose)
import           Test.LiquidCheck.Driver
import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Eval
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util
import           Test.LiquidCheck

import           Data.Proxy
import           Debug.Trace

--------------------------------------------------------------------------------
--- Code
--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a) deriving (Generic, Show)
infixr `Cons`

insert :: Int -> List Int -> List Int
insert x ys = insert' x ys

insert' x Nil
  = Cons x Nil
insert' x (y `Cons` ys)
  | x < y
  = x `Cons` y `Cons` ys
  | x == y
  = y `Cons` ys
  | otherwise
  = y `Cons` insert' x ys

insert_bad :: Int -> List Int -> List Int
insert_bad x Nil
  = Cons x Nil
insert_bad x (y `Cons` ys)
  | x < y
  = x `Cons` y `Cons` ys
  | otherwise
  = y `Cons` insert_bad x ys

mytake :: Int -> List Int -> List Int
mytake 0 xs          = Nil
mytake _ Nil         = Nil
mytake n (Cons x xs) = x `Cons` mytake (n-1) xs

{-@ mymap :: (Int -> Int) -> x:List Int -> {v:List Int | (llen v) = (llen x)} @-}
mymap :: (Int -> Int) -> List Int -> List Int
mymap f Nil         = Nil
mymap f (Cons x xs) = Cons (f x) (mymap f xs)

--------------------------------------------------------------------------------
--- LiquidCheck
--------------------------------------------------------------------------------
-- instance Constrain a => Constrain (List a)

instance Constrain a => Constrain (List a) where
  -- bookkeeping to ease debugging of .smt2 file, not strictly necessary
  getType _ = FObj "List.List"

  gen p 0 t = do 
    x <- fresh (getType p)
    n <- gen_nil x
    choose x [n]
    constrain x t
    return x
  gen p d t = do 
    -- `x` corresponds to `xs` from the figure in sec. 2
    x <- fresh (getType p)
    let t' = true t
    -- `n` corresponds to `xs` as well, *if* `c0` was picked
    n <- gen_nil x
    -- `c` corresponds to `xs` as well, *if* `c1` was picked
    c <- gen_cons (Proxy :: Proxy a, p) x d t'
    -- `choose` encodes the reachability stuff between `xs`, `c0`, and `c1`,
    -- and adds the `c0 xor c1` constraint
    choose x [n,c]
    -- now we add the top-level constraint, i.e. `p` in `{v:List a | p}`
    constrain x t
    return x

  stitch 0 _ = 
    fst <$> stitch_nil
  stitch d t = do 
    (c,cc) <- stitch_cons d t
    (n,cn) <- stitch_nil
    case (cc, cn) of
      (True,_) -> return c
      (_,True) -> return n

                    -- app = Fixpoint.EApp
  toExpr Nil         = app ("List.Nil"  :: Symbol) []
  toExpr (Cons x xs) = app ("List.Cons" :: Symbol) [toExpr x, toExpr xs]

gen_nil x = make0 "List.Nil" x
gen_cons ps x d t = make2 "List.Cons" ps t x d

stitch_nil = do
  -- equivalent to `stitch0 Nil`
  c <- popChoice
  return (Nil,c)
stitch_cons d t = do
  -- equivalent to `stitch2 Cons (d-1)`
  xs <- stitch (d-1) t
  x  <- stitch (d-1) t
  c  <- popChoice
  return (Cons x xs, c)

-- | cancel out the top-level refinement
true :: SpecType -> SpecType
true t = t { rt_reft = top (rt_reft t) }

make0 :: Symbol -> Variable -> Gen Variable
make0 c x = withFreshChoice $ \ch -> 
  -- generate constraints for `Nil`
  make c x []


-- | In order to generate constraints for `Cons x xs` we first need to generate
-- `x` and `xs`. We're given a refined type `t = {v:List a | p}`, so we need to
-- deconstruct `t` to determine proper types for `x` and `xs`. `applyPreds` does
-- for us, in particular it handles propagating the instantiation of `a` and any
-- abstract refinements.
make2 :: (Constrain a, Constrain b)
      => Symbol             -- ^ the DataCon
      -> (Proxy a, Proxy b) -- ^ proxies for the type-class instances
      -> SpecType           -- ^ the refined type
      -> Variable           -- ^ the Variable representing the constructed value
      -> Int                -- ^ the depth
      -> Gen Variable
make2 c (pa,pb) t v d = withFreshChoice $ \ch -> do
  dcp <- lookupCtor c
  tyi <- gets tyconInfo
  emb <- gets embEnv
  -- figure out the types for `x` and `xs`
  let [t1,t2] = applyPreds (addTyConInfo emb tyi t) dcp
  -- generate constraints for `x`
  x1 <- gen pa (d-1) (snd t1)
  let su = mkSubst [(fst t1, var x1)]
  -- generate constraints for `xs`
  x2 <- gen pb (d-1) (subst su $ snd t2)
  -- generate constraints for `Cons x xs`
  make c v [x1,x2]

make :: Symbol     -- ^ the DataCon
     -> Variable   -- ^ the Variable representing the constructed value
     -> [Variable] -- ^ the Variables representing the arguments to the DataCon
     -> Gen ()
make c v vs
  = do Just ch <- gets chosen
       mapM_ (addDep ch) vs
       -- ch => x = c vs
       addConstraint $ prop (fst ch) `imp` (var (fst v) `eq` app c (map (var . fst) vs))
       t <- lookupCtor c
       let (xs, _, rt) = bkArrowDeep t
           su          = mkSubst $ zip (map symbol xs) (map var vs)
       -- bookkeeping to ease debugging
       addConstructor (c, rTypeSort mempty t)
       -- add constraints to the constructed value, e.g. `len x = 0` if c == Nil
       constrain v $ subst su rt

constrain :: Variable -> SpecType -> Gen ()
constrain v t
  = do mc <- gets chosen
       case mc of
         Nothing -> addConstraint p
         Just c  -> let p' = prop c `imp` p
                    -- we need to guard constraints by the choice variable so
                    -- they are ignored unless Z3 picks `c`
                    in addConstraint p'
  where
    p = ofReft v (toReft $ rt_reft t)

ofReft :: Variable -> Reft -> Pred
ofReft (s,_) (Reft (v, rs))
  = let x = mkSubst [(v, var s)]
    in pAnd [subst x p | RConc p <- rs]

choose :: Variable -> [Variable] -> Gen ()
choose x cs
  = do cs <- forM cs $ \c -> do
               addDep x c
               return $ prop c
       addConstraint $ pOr cs
       addConstraint $ pAnd [ PNot $ pAnd [x, y]
                            | [x, y] <- filter ((==2) . length) $ subsequences cs ]

{-@ data List a <p:: a -> a -> Prop> =
      Nil | Cons (zoo::a) (zoog::List <p> (a<p zoo>))
  @-}

{-@ measure llen :: List a -> Int
    llen(Nil) = 0
    llen(Cons x xs) = 1 + llen(xs)
  @-}

{-@ type SortedList a = List <{\x y -> x < y}> a @-}

{-@ mytake :: n:Nat -> xs:SortedList Nat
           -> {v:SortedList Nat | (Min (llen v) n (llen xs))} @-}

{-@ insert :: n:Int -> xs:SortedList Int -> SortedList Int @-}

