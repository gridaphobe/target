{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LiquidSMT where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad.State
import           Data.Function
import           Data.List
import           Data.Maybe
import           Data.Ord
import           Data.String
import qualified Data.Text.Lazy as T
import           Debug.Trace
import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Parse
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.Types hiding (ctors, var)
import           System.Exit
import           System.IO.Unsafe
import           Text.PrettyPrint.HughesPJ hiding (first)

import qualified SMTLib2 as SMT
import qualified SMTLib2.Core as SMT
import qualified SMTLib2.Int as SMT

-- instance (SMTLIB2 a) => SMTLIB2 [a] where
--   smt2 = T.concat . map smt2


-- instance SMTLIB2 BareType where
--   smt2 (RApp c as ps r) = smt2 $ toReft r


-- instance SMTLIB2 Reft where
--   smt2 (Reft (v, rs)) = smt2 $ map toPred rs
--     where
--       toPred (RConc p) = p


ofReft :: String -> Reft -> Constraint
ofReft s (Reft (v, rs))
  -- = do v' <- freshen $ symbolString v
  --      let s = mkSubst [(v, var v')]
  --      return ([subst s p | RConc p <- rs], [v'])
  = let x = mkSubst [(v, var s)]
    in [subst x p | RConc p <- rs]

ofPred :: Pred -> SMT.Expr
ofPred PTrue           = SMT.true
ofPred PFalse          = SMT.false
ofPred (PAnd ps)       = SMT.app "and" $ map ofPred ps
ofPred (POr ps)        = SMT.app "or"  $ map ofPred ps
ofPred (PNot p)        = SMT.not       $ ofPred p
ofPred (PImp p q)      = ofPred p SMT.==> ofPred q
ofPred (PIff p q)      = SMT.app "iff" [ofPred p, ofPred q]
ofPred (PBexp e)       = undefined -- ofExpr e
ofPred (PAtom b e1 e2) = ofBrel b (ofExpr e1) (ofExpr e2)
ofPred (PAll ss p)     = undefined
ofPred PTop            = undefined

ofBrel Eq = (SMT.===)
ofBrel Ne = (SMT.=/=)
ofBrel Gt = SMT.nGt
ofBrel Ge = SMT.nGeq
ofBrel Lt = SMT.nLt
ofBrel Le = SMT.nLeq

ofExpr :: Expr -> SMT.Expr
ofExpr (EVar (S s))   = SMT.Lit $ SMT.LitStr s
ofExpr (EBin b e1 e2) = ofBop b (ofExpr e1) (ofExpr e2)
ofExpr (ECon (I i))   = SMT.num i
ofExpr (EApp f es)    = SMT.app (fromString $ show $ val f) $ map ofExpr es

ofBop Plus  = SMT.nAdd
ofBop Minus = SMT.nSub
ofBop Times = SMT.nMul
ofBop Div   = SMT.nDiv
ofBop Mod   = SMT.nMod


-- type Constraint = [SMT.Expr]
-- type Value     = SMT.Literal


driver :: Constrain a => Int -> BareType -> a -> IO [a]
driver d t v
  = do ctx <- makeContext Z3
       -- declare sorts
       mapM_ (\ s      -> command ctx $ Define s) (sorts v)
       -- declare data constructors
       mapM_ (\ (x,t)  -> command ctx $ makeDecl x t) cts
       -- declare variables
       mapM_ (\ x      -> command ctx $ Declare (symbol x) [] (fst x)) vs
       -- declare measures
       -- should be part of type class..
       command ctx $ Declare (stringSymbol "len") [FObj $ stringSymbol "GHC.Types.List"] FInt
       -- send assertions about nullary constructors, e.g. []
       -- this should be part of the type class..
       command ctx $ Assert $ len nil `eq` 0
       -- smtWrite ctx "(assert (forall ((x Int)) (=> (= x nil) (= (len x) 0))))"
       -- smtWrite ctx "(assert (forall ((x Int) (y Int) (xs Int)) (=> (= x (cons y xs)) (= (len x) (+ 1 (len xs))))))"
       mapM_ (command ctx .  Assert) cs
       -- print =<< command ctx CheckSat
       -- -- get model for variables and nullary constructors
       -- -- FIXME: does having a single [] break things when you have multiple lists?
       -- Values vals <- command ctx (GetValue $ map symbol vs ++ map fst consts)
       -- -- TODO: at this point we'd want to refute the model and get another one
       -- print vals
       vals <- take 10 <$> allSat ctx
       -- build up the haskell value
       let xs = map (flip runCons (construct d) . map (first symbolString)) vals
--       cleanupContext ctx
       return xs
  where
    (cs, vs) = runGen $ constrain d v t
    unints   = [symbol v | (t,v) <- vs, t /= FInt] ++ [c | (c,t) <- consts, t /= FInt]
    cts      = ctors v
    -- nullary constructors, needed later
    consts   = filter (notFun . snd) cts
    notFun (FFunc _ _) = False
    notFun _           = True
    allSat ctx = do resp <- command ctx CheckSat
                    case resp of
                      Unsat -> return []
                      Sat   -> unsafeInterleaveIO $
                               do Values vals <- command ctx (GetValue $ map symbol vs ++ map fst consts)
                                  let cs = refute vals
                                  command ctx $ Assert $ PNot $ pAnd cs
                                  (vals:) <$> allSat ctx
    refute model = let equiv = map (map fst) . filter ((>1) . length) . groupBy ((==) `on` snd) . sortBy (comparing snd) $ model
                   in  [var x `eq` (ESym $ SL v) | (x,v) <- model, x `notElem` unints]
                   ++ [var x `eq` var y | cls <- equiv
                                        , x   <- cls
                                        , y   <- cls
                                        , x /= y]

makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

type Constraint = [Pred]
type Variable   = ( Sort   -- ^ the `sort'
                  , String -- ^ the name
                  )
type Value      = String

instance Symbolic Variable where
  symbol (s, x) = symbol x

instance SMTLIB2 Constraint where
  smt2 = smt2 . PAnd

class Constrain a where
  constrain :: Int -> a -> BareType -> Gen (Constraint, [Variable])
  construct :: Int -> Cons a
  ctors     :: a -> [(Symbol, Sort)]
  sorts     :: a -> [Sort]

type Gen  = State Int
type Cons = State [(String,Value)]

fresh :: Gen Int
fresh = do i <- get
           modify (+1)
           return i

freshen :: Sort -> Gen Variable
freshen x = fresh >>= return . (x,) . (T.unpack (smt2 x) ++) . show

runGen :: Gen a -> a
runGen x = evalState x 0

pop :: Cons (String,Value)
pop = do (sv:svs) <- get
         put svs
         return sv

runCons :: [(String,Value)] -> Cons a -> a
runCons svs act = evalState act svs

instance Constrain Int where
  constrain _ _ (RApp _ [] _ r) = do x <- freshen FInt
                                     return $ (ofReft (snd x) $ toReft r, [x])
  construct _ = do (_,v) <- pop
                   return $ read v
  ctors _ = []
  sorts _ = []

instance Constrain a => Constrain [a] where
  constrain d _ (RApp _ [a] ps r) = act -- (concat cs, concat vs)
    where
      concat4 (a,b,c,d) = (concat a, concat b, concat c, concat d)
      unzip4 [] = ([],[],[],[])
      unzip4 ((a,b,c,d):ts) = let (as,bs,cs,ds) = unzip4 ts
                              in (a:as,b:bs,c:cs,d:ds)
      act = do (cs,ls,vs,xs) <- concat4 . unzip4 <$> unfoldrNM d build ([nil],[])
               l <- freshen $ FObj $ stringSymbol "GHC.Types.List"
               let c  = pOr $ map (var l `eq`) (nil : ls)
                   cr = ofReft (snd l) $ toReft r
                   -- cxs = foldr buildAbs [] vs
               return (cr ++ c:cs, l:xs)

      buildAbs :: Expr -> [Expr] -> Pred
      buildAbs h ts = pAnd [h `rel` t | t <- ts]
        where
          rel x y = pAnd [subst su p | RPoly [(sx,_)] (RVar _ r) <- ps
                                     , let Reft (sy, ras) = toReft r
                                     , RConc p <- ras
                                     , let su = mkSubst [(sx,x), (sy,y)]
                                     ]
      -- build :: ([Expr],[Expr]) -> Gen ((Constraint, [Expr], [Expr], [String]), ([Expr], [Expr]))
      build (l:ls,vs)
        = do l' <- freshen $ FObj $ stringSymbol "GHC.Types.List"
             (cs, x:xs) <- constrain d (undefined :: a) a
             let v = var x
                 lv = var $ snd l'
                 c = pAnd [ lv `eq` cons v l
                          , len lv `eq` (len l + 1)
                          , buildAbs v vs]
             return ((c:cs, lv:l:ls, v:vs, l':x:xs), (lv:l:ls, v:vs))

  construct d = do (_,x) <- pop
                   ls    <- unfoldrNM d build []
                   n     <- fromJust . lookup "nil" <$> get
                   return $ fromJust $ lookup (traceShow x x) ((n, []):ls)
    where
      build l = do (_,v) <- pop
                   x::a  <- construct d
                   return ((v,x:l),x:l)
  ctors _ = [(stringSymbol "nil", listsort), (stringSymbol "cons", FFunc 2 [FInt, listsort, listsort])]
         ++ ctors (undefined :: a)
  sorts _ = [FObj $ stringSymbol "GHC.Types.List"] ++ sorts (undefined :: a)

listsort = FObj $ stringSymbol "GHC.Types.List"

unfoldrM :: Monad m => (a -> m (b, a)) -> a -> m [b]
unfoldrM f z
  = do (x,z') <- f z
       xs     <- unfoldrM f z'
       return (x:xs)

unfoldrNM :: Monad m => Int -> (a -> m (b, a)) -> a -> m [b]
unfoldrNM 0 f z = return []
unfoldrNM d f z
  = do (x,z') <- f z
       xs     <- unfoldrNM (d-1) f z'
       return (x:xs)

eq = PAtom Eq

-- fresh :: SMT.Expr -> SMT.Expr
-- fresh x = var $ (++"_") $ render $ SMT.pp x

-- fresh :: Expr -> Expr
-- fresh (EVar x) = EVar . symbol . (++ "_") $ symbolString x


-- var :: String -> SMT.Expr
-- var = flip SMT.app [] . fromString

var :: Symbolic a => a -> Expr
var = EVar . symbol

len :: Expr -> Expr
len x = EApp (dummyLoc $ stringSymbol "len") [x]

-- nil :: SMT.Expr
-- nil = var "nil"

nil :: Expr
nil = var ("nil" :: String)

-- cons :: SMT.Expr -> SMT.Expr -> SMT.Expr
-- cons x xs = SMT.app "cons" [x,xs]

cons :: Expr -> Expr -> Expr
cons x xs = EApp (dummyLoc $ stringSymbol "cons") [x,xs]


instance Num Expr where
  fromInteger = ECon . I . fromInteger
  (+) = EBin Plus
  (-) = EBin Minus
  (*) = EBin Times

instance Real Expr
instance Enum Expr

instance Integral Expr where
  div = EBin Div
  mod = EBin Mod

--------------------------------------------------------------------------------
--- test data
--------------------------------------------------------------------------------

t :: BareType
t = rr "{v:[{v0:Int | (v0 >= 0 && v0 < 6)}]<{\\h t -> h < t}> | (len v) >= 3}"


list :: [Int]
list = []
