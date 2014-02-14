{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LiquidSMT where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad.State
import           Data.Char
import           Data.Default
import           Data.Function
import           Data.List
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.String
import qualified Data.Text.Lazy as T
import           Debug.Trace
import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Parse
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types hiding (prop)
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.RefType
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

io = liftIO

driver :: Constrain a => Int -> BareType -> a -> IO [a]
driver d t v = runGen $ do
       void $ gen v d t
       ctx <- io $ makeContext Z3
       -- declare sorts
       mapM_ (\ s      -> io . command ctx $ Define s) (sorts v)
       -- declare data constructors
       mapM_ (\ (x,t)  -> io . command ctx $ makeDecl (symbol x) t) cts
       -- declare variables
       vs <- gets variables
       mapM_ (\ x      -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       -- should be part of type class..
       io $ command ctx $ Declare (stringSymbol "len") [FObj $ stringSymbol "GHC.Types.List"] FInt
       -- send assertions about nullary constructors, e.g. []
       -- this should be part of the type class..
--       command ctx $ Assert $ len nil `eq` 0
       -- smtWrite ctx "(assert (forall ((x Int)) (=> (= x nil) (= (len x) 0))))"
       -- smtWrite ctx "(assert (forall ((x Int) (y Int) (xs Int)) (=> (= x (cons y xs)) (= (len x) (+ 1 (len xs))))))"
       cs <- gets constraints
       mapM_ (io . command ctx .  Assert) cs
       -- print =<< command ctx CheckSat
       -- -- get model for variables and nullary constructors
       -- -- FIXME: does having a single [] break things when you have multiple lists?
       -- Values vals <- command ctx (GetValue $ map symbol vs ++ map fst consts)
       -- -- TODO: at this point we'd want to refute the model and get another one
       -- print vals
       vals <- io $ take 10 <$> allSat ctx vs
       -- build up the haskell value
       xs <- forM vals $ \ vs -> do
         setValues vs
         stitch d
--       cleanupContext ctx
       return xs
  where
    -- (cs, vs) = runGen $ constrain d v t
    unints vs = [symbol v | (v,t) <- vs ++ consts, t `elem` interps]
    interps = [FInt, boolsort]
    cts       = ctors v
    -- -- nullary constructors, needed later
    consts   = filter (notFun . snd) cts
    notFun (FFunc _ _) = False
    notFun _           = True
    allSat ctx vs
      = do resp <- command ctx CheckSat
--           print resp
           case resp of
             Error e -> error $ T.unpack e
             Unsat   -> return []
             Sat     -> unsafeInterleaveIO $ do
               Values vals <- command ctx (GetValue $ map symbol vs ++ map symbol consts)
               let cs = refute vals vs
               command ctx $ Assert $ PNot $ pAnd cs
               (map snd vals:) <$> allSat ctx vs

    refute model vs = let equiv = map (map fst) . filter ((>1) . length) . groupBy ((==) `on` snd) . sortBy (comparing snd) $ model
                      in [var x `eq` (ESym $ SL v) | (x,v) <- model, x `elem` unints vs]
                   -- ++ [var x `eq` var y | cls <- equiv
                   --                      , x   <- cls
                   --                      , y   <- cls
                   --                      , x /= y]

makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

type Constraint = [Pred]
type Variable   = ( String -- ^ the name
                  , Sort   -- ^ the `sort'
                  )
type Value      = String

instance Symbolic Variable where
  symbol (x, s) = symbol x

instance SMTLIB2 Constraint where
  smt2 = smt2 . PAnd

-- class Constrain a where
--   constrain :: Int -> a -> BareType -> Gen (Constraint, [Variable])
--   construct :: Int -> Cons a
--   ctors     :: a -> [(Symbol, Sort)]
--   sorts     :: a -> [Sort]

-- type Gen  = State Int
-- type Cons = State [(String,Value)]

-- fresh :: Gen Int
-- fresh = do i <- get
--            modify (+1)
--            return i

-- freshen :: Sort -> Gen Variable
-- freshen x = fresh >>= return . (x,) . (T.unpack (smt2 x) ++) . show

-- runGen :: Gen a -> a
-- runGen x = evalState x 0

-- pop :: Cons (String,Value)
-- pop = do (sv:svs) <- get
--          put svs
--          return sv

-- runCons :: [(String,Value)] -> Cons a -> a
-- runCons svs act = evalState act svs

-- instance Constrain Int where
--   constrain _ _ (RApp _ [] _ r) = do x <- freshen FInt
--                                      return $ (ofReft (snd x) $ toReft r, [x])
--   construct _ = do (_,v) <- pop
--                    return $ read v
--   ctors _ = []
--   sorts _ = []

-- instance Constrain a => Constrain [a] where
--   constrain d _ (RApp _ [a] ps r) = act -- (concat cs, concat vs)
--     where
--       concat4 (a,b,c,d) = (concat a, concat b, concat c, concat d)
--       unzip4 [] = ([],[],[],[])
--       unzip4 ((a,b,c,d):ts) = let (as,bs,cs,ds) = unzip4 ts
--                               in (a:as,b:bs,c:cs,d:ds)
--       act = do (cs,ls,vs,xs) <- concat4 . unzip4 <$> unfoldrNM d build ([nil],[])
--                l <- freshen $ FObj $ stringSymbol "GHC.Types.List"
--                let c  = pOr $ map (var l `eq`) (nil : ls)
--                    cr = ofReft (snd l) $ toReft r
--                    -- cxs = foldr buildAbs [] vs
--                return (cr ++ c:cs, l:xs)

--       buildAbs :: Expr -> [Expr] -> Pred
--       buildAbs h ts = pAnd [h `rel` t | t <- ts]
--         where
--           rel x y = pAnd [subst su p | RPoly [(sx,_)] (RVar _ r) <- ps
--                                      , let Reft (sy, ras) = toReft r
--                                      , RConc p <- ras
--                                      , let su = mkSubst [(sx,x), (sy,y)]
--                                      ]
--       -- build :: ([Expr],[Expr]) -> Gen ((Constraint, [Expr], [Expr], [String]), ([Expr], [Expr]))
--       build (l:ls,vs)
--         = do l' <- freshen $ FObj $ stringSymbol "GHC.Types.List"
--              (cs, x:xs) <- constrain d (undefined :: a) a
--              let v = var x
--                  lv = var $ snd l'
--                  c = pAnd [ lv `eq` cons v l
--                           , len lv `eq` (len l + 1)
--                           , buildAbs v vs]
--              return ((c:cs, lv:l:ls, v:vs, l':x:xs), (lv:l:ls, v:vs))

--   construct d = do (_,x) <- pop
--                    ls    <- unfoldrNM d build []
--                    n     <- fromJust . lookup "nil" <$> get
--                    return $ fromJust $ lookup (traceShow x x) ((n, []):ls)
--     where
--       build l = do (_,v) <- pop
--                    x::a  <- construct d
--                    return ((v,x:l),x:l)
--   ctors _ = [(stringSymbol "nil", listsort), (stringSymbol "cons", FFunc 2 [FInt, listsort, listsort])]
--          ++ ctors (undefined :: a)
--   sorts _ = [FObj $ stringSymbol "GHC.Types.List"] ++ sorts (undefined :: a)

listsort = FObj $ stringSymbol "GHC.Types.List"
boolsort = FObj $ stringSymbol "Bool"

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

newtype Gen a = Gen (StateT GenState IO a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadState GenState)

runGen :: Gen a -> IO a
runGen (Gen x) = evalStateT x def

execGen :: Gen a -> IO GenState
execGen (Gen x) = execStateT x def

data GenState
  = GS { seed        :: Int
       , variables   :: [Variable]
       , choices     :: [String]
       , constraints :: Constraint
       , values      :: [String]
       } deriving (Show)

instance Default GenState where
  def = GS def def def def def

setValues vs = modify $ \s@(GS {..}) -> s { values = vs }

fresh :: Sort -> Gen String
fresh sort
  = do n <- gets seed
       modify $ \s@(GS {..}) -> s { seed = seed + 1 }
       let x = T.unpack (smt2 sort) ++ show n
       modify $ \s@(GS {..}) -> s { variables = (x,sort) : variables }
       return x

freshChoice :: Gen String
freshChoice
  = do c <- fresh boolsort
       modify $ \s@(GS {..}) -> s { choices = c : choices }
       return c

freshChoose :: [String] -> Sort -> Gen String
freshChoose xs sort
  = do x <- fresh sort
       cs <- forM xs $ \x' -> do
               c <- freshChoice
               constrain $ prop c `iff` var x `eq` var x'
               return $ prop c
       constrain $ pOr cs
       return x

constrain :: Pred -> Gen ()
constrain p = modify $ \s@(GS {..}) -> s { constraints = p : constraints }

pop :: Gen String
pop = do v <- gets $ head . values
         modify $ \s@(GS {..}) -> s { values = tail values}
         return v

popN :: Int -> Gen [String]
popN d = replicateM d pop

popChoices :: Int -> Gen [Bool]
popChoices n = fmap read <$> popN n
  where
    read "true"  = True
    read "false" = False
    read e       = error $ "popChoices: " ++ e

class Constrain a where
  gen    :: a -> Int -> BareType -> Gen String
  stitch :: Int -> Gen a
  sorts  :: a -> [Sort]
  ctors  :: a -> [Variable]

instance Constrain Int where
  gen _ _  (RApp _ [] _ r) = fresh FInt >>= \x -> do constrain $ ofReft x (toReft r)
                                                     return x
  stitch _                 = read <$> pop
  sorts _                  = []
  ctors _                  = []

instance (Constrain a) => Constrain [a] where
  gen _ 0 t = gen_nil t
  gen _ n t@(RApp c [ta] ps r)
    = do let t' = RApp c [ta] ps mempty
         x1 <- gen_nil t'
         (x2,c) <- gen_cons ((undefined :: a) : []) n t'
         x3 <- freshChoose [x1,x2] listsort
         constrain $ ofReft x3 (toReft r)
         return x3

  -- stitch n = error "TODO: Constrain [a] stitch"
  stitch 0 = stitch_nil
  stitch d = do [c,n] <- popChoices 2
                pop >>= io . print     -- the "actual" list, but we don't care about it
--                io $ print [n,c]
                cc    <- stitch_cons d
                nn    <- stitch_nil
                case (n,c) of
                  (True,_) -> return nn
                  (_,True) -> return cc

  ctors _ = [ ("nil", listsort)
            , ("cons", FFunc 2 [FInt, listsort, listsort])]
         ++ ctors (undefined :: a)
  sorts _ = [FObj $ stringSymbol "GHC.Types.List"] ++ sorts (undefined :: a)

gen_nil (RApp _ _ _ _)
  = do x <- fresh listsort
       constrain $ len (var x) `eq` 0
       return x

stitch_nil
  = do pop >> return []

gen_cons :: Constrain a => [a] -> Int -> BareType -> Gen (String,String)
gen_cons l@(a:_) n t@(RApp c [ta] ps r)
  = do x  <- gen a (n-1) ta
       let ta' = ta `strengthen` mconcat [subst su p | RPoly [v] tp <- ps
                                                   , let su = mkSubst [(fst v, var x)]
                                                   , let p  = rt_reft tp
                                                   ]
       let t' = RApp c [ta'] ps r
       io $ print t'
       xs <- gen l (n-1) t'
       c  <- return "" --peekChoice
       z  <- fresh listsort
--       constrain $ var z `eq` cons (var x) (var xs)
       constrain $ len (var z) `eq` len (var xs) + 1
--       constrain $ ofReft z $ toReft r
       return (z,c)

--stitch_cons :: Constrain [a] => Int -> Gen [a]
stitch_cons d
  = do z  <- pop
       xs <- stitch (d-1)
       x  <- stitch (d-1)
       return (x:xs)

ofReft :: String -> Reft -> Pred
ofReft s (Reft (v, rs))
  -- = do v' <- freshen $ symbolString v
  --      let s = mkSubst [(v, var v')]
  --      return ([subst s p | RConc p <- rs], [v'])
  = let x = mkSubst [(v, var s)]
    in pAnd [subst x p | RConc p <- rs]

infix 4 `eq`
eq  = PAtom Eq
infix 3 `iff`
iff = PIff

var :: Symbolic a => a -> Expr
var = EVar . symbol

prop :: Symbolic a => a -> Pred
prop = PBexp . EVar . symbol

len :: Expr -> Expr
len x = EApp (dummyLoc $ stringSymbol "len") [x]

-- nil :: Expr
-- nil = var ("nil" :: String)

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

t' :: BareType
t' = rr "{v:[{v0:Int | (v0 >= 0 && v0 < 6)}] | true}"


i :: BareType
i = rr "{v:Int | v > 0}"

list :: [Int]
list = []

inT :: Int
inT = 0
