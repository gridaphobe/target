{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module LiquidSMT where

import           Control.Applicative
import           Control.Arrow hiding (app)
import           Control.Exception.Base
import           Control.Monad.State
import           Data.Char
import           Data.Default
import           Data.Function
import qualified Data.HashMap.Strict as M
import           Data.List hiding (sort)
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.String
import qualified Data.Text.Lazy as T
import           Debug.Trace
import           GHC
import           Name
import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Parse
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types hiding (prop, Def)
import           Language.Haskell.Liquid.CmdLine
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.GhcMisc
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types hiding (var, env)
import qualified Language.Haskell.TH as TH
import           System.Exit
import           System.IO.Unsafe
import           Text.PrettyPrint.HughesPJ hiding (first)
import           Text.Printf

io = liftIO


reaches root model deps = go root
  where
    go root
      | isChoice && taken
      = (root,val) : concatMap go [r | (x,r) <- deps, x == root]
      | isChoice
      = [(root,val)]
      | otherwise
      = (root,val) : concatMap go [r | (x,r) <- deps, x == root]
      where
        val      = fromJust $ lookup root model
        isChoice = "CHOICE" `isPrefixOf` symbolString root
        taken    = val == "true"


myTrace s x = trace (s ++ ": " ++ show x) x

makeDecl :: Symbol -> Sort -> Command
makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

type Constraint = [Pred]
type Variable   = ( String -- ^ the name
                  , Sort   -- ^ the `Sort'
                  )
type Value      = String

instance Symbolic Variable where
  symbol (x, s) = symbol x

instance SMTLIB2 Constraint where
  smt2 = smt2 . PAnd


listsort = FObj $ stringSymbol "Int"
boolsort = FObj $ stringSymbol "Bool"

newtype Gen a = Gen (StateT GenState IO a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadState GenState)

runGen :: GhcSpec -> Gen a -> IO a
runGen e (Gen x) = evalStateT x (initGS e)

execGen :: GhcSpec -> Gen a -> IO GenState
execGen e (Gen x) = execStateT x (initGS e)

data GenState
  = GS { seed        :: !Int
       , variables   :: ![Variable]
       , choices     :: ![String]
       , constraints :: !Constraint
       , values      :: ![String]
       , deps        :: ![(String, String)]
       , ctorEnv     :: !DataConEnv
       , measEnv     :: !MeasureEnv
       } deriving (Show)

initGS sp = GS def def def def def def sigs (measures sp)
  where
    sigs = map (showpp *** val) (ctors sp)

type DataConEnv = [(String, SpecType)]
type MeasureEnv = [Measure SpecType DataCon]

setValues vs = modify $ \s@(GS {..}) -> s { values = vs }

addDep from to = modify $ \s@(GS {..}) -> s { deps = (from,to):deps }

-- | `fresh' generates a fresh variable and encodes the reachability
-- relation between variables, e.g. `fresh xs sort` will return a new
-- variable `x`, from which everything in `xs` is reachable.
fresh :: [String] -> Sort -> Gen String
fresh xs sort
  = do n <- gets seed
       modify $ \s@(GS {..}) -> s { seed = seed + 1 }
       let x = T.unpack (smt2 sort) ++ show n
       modify $ \s@(GS {..}) -> s { variables = (x,sort) : variables }
       mapM_ (addDep x) xs
       return x

freshChoice :: [String] -> Gen String
freshChoice xs
  = do c <- fresh xs choicesort
       modify $ \s@(GS {..}) -> s { choices = c : choices }
       return c

choicesort = FObj $ stringSymbol "CHOICE"

freshChoose :: [String] -> Sort -> Gen String
freshChoose xs sort
  = do x <- fresh [] sort
       cs <- forM xs $ \x' -> do
               c <- freshChoice [x']
               constrain $ prop c `iff` var x `eq` var x'
               addDep x c
               return $ prop c
       constrain $ pOr cs
       constrain $ pAnd [ PNot $ pAnd [x, y]
                        | [x, y] <- filter ((==2) . length) $ subsequences cs ]
       return x


make :: TH.Name -> [String] -> Sort -> Gen String
make c vs s
  = do x  <- fresh vs s
       t <- (fromJust . lookup (show c)) <$> gets ctorEnv
       let (xs, _, rt) = bkArrowDeep t
           su          = mkSubst $ zip (map symbol xs) (map var vs)
       constrain $ ofReft x $ subst su $ toReft $ rt_reft rt
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


class Testable a where
  test :: a -> Int -> SpecType -> Gen ()

instance (Constrain a, Constrain b) => Testable (a -> b) where
  test f d (bkUniv -> (_,_,_,(RFun x i o r))) = do
    a <- gen (undefined :: a) d i
    vals <- allSat [symbol a]
    -- build up the haskell value
    (xvs :: [a]) <- forM vals $ \ vs -> do
      setValues vs
      stitch d
    io $ print xvs
    forM_ xvs $ \xv -> do
      r <- io $ evaluate (f xv)
      io . print =<< evalReft (M.fromList [(show x, toExpr xv)]) (toReft $ rt_reft o) (toExpr r)

instance (Constrain a, Constrain b, Constrain c) => Testable (a -> b -> c) where
  test f d (bkUniv -> (_,_,_,(RFun xa ta (RFun xb tb to _) _))) = do
    a <- gen (undefined :: a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (undefined :: b) d tb'
    vals <- allSat [symbol a, symbol b]
    -- build up the haskell value
    (xvs :: [(a,b)]) <- forM vals $ \ vs -> do
      setValues vs
      b <- stitch d
      a <- stitch d
      return (a,b)
    forM_ xvs $ \(a,b) -> do
      io $ print (a,b)
      r <- io $ evaluate (f a b)
      io . print =<< evalReft (M.fromList [(show xa, toExpr a),(show xb, toExpr b)]) (toReft $ rt_reft to) (toExpr r)
  test f d t = error $ show t

allSat :: [Symbol] -> Gen [[String]]
allSat roots = setup >>= go 100
  where
    setup = do
       ctx <- io $ makeContext Z3
       -- declare sorts
       io $ smtWrite ctx "(define-sort CHOICE () Bool)"
       -- declare variables
       vs <- gets variables
       mapM_ (\ x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       ms <- gets measEnv
       mapM_ (\ m -> io . command ctx $ makeDecl (val $ name m) (rTypeSort mempty $ sort m)) ms
       cs <- gets constraints
       deps <- map (symbol *** symbol) <$> gets deps
       mapM_ (io . command ctx .  Assert) cs
       return (ctx,vs,deps)

    go 0 _ = return []
    go n (ctx,vs,deps) = do
       resp <- io $ command ctx CheckSat
       case resp of
         Error e -> error $ T.unpack e
         Unsat   -> return []
         Sat     -> do
           Values model <- io $ command ctx (GetValue $ map symbol vs)
           let cs = refute roots model deps vs
           io $ command ctx $ Assert $ PNot $ pAnd cs
           (map snd model:) <$> go (n-1) (ctx,vs,deps)

    ints vs = [symbol v | (v,t) <- vs, t `elem` interps]
    interps = [FInt, boolsort, choicesort]
    refute roots model deps vs = [ var x `eq` (ESym $ SL v)
                                 | (x,v) <- realized
                                 , x `elem` ints vs]
      where
        realized = concat [reaches root model deps | root <- roots]


--check :: a -> SpecType -> IO Bool
-- check1 x (sa,a) t
--   = do v <- evaluate (Right x) `catch` \(_ :: SomeException) -> return $ Left "CRASH"
--        b <- evaluate (evalReft undefined (toReft t) x)
--             `catch` \(_ :: SomeException) -> return False
--        let k = if b
--                then "SAFE" :: String
--                else "UNSAFE"
--        printf "%s:\tx = %d, f x = %s\n" k (show x) (show v)


evalReft :: M.HashMap String Expr -> Reft -> Expr -> Gen Bool
evalReft m (Reft (S v, rs)) x = and <$> sequence [ evalPred p (M.insert v x m)
                                                 | RConc p <- rs
                                                 ]

evalPred PTrue           m = return True
evalPred PFalse          m = return False
evalPred (PAnd ps)       m = and <$> sequence [evalPred p m | p <- ps]
evalPred (POr ps)        m = or  <$> sequence [evalPred p m | p <- ps]
evalPred (PNot p)        m = not <$> evalPred p m
evalPred (PImp p q)      m = do pv <- evalPred p m
                                if pv
                                   then evalPred q m
                                   else return True
evalPred (PIff p q)      m = and <$> sequence [ evalPred (p `imp` q) m
                                              , evalPred (q `imp` p) m
                                              ]
evalPred (PAtom b e1 e2) m = evalBrel b <$> evalExpr e1 m <*> evalExpr e2 m
evalPred p               m = error $ "evalPred: " ++ show p
-- evalPred (PBexp e)       m = undefined -- ofExpr e
-- evalPred (PAll ss p)     m = undefined
-- evalPred PTop            m = undefined

evalBrel Eq = (==)
evalBrel Ne = (/=)
evalBrel Gt = (>)
evalBrel Ge = (>=)
evalBrel Lt = (<)
evalBrel Le = (<=)

applyMeasure :: Measure SpecType DataCon -> Expr -> M.HashMap String Expr -> Gen Expr
applyMeasure m (EApp c xs) env = evalExpr e' env
  where
    eq = fromJust $ find ((==val c) . symbol . show . ctor) $ eqns m
    (E e) = body eq
    e' = subst (mkSubst $ zip (binds eq) xs) e
applyMeasure m e           env = error $ printf "applyMeasure(%s, %s)" (showpp m) (showpp e)

evalExpr :: Expr -> M.HashMap String Expr -> Gen Expr
evalExpr (ECon i)       m = return $ ECon i
evalExpr (EVar x)       m = return $ m M.! showpp x
evalExpr (EBin b e1 e2) m = evalBop b <$> evalExpr e1 m <*> evalExpr e2 m
evalExpr (EApp f es)    m
  = do ms <- find ((==f) . name) <$> gets measEnv
       case ms of
         Nothing -> EApp f <$> mapM (flip evalExpr m) es
         Just ms -> do e' <- (evalExpr (head es) m)
                       applyMeasure ms e' m

evalBop Plus (ECon (I x)) (ECon (I y)) = ECon . I $ x + y
evalBop b    e1           e2           = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)


class Show a => Constrain a where
  gen    :: a -> Int -> SpecType -> Gen String
  stitch :: Int -> Gen a
  toExpr :: a -> Expr

instance Constrain () where
  gen _ _ _ = fresh [] FInt
  stitch _  = return ()
  toExpr _  = app (stringSymbol "()") []

instance Constrain Int where
  gen _ d (RApp _ [] _ r) = fresh [] FInt >>= \x ->
    do constrain $ ofReft x (toReft r)
       -- use the unfolding depth to constrain the range of Ints, like QuickCheck
       constrain $ var x `ge` (0 - fromIntegral d)
       constrain $ var x `le` fromIntegral d
       return x
  stitch _ = read <$> pop
  toExpr i = ECon $ I $ fromIntegral i

instance (Constrain a) => Constrain [a] where
  gen _ 0 t = gen_nil t
  gen _ d t@(RApp c [ta] ps r)
    = do let t' = RApp c [ta] ps mempty
         x1 <- gen_nil t'
         x2 <- gen_cons (undefined :: [a]) d t'
         x3 <- freshChoose [x1,x2] listsort
         constrain $ ofReft x3 (toReft r)
         return x3

  stitch 0 = stitch_nil
  stitch d = do [c,n] <- popChoices 2
                pop  -- the "actual" list, but we don't care about it
                cc    <- stitch_cons d
                nn    <- stitch_nil
                case (n,c) of
                  (True,_) -> return nn
                  (_,True) -> return cc

  toExpr []     = app (stringSymbol "[]") -- (show '[])
                      []
  toExpr (x:xs) = app (stringSymbol ":") -- (show '(:))
                       [toExpr x, toExpr xs]

gen_nil (RApp _ _ _ _)
  = make '[] [] listsort

stitch_nil
  = do pop >> return []

gen_cons :: forall a. Constrain a => [a] -> Int -> SpecType -> Gen String
gen_cons _ n t@(RApp c [ta] ps r)
  = do x  <- gen (undefined :: a) (n-1) ta
       let ta' = case ps of
                   []  -> ta
                   [p] -> applyRef p [x] ta
       let t'  = RApp c [ta'] ps r
       xs <- gen (undefined :: [a]) (n-1) t'
       make '(:) [x,xs] listsort
gen_cons _ _ t = error $ show t

stitch_cons :: Constrain a => Int -> Gen [a]
stitch_cons d
  = do z  <- pop
       xs <- stitch (d-1)
       x  <- stitch (d-1)
       return (x:xs)


data Tree a = Leaf | Node a (Tree a) (Tree a) deriving (Eq, Ord, Show)

treesort = FObj $ stringSymbol "Tree"

treeList Leaf = []
treeList (Node x l r) = treeList l ++ [x] ++ treeList r

instance Constrain a => Constrain (Tree a) where
  gen _ 0 t = gen_leaf t
  gen _ d t@(RApp c [ta] ps r)
    = do let t' = RApp c [ta] ps mempty
         l <- gen_leaf t'
         n <- gen_node (Node (undefined :: a) undefined undefined) d t'
         z <- freshChoose [l,n] treesort
         constrain $ ofReft z (toReft r)
         return z

  stitch 0 = stitch_leaf
  stitch d
    = do [cn,cl] <- popChoices 2
         void pop -- "actual" tree
         n <- stitch_node d
         l  <- stitch_leaf
         case (cn,cl) of
           (True,_) -> return n
           (_,True) -> return l

gen_leaf _
  = make 'Leaf [] treesort

stitch_leaf = pop >> return Leaf

gen_node :: Constrain a => Tree a -> Int -> SpecType -> Gen String
gen_node foo@(Node a _ _) d t@(RApp c [ta] [pl,pr] r)
  = do x <- gen (a) (d-1) ta
       let tal = applyRef pl [x] ta
       let tl  = RApp c [tal] [pl,pr] r
       let tar = applyRef pr [x] ta
       let tr  = RApp c [tar] [pl,pr] r
       nl <- gen (foo) (d-1) tl
       nr <- gen (foo) (d-1) tr
       make 'Node [x,nl,nr] treesort

stitch_node d
  = do z <- pop
       nr <- stitch (d-1)
       nl <- stitch (d-1)
       x <- stitch (d-1)
       return (Node x nl nr)


ofReft :: String -> Reft -> Pred
ofReft s (Reft (v, rs))
  = let x = mkSubst [(v, var s)]
    in pAnd [subst x p | RConc p <- rs]


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

instance Real Expr
instance Enum Expr

instance Integral Expr where
  div = EBin Div
  mod = EBin Mod



-- applyRef :: Ref -> [Variable] -> RType
applyRef (RPoly xs p) vs t
  = t `strengthen` r
  where
    r  = subst su $ rt_reft p
    su = mkSubst [(fst x, var v) | x <- xs | v <- vs]


getSpec :: FilePath -> IO GhcSpec
getSpec target
  = do cfg   <- mkOpts mempty
       info  <- getGhcInfo cfg target
       case info of
         Left err -> error $ show err
         Right i  -> return $ spec i

testOne :: Testable f => f -> String -> FilePath -> IO ()
testOne f name path
  = do sp <- getSpec path
       let ty = val $ fromJust $ lookup (name) $ map (first showpp) $ tySigs sp
       runGen sp $ test f 5 ty

mkTest :: TH.Name -> TH.ExpQ
mkTest f = do loc <- TH.location
              let name = show f
                  file = TH.loc_filename loc
              [| testOne $(TH.varE f) $(TH.stringE name) $(TH.stringE file) |]

-- mytake :: Int -> [a] -> [a]
-- mytake 0 xs     = xs
-- mytake _ []     = []
-- mytake n (x:xs) = x : mytake (n-1) xs

--------------------------------------------------------------------------------
--- | Dependency Graph
--------------------------------------------------------------------------------

data Dep = Empty
         | Choice String [Dep]
         | Direct String Dep
         deriving (Show, Eq)

leaf = flip Direct Empty
x20 = leaf "x20"
x21 = leaf "x21"
p10 = Direct "p10" x20
p11 = Direct "p11" x21
x10 = Choice "x10" [p10, p11]
x11 = leaf "x11"
p00 = Direct "p00" x10
p01 = Direct "p01" x11
x0  = Choice "x0" [p00, p01]


--------------------------------------------------------------------------------
--- | Template Haskell
--------------------------------------------------------------------------------

-- ref :: ?? -> Q [Dec]

infix 6 ~>
(~>) :: Bind a b c d -> RType a b c d -> RType a b c d
(x,i) ~> o = RFun x i o undefined

type Bind a b c d = (Symbol, RType a b c d)

infix 5 -:
(-:) :: Symbol -> RType a b c d -> Bind a b c d
x-:t = (x,t)

instance IsString Symbol where
  fromString = symbol


-- quoteRTypeDec s
--   = do -- loc <- TH.location
--        -- let pos =  (TH.loc_filename loc,
--        --             fst (TH.loc_start loc),
--        --             snd (TH.loc_start loc))
--        let t :: SpecType = rr s
--        let ht = TH.ConT ''Int
--        let sig = TH.SigD (TH.mkName "foo") ht
--        return [sig]
