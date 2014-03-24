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
import           Language.Fixpoint.Types hiding (prop, Def)
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types hiding (ctors, var, env)
import qualified Language.Haskell.TH as TH
import           System.Exit
import           System.IO.Unsafe
import           Text.PrettyPrint.HughesPJ hiding (first)
import           Text.Printf

-- instance (SMTLIB2 a) => SMTLIB2 [a] where
--   smt2 = T.concat . map smt2


-- instance SMTLIB2 BareType where
--   smt2 (RApp c as ps r) = smt2 $ toReft r


-- instance SMTLIB2 Reft where
--   smt2 (Reft (v, rs)) = smt2 $ map toPred rs
--     where
--       toPred (RConc p) = p

io = liftIO

driver :: Constrain a => Int -> Int -> BareType -> a -> DataConEnv -> IO [a]
driver n d t v env = runGen env $ do
       root <- gen v d t
       ctx <- io $ makeContext Z3
       let ctx' = ctx  -- {verbose = True}
       -- declare sorts
       io $ smtWrite ctx "(define-sort CHOICE () Bool)"
       --mapM_ (\ s      -> io . command ctx $ Define s) (sorts v)
       -- declare data constructors
       -- mapM_ (\ (x,t)  -> io . command ctx $ makeDecl (symbol x) t) cts
       -- declare variables
       vs <- gets variables
       mapM_ (\ x      -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       -- should be part of type class..
       io $ command ctx $ Declare (stringSymbol "len") [listsort] FInt
       -- io $ command ctx $ Declare (stringSymbol "size") [treesort] FInt
       cs <- gets constraints
       deps <- gets deps
       mapM_ (io . command ctx .  Assert) cs
       vals <- io $ take n <$> allSat ctx' (symbol root) (map (symbol *** symbol) deps) vs
       -- build up the haskell value
       xs <- forM vals $ \ vs -> do
         setValues vs
         stitch d
       io $ cleanupContext ctx
       return xs
  where
    unints vs = [symbol v | (v,t) <- vs, t `elem` interps]
    interps   = [FInt, boolsort, choicesort]
    allSat ctx root deps vs
      = do resp <- command ctx CheckSat
           print resp
           case resp of
             Error e -> error $ T.unpack e
             Unsat   -> return []
             Sat     -> unsafeInterleaveIO $ do
               Values model <- command ctx (GetValue $ map symbol vs)
               let cs = refute root model deps vs
               command ctx $ Assert $ PNot $ pAnd cs
               (map snd model:) <$> allSat ctx root deps vs

    -- refute model vs = let equiv = map (map fst) . filter ((>1) . length) . groupBy ((==) `on` snd) . sortBy (comparing snd) $ model
    --                   in [var x `eq` (ESym $ SL v) | (x,v) <- model, x `elem` unints vs]
    refute root model deps vs = let realized = reaches root model deps
                                in [var x `eq` (ESym $ SL v) | (x,v) <- realized, x `elem` unints vs]

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

runGen :: DataConEnv -> Gen a -> IO a
runGen e (Gen x) = evalStateT x (initGS e)

execGen :: DataConEnv -> Gen a -> IO GenState
execGen e (Gen x) = execStateT x (initGS e)

data GenState
  = GS { seed        :: !Int
       , variables   :: ![Variable]
       , choices     :: ![String]
       , constraints :: !Constraint
       , values      :: ![String]
       , deps        :: ![(String, String)]
       , ctorEnv     :: !DataConEnv
       } deriving (Show)

-- instance Default GenState where
--   def = GS def def def def def def def

initGS env = GS def def def def def def env

type DataConEnv = [(String, BareType)]

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
       constrain $ pAnd [ PNot $ pAnd [x, y] | [x, y] <- filter ((==2) . length) $ subsequences cs ]
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
  test :: a -> Int -> BareType -> Gen ()

instance (Show a, Constrain a, Constrain b, Show b) => Testable (a -> b) where
  test f d (RFun x i o r) = do
    a <- gen (undefined :: a) d i
    vals <- take 10 <$> allSat [symbol a]
    -- build up the haskell value
    (xvs :: [a]) <- forM vals $ \ vs -> do
      setValues vs
      stitch d
    io $ print xvs
    io $ forM_ xvs $ \xv -> do
      r <- evaluate (f xv)
      -- TODO: CONVERT `xv' TO `Expr' and symbolically evaluate
      print $ evalReft (M.fromList [(show x, toExpr xv)]) (toReft $ rt_reft o) (toExpr r)
      --undefined

instance (Show a, Show b, Constrain a, Constrain b, Constrain c) => Testable (a -> b -> c) where
  test f d (RFun xa ta (RFun xb tb to _) _) = do
    a <- gen (undefined :: a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (undefined :: b) d tb'
    vals <- take 10 <$> allSat [symbol a, symbol b]
    -- build up the haskell value
    (xvs :: [(a,b)]) <- forM vals $ \ vs -> do
      setValues vs
      b <- stitch d
      a <- stitch d
      return (a,b)
    io $ forM_ xvs $ \(a,b) -> do
      print (a,b)
      r <- evaluate (f a b)
      -- TODO: CONVERT `xv' TO `Expr' and symbolically evaluate
      print $ evalReft (M.fromList [(show xa, toExpr a),(show xb, toExpr b)]) (toReft $ rt_reft to) (toExpr r)
      --undefined

allSat :: [Symbol] -> Gen [[String]]
allSat roots = setup >>= go 10
  where
    setup = do
       ctx <- io $ makeContext Z3
       -- declare sorts
       io $ smtWrite ctx "(define-sort CHOICE () Bool)"
       -- declare variables
       vs <- gets variables
       mapM_ (\ x      -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       -- should be part of type class..
       io $ command ctx $ Declare (stringSymbol "len") [listsort] FInt
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
           let cs = myTrace "refuted" $ refute roots model deps vs
           io $ command ctx $ Assert $ PNot $ pAnd cs
           (map snd model:) <$> go (n-1) (ctx,vs,deps)

    -- refute model vs = let equiv = map (map fst) . filter ((>1) . length) . groupBy ((==) `on` snd) . sortBy (comparing snd) $ model
    --                   in [var x `eq` (ESym $ SL v) | (x,v) <- model, x `elem` unints vs]
    unints vs = [symbol v | (v,t) <- vs, t `elem` interps]
    interps   = [FInt, boolsort, choicesort]
    refute roots model deps vs = let realized = myTrace "realized" $ concat [reaches root model deps | root <- roots]
                                 in [var x `eq` (ESym $ SL v) | (x,v) <- realized, x `elem` unints vs]

--makeChecker1 :: (a -> b) -> BareType -> (a -> IO Bool)
makeChecker1 f t a = check1 r (x,a) rt
  where
    ([x],_,rt) = bkArrowDeep t
    r = f a

-- makeChecker2 :: (a -> b -> c) -> BareType -> (a -> b -> IO Bool)
-- makeChecker2 f t = \a b -> let r = f a b in check r t

-- makeChecker3 :: (a -> b -> c -> d) -> BareType -> (a -> b -> c -> IO Bool)
-- makeChecker3 f t = \a b c -> let r = f a b c in check r t

--check :: a -> BareType -> IO Bool
check1 x (sa,a) t
  = do v <- evaluate (Right x) `catch` \(_ :: SomeException) -> return $ Left "CRASH"
       b <- evaluate (evalReft undefined (toReft t) x)
            `catch` \(_ :: SomeException) -> return False
       let k = if b
               then "SAFE" :: String
               else "UNSAFE"
       printf "%s:\tx = %d, f x = %s\n" k (show x) (show v)


evalReft :: M.HashMap String Expr -> Reft -> Expr -> Bool
evalReft m (Reft (S v, rs)) x = and [ evalPred p (M.insert v x m)
                                    | RConc p <- rs
                                    ]

evalPred PTrue           m = True
evalPred PFalse          m = False
evalPred (PAnd ps)       m = and [evalPred p m | p <- ps]
evalPred (POr ps)        m = or  [evalPred p m | p <- ps]
evalPred (PNot p)        m = not $ evalPred p m
evalPred (PImp p q)      m = undefined
evalPred (PIff p q)      m = undefined
evalPred (PBexp e)       m = undefined -- ofExpr e
evalPred (PAtom b e1 e2) m = evalBrel b (evalExpr e1 m) (evalExpr e2 m)
evalPred (PAll ss p)     m = undefined
evalPred PTop            m = undefined

evalBrel Eq = (==)
evalBrel Ne = (/=)
evalBrel Gt = (>)
evalBrel Ge = (>=)
evalBrel Lt = (<)
evalBrel Le = (<=)

applyMeasure :: Measure BareType LocSymbol -> Expr -> M.HashMap String Expr -> Expr
applyMeasure m (EApp c xs) env = evalExpr e' env
  where
    eq = fromJust $ find ((==c) . ctor) $ -- myTrace ("eqns: " ++ show c ) $
         eqns m
    (E e) = body eq
    e' = subst (mkSubst $ zip (binds eq) xs) e
applyMeasure m e           env = error $ printf "applyMeasure(%s, %s)" (showpp m) (showpp e)

evalExpr :: Expr -> M.HashMap String Expr -> Expr
evalExpr (ECon i)       m = ECon i
evalExpr (EVar x)       m = m M.! showpp x
evalExpr (EBin b e1 e2) m = evalBop b (evalExpr e1 m) (evalExpr e2 m)
evalExpr (EApp f es)    m
  | val f == S "len"      = applyMeasure specs (evalExpr (head es) m) m
  | otherwise             = EApp f $ map (flip evalExpr m) es

evalBop Plus (ECon (I x)) (ECon (I y)) = ECon . I $ x + y
evalBop b    e1           e2           = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)

-- fromPred :: Pred -> M.HashMap String Integer -> Bool
fromPred PTrue           m = True
fromPred PFalse          m = False
fromPred (PAnd ps)       m = and [fromPred p m | p <- ps]
fromPred (POr ps)        m = or  [fromPred p m | p <- ps]
fromPred (PNot p)        m = not $ fromPred p m
fromPred (PImp p q)      m = undefined
fromPred (PIff p q)      m = undefined
fromPred (PBexp e)       m = undefined -- ofExpr e
fromPred (PAtom b e1 e2) m = fromBrel b (fromExpr e1 m) (fromExpr e2 m)
fromPred (PAll ss p)     m = undefined
fromPred PTop            m = undefined

fromBrel Eq = (==)
fromBrel Ne = (/=)
fromBrel Gt = (>)
fromBrel Ge = (>=)
fromBrel Lt = (<)
fromBrel Le = (<=)

fromExpr (EVar (S s))   m = m M.! s
fromExpr (EBin b e1 e2) m = fromBop b (fromExpr e1 m) (fromExpr e2 m)
fromExpr (ECon (I i))   m = i

fromBop Plus  = (+)
fromBop Minus = (-)
fromBop Times = (*)
fromBop Div   = div
fromBop Mod   = mod

toPred (RConc p) = p

-- type family Args a

-- type instance Args (a -> b) = a
-- type instance Args (a -> b -> c) = (a,b)

-- class Checkable a where
--   type Args a
--   makeChecker :: a -> BareType -> (Args a -> Bool)

-- instance Checkable (a -> b) where
--   type Args (a -> b) = a
--   makeChecker f t = \x -> let r = f x in check r t

-- instance Checkable (a -> b -> c) where
--   type Args (a -> b -> c) = (a,b)
--   makeChecker f t = \(a,b) -> let r = f a b in check r t

-- class Checkable fun args | fun -> args where
--   makeChecker :: fun -> BareType -> (args -> Bool)

-- instance Checkable (a -> b) a where
--   makeChecker f t = \a -> let r = f a in check r t

-- instance Checkable (a -> b -> c) (a,b) where
--   makeChecker f t = \(a,b) -> let r = f a b in check r t

--instance Checkable

-- instance (Constrain a, Constrain b) => Testable (a -> b) where
--   test x _ = error "WTF"

class Constrain a where
  gen    :: a -> Int -> BareType -> Gen String
  stitch :: Int -> Gen a
  toExpr :: a -> Expr
  sorts  :: a -> [Sort]
  ctors  :: a -> [Variable]

instance Constrain Int where
  gen _ _  (RApp _ [] _ r) = fresh [] FInt >>= \x ->
    do constrain $ ofReft x (toReft r)
       return x
  stitch _                 = read <$> pop
  toExpr i = ECon $ I $ fromIntegral i
  sorts _                  = []
  ctors _                  = []

instance (Constrain a) => Constrain [a] where
  gen _ 0 t = gen_nil t
  gen _ d t@(RApp c [ta] ps r)
    = do let t' = RApp c [ta] ps mempty
         x1 <- gen_nil t' -- (undefined :: [a]) (d-1) t
         x2 <- gen_cons (undefined :: [a]) d t'
         x3 <- freshChoose [x1,x2] listsort
         constrain $ ofReft x3 (toReft r)
         return x3

  stitch 0 = stitch_nil
  stitch d = do [c,n] <- popChoices 2
                pop  -- the "actual" list, but we don't care about it
                cc    <- stitch_cons d
                nn    <- stitch_nil
                -- io $ print (n,c)
                case (n,c) of
                  (True,_) -> return nn
                  (_,True) -> return cc

  toExpr []     = app  (stringSymbol "[]") -- (show '[])
                       []
  toExpr (x:xs) = app (stringSymbol ":") -- (show '(:))
                       [toExpr x, toExpr xs]
  ctors _ = [ ("nil", listsort)
            , ("cons", FFunc 2 [FInt, listsort, listsort])
            ] ++ ctors (undefined :: a)
  sorts _ = [listsort] ++ sorts (undefined :: a)

gen_nil (RApp _ _ _ _)
  = make '[] [] listsort

stitch_nil
  = do pop >> return []

gen_cons :: forall a. Constrain a => [a] -> Int -> BareType -> Gen String
gen_cons _ n t@(RApp c [ta] [p] r)
  = do x  <- gen (undefined :: a) (n-1) ta
       let ta' = applyRef p [x] ta
       let t'  = RApp c [ta'] [p] r
       xs <- gen (undefined :: [a]) (n-1) t'
       make '(:) [x,xs] listsort

stitch_cons :: Constrain a => Int -> Gen [a]
stitch_cons d
  = do z  <- pop
       xs <- stitch (d-1)
       x  <- stitch (d-1)
       return (x:xs)

ofReft :: String -> Reft -> Pred
ofReft s (Reft (v, rs))
  = let x = mkSubst [(v, var s)]
    in pAnd [subst x p | RConc p <- rs]

infix 4 `eq`
eq  = PAtom Eq
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


--------------------------------------------------------------------------------
--- test data
--------------------------------------------------------------------------------

t :: BareType
t = rr "{v:[{v0:Int | (v0 >= 0 && v0 < 5)}]<{\\h t -> h < t}> | (len v) >= 3}"

t' :: BareType
t' = rr "{v:[{v0:Int | (v0 >= 0 && v0 < 6)}] | true}"


i :: BareType
i = rr "{v:Int | v > 0}"

list :: [Int]
list = []

inT :: Int
inT = 0

tree :: Tree Int
tree = Leaf

tt :: BareType
tt = rr "{v:Tree <{\\r x -> x < r}, {\\r y -> r < y}> {v0 : Int | (v0 >= 0 && v0 < 16)} | (size v) > 0}"

specs :: Measure BareType LocSymbol
specs = rr $ unlines [ "len :: [a] -> Int"
                     , "len ([])   = 0"
                     , "len (x:xs) = 1 + len(xs)"

                -- , "measure size :: Tree a -> Int"
                -- , "size (Leaf)       = 0"
                -- , "size (Node x l r) = 1 + size(l) + size(r)"
                ]

nilT  = rr "{v:[a] | (len v) = 0}"
consT = rr "x:a -> xs:[a] -> {v:[a] | (len v) = 1 + (len xs)}"
env :: DataConEnv
env = [("GHC.Types.[]",nilT),("GHC.Types.:",consT)]

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

  ctors _ = [ ("leaf", treesort)
            , ("node", FFunc 3 [FInt, treesort, treesort, treesort])
            ] ++ ctors (undefined :: a)
  sorts _ = [treesort] ++ sorts (undefined :: a)

gen_leaf _
  = make 'Leaf [] treesort

stitch_leaf = pop >> return Leaf

gen_node :: Constrain a => Tree a -> Int -> BareType -> Gen String
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


-- applyRef :: Ref -> [Variable] -> RType
applyRef (RPoly xs p) vs t
  = t `strengthen` r
  where
    r  = subst su $ rt_reft p
    su = mkSubst [(fst x, var v) | x <- xs | v <- vs]


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
