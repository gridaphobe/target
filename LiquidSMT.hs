{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
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
{- LANGUAGE TemplateHaskell #-}

module LiquidSMT where

import           Control.Applicative
import           Control.Arrow hiding (app)
import           Control.Exception.Base
import           Control.Monad.State
import           Data.Char
import           Data.Default
import           Data.Function
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import           Data.List hiding (sort)
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.Proxy
import           Data.String
import qualified Data.Text.Lazy as T
import qualified Data.Vector as V
import           Debug.Trace
import           GHC
import           Name
import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Names
import           Language.Fixpoint.Parse
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types hiding (prop, Def)
import           Language.Haskell.Liquid.CmdLine
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.GhcMisc
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types hiding (var, env)
import qualified Language.Haskell.TH as TH
import           System.Exit
import           System.IO.Unsafe
import           Text.PrettyPrint.HughesPJ hiding (first)
import           Text.Printf

import           GHC.Generics
import           Generics.Deriving.ConNames
io = liftIO


reaches root model deps = go root
  where
    go root
      | isChoice && taken
      = (root,val) `V.cons` V.concatMap go (reached deps) -- [r | (x,r) <- deps, x == root]
      | isChoice
      = V.fromList [(root,val)]
      | otherwise
      = (root,val) `V.cons` V.concatMap go (reached deps) -- [r | (x,r) <- deps, x == root]
      where
        val      = model M.! root
        isChoice = "CHOICE" `isPrefixOf` symbolString root
        taken    = val == "true"
        reached  = V.map snd . V.filter ((==root).fst)


myTrace s x = trace (s ++ ": " ++ show x) x

makeDecl :: Symbol -> Sort -> Command
makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        t

type Constraint = [Pred]
type Variable   = ( String -- the name
                  , Sort   -- the `Sort'
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
       , dconEnv     :: ![(String, DataConP)]
       , ctorEnv     :: !DataConEnv
       , measEnv     :: !MeasureEnv
       , tyconInfo   :: !(M.HashMap TyCon RTyCon)
       , constrs     :: ![(String, String)]
       , modName     :: !String
       } deriving (Show)

initGS sp = GS def def def def def def dcons sigs (measures sp) tyi free ""
  where
    dcons = map (showpp *** id) (dconsP sp)
    sigs  = map (showpp *** val) (ctors sp)
    tyi   = makeTyConInfo (tconsP sp)
    free  = map (showpp *** showpp) $ freeSyms sp

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
freshChoose [] sort = error "freshChoose"
freshChoose [x'] sort
  = do x <- fresh [] sort
       c <- freshChoice [x']
       constrain $ prop c `iff` var x `eq` var x'
       addDep x c
       constrain $ prop c
       return x
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


-- make :: TH.Name -> [String] -> Sort -> Gen String
make c vs s
  = do x  <- fresh vs s
       -- io $ print c
       t <- (safeFromJust "make" . lookup c) <$> gets ctorEnv
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
  test f d (stripQuals -> (RFun x i o r)) = do
    a <- gen (Proxy :: Proxy a) d i
    vals <- allSat [symbol a]
    -- build up the haskell value
    (xvs :: [a]) <- forM vals $ \ vs -> do
      setValues vs
      stitch d
    io $ print xvs
    forM_ xvs $ \xv -> do
      r <- io $ evaluate (f xv)
      io . print =<< evalReft (M.fromList [(show x, toExpr xv)]) (toReft $ rt_reft o) (toExpr r)

fourth4 (_,_,_,d) = d

stripQuals = snd . bkClass . fourth4 . bkUniv

instance (Constrain a, Constrain b, Constrain c) => Testable (a -> b -> c) where
  test f d (stripQuals -> (RFun xa ta (RFun xb tb to _) _)) = do
    a <- gen (Proxy :: Proxy a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (Proxy :: Proxy b) d tb'
    cts <- gets constrs
    vals <- allSat [symbol a, symbol b]
    -- build up the haskell value
    (xvs :: [(a,b)]) <- forM vals $ \ vs -> do
      setValues vs
      b <- stitch d
      a <- stitch d
      return (a,b)
    io $ print vals
    forM_ xvs $ \(a,b) -> do
      io $ print (a,b)
      r <- io $ evaluate (f a b)
      let env = map (second (flip app [])) cts ++ [(show xa, toExpr a),(show xb, toExpr b)]
      io . print =<< evalReft (M.fromList env) (toReft $ rt_reft to) (toExpr r)
  test f d t = error $ show t

allSat :: [Symbol] -> Gen [[String]]
allSat roots = setup >>= go
  where
    setup = do
       ctx <- io $ makeContext Z3
       -- declare sorts
       io $ smtWrite ctx "(define-sort CHOICE () Bool)"
       -- declare constructors
       cts <- gets constrs
       mapM_ (\ (_,c) -> io . command ctx $ Declare (symbol c) [] FInt) cts
       -- declare variables
       vs <- gets variables
       mapM_ (\ x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       ms <- gets measEnv
       mapM_ (\ m -> io . command ctx $ makeDecl (val $ name m) (rTypeSort mempty $ sort m)) ms
       cs <- gets constraints
       deps <- V.fromList . map (symbol *** symbol) <$> gets deps
       mapM_ (\c -> do {i <- gets seed; modify $ \s@(GS {..}) -> s { seed = seed + 1 };
                        io . command ctx $ Assert (Just i) c})
         cs
       return (ctx,vs,deps)

    go :: (Context, [(String,Sort)], V.Vector (Symbol,Symbol)) -> Gen [[String]]
    go (ctx,vs,deps) = do
       resp <- io $ command ctx CheckSat
       case resp of
         Error e -> error $ T.unpack e
         Unsat   -> io (cleanupContext ctx) >> return []
         Sat     -> do
           Values model <- io $ command ctx (GetValue $ map symbol vs)
           let cs = V.toList $ refute roots (M.fromList model) deps vs
           i <- gets seed
           modify $ \s@(GS {..}) -> s { seed = seed + 1 }
           io $ command ctx $ Assert (Just i) $ PNot $ pAnd cs
           (map snd model:) <$> go (ctx,vs,deps)

    ints vs = S.fromList [symbol v | (v,t) <- vs, t `elem` interps]
    interps = [FInt, boolsort, choicesort]
    refute roots model deps vs
      = V.map    (\(x,v) -> var x `eq` ESym (SL v))
      . V.filter (\(x,v) -> x `S.member` ints vs)
      $ realized
      where
        realized = V.concat $ map (\root -> reaches root model deps) roots


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
evalPred (PBexp e)       m = (==0) <$> evalExpr e m
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
applyMeasure m (EApp c xs) env = evalBody eq xs env
  where
    eq = safeFromJust "applyMeasure" $ find ((==val c) . symbol . show . ctor) $ eqns m
applyMeasure m e           env = error $ printf "applyMeasure(%s, %s)" (showpp m) (showpp e)

evalBody eq xs env = go $ body eq
  where
    go (E e) = evalExpr (subst su e) env
    go (P p) = evalPred (subst su p) env >>= \b -> return $ if b then 0 else 1
    su = mkSubst $ zip (binds eq) xs


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
evalExpr (EIte p e1 e2) m
  = do b <- evalPred p m
       if b
         then evalExpr e1 m
         else evalExpr e2 m
evalExpr e              m = error $ printf "evalExpr(%s)" (show e)

evalBop Plus (ECon (I x)) (ECon (I y)) = ECon . I $ x + y
evalBop b    e1           e2           = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)


class Show a => Constrain a where
  getType :: Proxy a -> String
  default getType :: (Generic a, GConstrain (Rep a))
                  => Proxy a -> String
  getType p = gtype (reproxy p :: Proxy (Rep a a))

  gen         :: Proxy a -> Int -> SpecType -> Gen String
  default gen :: (Generic a, GConstrain (Rep a))
              => Proxy a -> Int -> SpecType -> Gen String
  -- gen = undefined
  gen p = ggen (reproxy p :: Proxy (Rep a a))


  stitch :: Int -> Gen a
  default stitch :: (Generic a, GConstrain (Rep a)) => Int -> Gen a
  stitch d = to <$> gstitch d

  toExpr :: a -> Expr
  -- default toExpr :: (Generic a, GConstrain (Rep a)) => a -> Expr
  -- toExpr = gtoExpr . from

reproxyElem :: proxy (f a) -> Proxy a
reproxyElem = reproxy

instance Constrain Bool
instance Constrain a => Constrain [a]
-- instance (Constrain a, Constrain b) => Constrain (a,b)

class GConstrainSum f where
  ggenAlts      :: Proxy (f a) -> Int -> SpecType -> Gen [String]
  ggenAltsNoRec :: Proxy (f a) -> String -> SpecType -> Gen [String]

-- instance (Constructor c, GConstrain (C1 c U1), GConstrainSum g) => GConstrainSum ((C1 c U1) :+: g) where
--   ggenAlts p d t
--     = do x  <- ggen (reproxy p :: Proxy (C1 c U1 a)) d t
--          xs <- ggenAlts (reproxy p :: Proxy (g a)) d t
--          return $ x:xs
--   ggenAltsNoRec p d t
--     = do x  <- ggen (reproxy p :: Proxy (C1 c U1 a)) d t
--          io $ print x
--          xs <- ggenAltsNoRec (reproxy p :: Proxy (g a)) d t
--          return $ x:xs

instance (GConstrain f, GConstrainSum g) => GConstrainSum (f :+: g) where
  ggenAlts p d t
    = do x  <- ggen (reproxy p :: Proxy (f a)) d t
         xs <- ggenAlts (reproxy p :: Proxy (g a)) d t
         return $ x:xs
  ggenAltsNoRec p d t
    = do -- x  <- ggen (reproxy p :: Proxy (f a)) 0 t
         -- io $ print $ conName (undefined :: f a)
         -- myConName (reproxy p :: Proxy f)
         if gisRecursive (reproxy p :: Proxy (f a)) d
         then ggenAltsNoRec (reproxy p :: Proxy (g a)) d t
         else do
         x  <- ggen (reproxy p :: Proxy (f a)) 0 t
         xs <- ggenAltsNoRec (reproxy p :: Proxy (g a)) d t
         return $ x:xs

-- myConName :: (Constructor c, GConstrain f) => Proxy (C1 c f) -> Gen ()
-- myConName p = io $ print $ conName (undefined :: C1 c f a)

instance (Constructor c, GConstrainProd f) => GConstrainSum (C1 c f) where
  ggenAlts p d t
    = do x <- ggen p d t
         return [x]
  ggenAltsNoRec p d t
    = if gisRecursive p d
      then return []
      else do
      x <- ggen p 0 t
      return [x]

class GConstrainProd f where
  gconArgTys :: Proxy (f a) -> [String]
  ggenArgs :: Proxy (f a) -> Int -> [(Symbol,SpecType)] -> Gen [String]

instance (GConstrain f, GConstrainProd g) => GConstrainProd (f :*: g) where
  gconArgTys p = gtype (reproxy p :: Proxy (f a)) : gconArgTys (reproxy p :: Proxy (g a))
  ggenArgs (p :: Proxy ((f :*: g) a)) d (t:ts)
    = do x  <- ggen (reproxy p :: Proxy (f a)) (d-1) (snd t)
         let su = mkSubst [(fst t, var x)]
         xs <- ggenArgs (reproxy p :: Proxy (g a)) d (map (second (subst su)) ts)
         return $ x:xs

instance (GConstrain f) => GConstrainProd (S1 c f) where
  gconArgTys p = [gtype (reproxy p :: Proxy (f a))]
  ggenArgs (p :: Proxy (S1 c f a)) d [t]
    = do x <- ggen (reproxy p :: Proxy (f a)) (d-1) (snd t)
         return [x]

instance GConstrainProd U1 where
  gconArgTys p = []
  ggenArgs (p :: Proxy (U1 a)) d []
    = do x <- fresh [] FInt
         return [x]

instance (Constrain f, GConstrain (Rep f)) => GConstrainProd (K1 i f) where
  gconArgTys p = [gtype (reproxy p :: Proxy (Rep f f))]
  ggenArgs (p :: Proxy (K1 i f a)) d [t]
    = do x <- gen (reproxy p :: Proxy f) (d-1) (snd t)
         return [x]

class GConstrain f where
  gisRecursive :: Proxy (f a) -> String -> Bool
  gtype        :: Proxy (f a) -> String
  ggen         :: Proxy (f a) -> Int    -> SpecType -> Gen String
  ggenNoRec    :: Proxy (f a) -> String -> SpecType -> Gen String
  gstitch      :: Int -> Gen (f a)
  -- gtoExpr :: f a -> Expr
  -- gtoExprs :: f a -> [Expr]

instance GConstrain U1 where
  ggen p d t = fresh [] FInt
  ggenNoRec p d t = fresh [] FInt
  gstitch _  = pop >> return U1
  -- gtoExpr c  = error "U1" --app (symbol $ conName c) []
  -- gtoExprs _ = []

-- instance (GConstrain a, GConstrain b) => GConstrain (a :*: b) where
--   ggen p d t
--     = error "*" --do xs 
  -- gstitch d  = undefined
  -- gtoExpr (a :*: b)  = error ":*:"
  -- gtoExprs (a :*: b)  = gtoExprs a ++ gtoExprs b

instance (GConstrain f, GConstrainSum g) => GConstrain (f :+: g) where
  ggenNoRec p d t
    = do xs <- ggenAltsNoRec p d t
         -- io $ print xs
         x  <- freshChoose xs FInt
         constrain $ ofReft x $ toReft $ rt_reft t
         return x
  ggen p d t
    = do xs <- ggenAlts p d t
         x  <- freshChoose xs FInt
         constrain $ ofReft x $ toReft $ rt_reft t
         return x
  gstitch d  = error ":+:"
  -- gtoExpr c@(L1 x) = gtoExpr x -- app (symbol $ conName c) [gtoExpr x]
  -- gtoExpr c@(R1 x) = gtoExpr x -- app (symbol $ conName x) [gtoExpr x]
  -- gtoExprs (L1 x) = error "L1" -- gtoExprs x
  -- gtoExprs (R1 x) = error "R1" -- gtoExprs x

instance (Constructor c, GConstrainProd f) => GConstrain (C1 c f) where
  gisRecursive p t = myTrace ("gisRecursive " ++ cn) $ any (==t) (gconArgTys (reproxy p :: Proxy (f a)))
    where cn = conName (undefined :: C1 c f a)
  ggen p d t
    = do let cn = conName (undefined :: C1 c f a)
         mod <- gets modName
         -- io $ print (mod,cn)
         dcp <- safeFromJust "ggen" . lookup (mod++"."++cn) <$> gets ctorEnv
         tyi <- gets tyconInfo
         let ts = applyPreds (expandRApp (M.fromList []) tyi t) dcp
         -- io $ print ts
         xs  <- ggenArgs (reproxy p :: Proxy (f a)) d ts
         make (mod++"."++cn) xs FInt
  gstitch d  = error "C1"
  -- gtoExpr c@(M1 x)  = app (symbol $ conName c) (gtoExprs x)
  -- gtoExprs _ = error "C1"

instance (Datatype c, GConstrain f) => GConstrain (D1 c f) where
  gtype p = qualifiedDatatypeName (undefined :: D1 c f a)
  ggen (p :: Proxy (D1 c f a)) 0 t
    = inModule mod $ ggenNoRec (reproxy p :: Proxy (f a)) ty t
    where
      ty
        = mod ++ "." ++ datatypeName (undefined :: D1 c f a)
      mod
        = GHC.Generics.moduleName (undefined :: D1 c f a)
      inModule m act
        = do m' <- gets modName
             modify $ \s -> s { modName = m }
             r <- act
             modify $ \s -> s { modName = m' }
             return r
  ggen (p :: Proxy (D1 c f a)) d t
    = inModule mod $ ggen (reproxy p :: Proxy (f a)) d t
    where
      mod
        = GHC.Generics.moduleName (undefined :: D1 c f a)
      inModule m act
        = do m' <- gets modName
             modify $ \s -> s { modName = m }
             r <- act
             modify $ \s -> s { modName = m' }
             return r
  gstitch d  = error "D1"
  -- gtoExpr c@(M1 x) = app (symbol $ GHC.Generics.moduleName c ++ "." ++ (show $ val d)) xs
  --   where
  --     (EApp d xs) = gtoExpr x -- app (symbol $ conName c) (gtoExprs x)
  -- gtoExprs (M1 c)  = error "D1"

instance (GConstrain f) => GConstrain (S1 c f) where
  gtype p    = gtype (reproxy p :: Proxy (f a))
  ggen p d t = ggen (reproxy p :: Proxy (f a)) d t
  gstitch d  = error "S1"
  -- gtoExpr (M1 c)  = gtoExpr c -- app (symbol $ conName c) []
  -- gtoExprs (M1 c) = gtoExprs c

instance (Constrain a) => GConstrain (K1 i a) where
  gtype p    = getType (reproxy p :: Proxy a) --gtype (reproxy p :: Proxy (Rep a a))
  ggen p d t = gen (reproxy p :: Proxy a) d t
  gstitch d  = error "K1"
  -- gtoExpr  (K1 x) = toExpr x
  -- gtoExprs (K1 x) = [toExpr x]

-- getType a = qualifiedDatatypeName $ from a

-- isRec :: Datatype c => D1 c f a -> Bool
isRec d@(M1 x) = any (==me) $ gtypes x
  where
    me = qualifiedDatatypeName d

class Foo f where
  gtypes :: f a -> [String]
  ggetType :: f a -> String

instance Datatype c => Foo (D1 c f) where
  ggetType d = qualifiedDatatypeName d

instance Foo U1 where
  gtypes _ = []

instance Foo f => Foo (C1 c f) where
  gtypes (_::(C1 c f a)) = gtypes (undefined :: f a)

instance (Foo f, Foo g) => Foo (f :*: g) where
  gtypes (_::(f :*: g)a) = ggetType (undefined :: f a) : gtypes (undefined :: g a)
-- types ((M1 (K1 f)) :*: g) = qualifiedDatatypeName f : types g

instance (Foo f, Foo g) => Foo (f :+: g) where
  -- gtypes _ = gtypes (undefined :: g a)
  gtypes (L1 x) = gtypes x
  gtypes (R1 x) = gtypes x

instance Foo f => Foo (S1 c f) where
  ggetType (_::S1 c f a) = ggetType (undefined :: f a)
  gtypes (_::S1 c f a) = gtypes (undefined :: f a)

instance (Generic a, Foo (Rep a)) => Foo (K1 i a) where
  ggetType (_::K1 i a a1) = ggetType (undefined :: Rep a a1)
  gtypes (_::K1 i a a1) = [ggetType (undefined :: Rep a a1)]


-- instance (Generic a) => Foo (K1 i a) where
--   getType (K1 x) = qualifiedDatatypeName $ from x

qualifiedDatatypeName d = GHC.Generics.moduleName d ++ "." ++ datatypeName d

instance Constrain () where
  gen _ _ _ = fresh [] FInt
  stitch _  = return ()
  toExpr _  = app (stringSymbol "()") []

instance Constrain Int where
  gen _ d t = fresh [] FInt >>= \x ->
    do constrain $ ofReft x (toReft $ rt_reft t)
       -- use the unfolding depth to constrain the range of Ints, like QuickCheck
       constrain $ var x `ge` (0 - fromIntegral 5)
       constrain $ var x `le` fromIntegral 5
       return x
  stitch _ = read <$> pop
  toExpr i = ECon $ I $ fromIntegral i

-- instance (Constrain a) => Constrain [a] where
--   gen _ 0 t = gen_nil t
--   gen p d t@(RApp c [ta] ps r)
--     = do let t' = RApp c [ta] ps mempty
--          x1 <- gen_nil t'
--          x2 <- gen_cons p d t'
--          x3 <- freshChoose [x1,x2] listsort
--          constrain $ ofReft x3 (toReft r)
--          return x3

--   stitch 0 = stitch_nil
--   stitch d = do [c,n] <- popChoices 2
--                 pop  -- the "actual" list, but we don't care about it
--                 cc    <- stitch_cons d
--                 nn    <- stitch_nil
--                 case (n,c) of
--                   (True,_) -> return nn
--                   (_,True) -> return cc

--   toExpr []     = app (stringSymbol "[]") -- (show '[])
--                       []
--   toExpr (x:xs) = app (stringSymbol ":") -- (show '(:))
--                       [toExpr x, toExpr xs]

-- gen_nil (RApp _ _ _ _)
--   = make "GHC.Types.[]" [] listsort

-- stitch_nil
--   = do pop >> return []

-- gen_cons :: forall a. Constrain a => Proxy [a] -> Int -> SpecType -> Gen String
-- gen_cons p d t@(RApp c [ta] ps r)
--   = make2 "GHC.Types.:" (reproxyElem p, p) t listsort d
-- gen_cons _ _ t = error $ show t

-- stitch_cons :: Constrain a => Int -> Gen [a]
-- stitch_cons d
--   = do z  <- pop
--        xs <- stitch (d-1)
--        x  <- stitch (d-1)
--        return (x:xs)


-- make2 :: forall a b. (Constrain a, Constrain b)
--       => TH.Name -> (Proxy a, Proxy b) -> SpecType -> Sort -> Int -> Gen String
make2 c (pa,pb) t s d
  = do dcp <- fromJust . lookup c <$> gets ctorEnv
       tyi <- gets tyconInfo
       let [t1,t2] = applyPreds (expandRApp (M.fromList []) tyi t) dcp
       x1 <- gen pa (d-1) (snd t1)
       let su = mkSubst [(fst t1, var x1)]
       x2 <- gen pb (d-1) (subst su $ snd t2)
       make c [x1,x2] s

-- make3 :: forall a b c. (Constrain a, Constrain b, Constrain c)
--       => TH.Name -> (Proxy a, Proxy b, Proxy c) -> SpecType -> Sort -> Int -> Gen String
make3 c (pa,pb,pc) t s d
  = do dcp <- fromJust . lookup c <$> gets ctorEnv
       tyi <- gets tyconInfo
       let [t1,t2,t3] = applyPreds (expandRApp (M.fromList []) tyi t) dcp
       x1 <- gen pa (d-1) (snd t1)
       let su = mkSubst [(fst t1, var x1)]
       x2 <- gen pb (d-1) (subst su $ snd t2)
       let su = mkSubst [(fst t1, var x1),(fst t2, var x2)]
       x3 <- gen pc (d-1) (subst su $ snd t3)
       make c [x1,x2,x3] s

make4 c (p1,p2,p3,p4) t s d
  = do dcp <- fromJust . lookup c <$> gets ctorEnv
       tyi <- gets tyconInfo
       let [t1,t2,t3,t4] = applyPreds (expandRApp (M.fromList []) tyi t) dcp
       x1 <- gen p1 (d-1) (snd t1)
       let su = mkSubst [(fst t1, var x1)]
       x2 <- gen p2 (d-1) (subst su $ snd t2)
       let su = mkSubst [(fst t1, var x1),(fst t2, var x2)]
       x3 <- gen p3 (d-1) (subst su $ snd t3)
       let su = mkSubst [(fst t1, var x1),(fst t2, var x2),(fst t3, var x3)]
       x4 <- gen p4 (d-1) (subst su $ snd t4)
       make c [x1,x2,x3,x4] s

make5 c (p1,p2,p3,p4,p5) t s d
  = do dcp <- fromJust . lookup c <$> gets ctorEnv
       tyi <- gets tyconInfo
       let [t1,t2,t3,t4,t5] = applyPreds (expandRApp (M.fromList []) tyi t) dcp
       x1 <- gen p1 (d-1) (snd t1)
       let su = mkSubst [(fst t1, var x1)]
       x2 <- gen p2 (d-1) (subst su $ snd t2)
       let su = mkSubst [(fst t1, var x1),(fst t2, var x2)]
       x3 <- gen p3 (d-1) (subst su $ snd t3)
       let su = mkSubst [(fst t1, var x1),(fst t2, var x2),(fst t3, var x3)]
       x4 <- gen p4 (d-1) (subst su $ snd t4)
       let su = mkSubst [(fst t1, var x1),(fst t2, var x2),(fst t3, var x3),(fst t4, var x4)]
       x5 <- gen p5 (d-1) (subst su $ snd t5)
       make c [x1,x2,x3,x4,x5] s

-- applyPreds :: SpecType -> DataConP -> [SpecType]
applyPreds sp dc = zip xs (map tx ts)
  where
    (as, ps, _, t) = bkUniv dc
    (xs, ts, rt)   = bkArrow . snd $ bkClass t
    -- args  = reverse tyArgs
    su    = [(tv, toRSort t, t) | tv <- as | t <- rt_args sp]
    sup   = [(p, r) | p <- ps | r <- rt_pargs sp]
    tx    = (\t -> replacePreds "applyPreds" t sup) . onRefs (monosToPoly sup) . subsTyVars_meet su

onRefs f t@(RVar _ _) = t
onRefs f t = t { rt_pargs = f <$> rt_pargs t}

monosToPoly su r = foldr monoToPoly r su

monoToPoly (p, r) (RMono _ (U _ (Pr [up]) _))
  | pname p == pname up
  = r
monoToPoly _ m = m


-- apply4 :: (Constrain a, Constrain b, Constrain c, Constrain d)
--        => (a -> b -> c -> d -> e) -> Int -> Gen e
apply4 c d
  = do pop
       c <$> cons <*> cons <*> cons <*> cons
  where
    cons :: Constrain a => Gen a
    cons = stitch (d-1)

data Tree a = Leaf | Node a (Tree a) (Tree a) deriving (Eq, Ord, Show, Generic)

treesort = FObj $ stringSymbol "Int"

treeList Leaf = []
treeList (Node x l r) = treeList l ++ [x] ++ treeList r

instance Constrain a => Constrain (Tree a) where
  gen _ 0 t = gen_leaf t
  gen p d t@(RApp c [ta] ps r)
    = do let t' = RApp c [ta] ps mempty
         l <- gen_leaf t'
         n <- gen_node p d t'
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

  toExpr Leaf         = app (stringSymbol "LiquidSMT.Leaf") []
  toExpr (Node x l r) = app (stringSymbol "LiquidSMT.Node") [toExpr x, toExpr l, toExpr r]

gen_leaf _
  = make "LiquidSMT.Leaf" [] treesort

stitch_leaf = pop >> return Leaf

gen_node :: forall a. Constrain a => Proxy (Tree a) -> Int -> SpecType -> Gen String
gen_node p d t@(RApp _ _ _ _)
  -- = do x <- gen (Proxy :: Proxy a) (d-1) ta
  --      let tal = applyRef pl [x] ta
  --      let tl  = RApp c [tal] [pl,pr] r
  --      let tar = applyRef pr [x] ta
  --      let tr  = RApp c [tar] [pl,pr] r
  --      nl <- gen p (d-1) tl
  --      nr <- gen p (d-1) tr
  --      make 'Node [x,nl,nr] treesort
  = make3 "LiquidSMT.Node" (reproxyElem p, p, p) t treesort d

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
       let ty = val $ safeFromJust "testOne" $ lookup (name) $ map (first showpp) $ tySigs sp
       runGen sp $ test f 2 ty

-- mkTest :: TH.Name -> TH.ExpQ
-- mkTest f = do loc <- TH.location
--               let name = show f
--                   file = TH.loc_filename loc
--               [| testOne $(TH.varE f) $(TH.stringE name) $(TH.stringE file) |]

-- mytake :: Int -> [a] -> [a]
-- mytake 0 xs     = xs
-- mytake _ []     = []
-- mytake n (x:xs) = x : mytake (n-1) xs


safeFromJust msg Nothing  = error msg
safeFromJust msg (Just x) = x

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
