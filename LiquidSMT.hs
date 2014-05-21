{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE BangPatterns #-}
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
{-# LANGUAGE LambdaCase #-}
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
import           Data.Text.Format hiding (print)
import qualified Data.Text.Lazy as T
import qualified Data.Vector as V
import           Debug.Trace
import           GHC hiding (Failed)
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
import           Language.Haskell.Liquid.Types hiding (var, env, Result(..))
import qualified Language.Haskell.TH as TH
import           System.Exit
import           System.FilePath
import           System.IO.Unsafe
import           Text.PrettyPrint.HughesPJ hiding (first)
import           Text.Printf

import           GHC.Generics
import           Generics.Deriving.ConNames

import           Encoding (zDecodeString)


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


listsort = FObj $ stringSymbol "GHC.Types.List"
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
       , freesyms    :: ![(String,String)]
       , constructors :: ![Variable] -- (S.HashSet Variable)  --[(String, String)]
       , sigs        :: ![(String, SpecType)]
       , depth       :: !Int
       , chosen      :: !(Maybe String)
       , sorts       :: !(S.HashSet T.Text)
       , modName     :: !String
       , makingTy    :: !Sort
       } deriving (Show)

initGS sp = GS def def def def def def dcons cts (measures sp) tyi free [] sigs def Nothing S.empty "" FInt
  where
    dcons = map (showpp *** id) (dconsP sp)
    cts   = map (showpp *** val) (ctors sp)
    tyi   = makeTyConInfo (tconsP sp)
    free  = map (showpp *** showpp) $ freeSyms sp
    sigs  = map (showpp *** val) $ tySigs sp

type DataConEnv = [(String, SpecType)]
type MeasureEnv = [Measure SpecType DataCon]

setValues vs = modify $ \s@(GS {..}) -> s { values = vs }

addDep from to = modify $ \s@(GS {..}) -> s { deps = (from,to):deps }

addConstraint p = modify $ \s@(GS {..}) -> s { constraints = p:constraints }

addConstructor c
  = do -- modify $ \s@(GS {..}) -> s { constructors = S.insert c constructors }
       modify $ \s@(GS {..}) -> s { constructors = nub $ c:constructors }

inModule m act
  = do m' <- gets modName
       modify $ \s -> s { modName = m }
       r <- act
       modify $ \s -> s { modName = m' }
       return r

making ty act
  = do ty' <- gets makingTy
       modify $ \s -> s { makingTy = ty }
       r <- act
       modify $ \s -> s { makingTy = ty' }
       return r

withFreshChoice act
  = do c  <- freshChoice []
       mc <- gets chosen
       modify $ \s -> s { chosen = Just c }
       x  <- act
       modify $ \s -> s { chosen = mc }
       addDep c x
       return (x,c)

-- | `fresh` generates a fresh variable and encodes the reachability
-- relation between variables, e.g. `fresh xs sort` will return a new
-- variable `x`, from which everything in `xs` is reachable.
fresh :: [String] -> Sort -> Gen String
fresh xs sort
  = do n <- gets seed
       modify $ \s@(GS {..}) -> s { seed = seed + 1 }
       modify $ \s@(GS {..}) -> s { sorts = S.insert (smt2 sort) sorts }
       let x = (zDecodeString $ T.unpack (smt2 sort)) ++ show n
       modify $ \s@(GS {..}) -> s { variables = (x,sort) : variables }
       mapM_ (addDep x) xs
       return x

freshChoice :: [String] -> Gen String
freshChoice xs
  = do c <- fresh xs choicesort
       modify $ \s@(GS {..}) -> s { choices = c : choices }
       return c

choicesort = FObj $ stringSymbol "CHOICE"

freshChoose :: [(String,String)] -> Sort -> Gen String
freshChoose xcs sort
  = do x' <- fresh [] sort
       cs <- forM xcs $ \(x,c) -> do
               constrain $ prop c `iff` var x `eq` var x'
               addDep x' c
               return $ prop c
       constrain $ pOr cs
       constrain $ pAnd [ PNot $ pAnd [x, y]
                        | [x, y] <- filter ((==2) . length) $ subsequences cs ]
       return x'

-- make :: TH.Name -> [String] -> Sort -> Gen String
make c vs s
  = do x  <- fresh vs s
       t <- (safeFromJust "make" . lookup c) <$> gets ctorEnv
       let (xs, _, rt) = bkArrowDeep t
           su          = mkSubst $ zip (map symbol xs) (map var vs)
       addConstructor (c, rTypeSort mempty t)
       addConstraint $ var x `eq` app c (map var vs)
       constrain $ ofReft x $ subst su $ toReft $ rt_reft rt
       return x

constrain :: Pred -> Gen ()
constrain p
  = do mc <- gets chosen
       case mc of
         Nothing -> addConstraint p
         Just c  -> let p' = prop c `imp` p
                    in addConstraint p'

pop :: Gen String
pop = do (v:vs) <- gets values
         modify $ \s@(GS {..}) -> s { values = vs }
         return v

popN :: Int -> Gen [String]
popN d = replicateM d pop

popChoice :: Gen Bool
popChoice = read <$> pop
  where
    read "true"  = True
    read "false" = False
    read e       = error $ "popChoice: " ++ e

popChoices :: Int -> Gen [Bool]
popChoices n = fmap read <$> popN n
  where
    read "true"  = True
    read "false" = False
    read e       = error $ "popChoices: " ++ e

data Result = Passed !Int
            | Failed !String
            deriving (Show)

class Testable a where
  test :: a -> Int -> SpecType -> Gen Result

instance (Constrain a, Constrain b) => Testable (a -> b) where
  test f d (stripQuals -> (RFun x i o _)) = do
    a <- gen (Proxy :: Proxy a) d i
    cts <- gets freesyms
    vals <- allSat [symbol a]
    -- build up the haskell value
    (xvs :: [a]) <- forM vals $ \ vs -> do
      setValues vs
      stitch d
    foldM (\case
              r@(Failed _) -> const $ return r
              (Passed n) -> \a -> do
                r <- io $ evaluate (f a)
                let env = map (second (`app` [])) cts ++ [(show x, toExpr a)]
                sat <- evalType (M.fromList env) o (toExpr r)
                case sat of
                  False -> return $ Failed $ show a
                  True  -> return $ Passed (n+1))
      (Passed 0) xvs
  test f d t = error $ show t


fourth4 (_,_,_,d) = d

stripQuals = snd . bkClass . fourth4 . bkUniv

instance (Constrain a, Constrain b, Constrain c) => Testable (a -> b -> c) where
  test f d (stripQuals -> (RFun xa ta (RFun xb tb to _) _)) = do
    a <- gen (Proxy :: Proxy a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (Proxy :: Proxy b) d tb'
    cts <- gets freesyms
    vals <- allSat [symbol a, symbol b]
    -- build up the haskell value
    (xvs :: [(a,b)]) <- forM vals $ \ vs -> do
      setValues vs
      !b <- stitch d
      !a <- stitch d
      return (a,b)
    foldM (\case
              r@(Failed _) -> const $ return r
              (Passed n) -> \(a,b) -> do
                r <- io $ evaluate (f a b)
                let env = map (second (`app` [])) cts
                       ++ [(show xa, toExpr a),(show xb, toExpr b)]
                sat <- evalType (M.fromList env) to (toExpr r)
                case sat of
                  False -> return $ Failed $ show (a, b)
                  True  -> return $ Passed (n+1))
      (Passed 0) xvs
  test f d t = error $ show t

instance (Constrain a, Constrain b, Constrain c, Constrain d)
         => Testable (a -> b -> c -> d) where
  test f d (stripQuals -> (RFun xa ta (RFun xb tb (RFun xc tc to _) _) _)) = do
    a <- gen (Proxy :: Proxy a) d ta
    let tb' = subst (mkSubst [(xa, var a)]) tb
    b <- gen (Proxy :: Proxy b) d tb'
    let tc' = subst (mkSubst [(xa, var a), (xb, var b)]) tc
    c <- gen (Proxy :: Proxy c) d tc'
    cts <- gets freesyms
    vals <- allSat [symbol a, symbol b, symbol c]
    -- build up the haskell value
    (xvs :: [(a,b,c)]) <- forM vals $ \ vs -> do
      setValues vs
      !c <- stitch d
      !b <- stitch d
      !a <- stitch d
      return (a,b,c)
    foldM (\case
              r@(Failed _) -> const $ return r
              (Passed n) -> \(a,b,c) -> do
                r <- io $ evaluate (f a b c)
                let env = map (second (`app` [])) cts
                       ++ [(show xa, toExpr a),(show xb, toExpr b),(show xc, toExpr c)]
                sat <- evalType (M.fromList env) to (toExpr r)
                case sat of
                  False -> return $ Failed $ show (a, b, c)
                  True  -> return $ Passed (n+1))
      (Passed 0) xvs
  test f d t = error $ show t

allSat :: [Symbol] -> Gen [[String]]
allSat roots = setup >>= go
  where
    setup = do
       ctx <- io $ makeContext Z3
       -- declare sorts
       ss  <- S.toList <$> gets sorts
       let defSort b e = io $ smtWrite ctx (format "(define-sort {} () {})" (b,e))
       -- FIXME: combine this with the code in `fresh`
       forM_ ss $ \case
         "Int" -> return ()
         "GHC.Types.Bool"   -> defSort ("GHC.Types.Bool" :: T.Text) ("Bool" :: T.Text)
         "CHOICE" -> defSort ("CHOICE" :: T.Text) ("Bool" :: T.Text)
         s        -> defSort s ("Int" :: T.Text)
       -- declare constructors
       cts <- gets constructors
       mapM_ (\ (c,t) -> io . command ctx $ makeDecl (symbol c) t) cts
       -- declare variables
       vs <- gets variables
       mapM_ (\ x -> io . command ctx $ Declare (symbol x) [] (snd x)) vs
       -- declare measures
       ms <- gets measEnv
       mapM_ (\ m -> io . command ctx $ makeDecl (val $ name m) (rTypeSort mempty $ sort m)) ms
       -- assert constraints
       cs <- gets constraints
       mapM_ (\c -> do {i <- gets seed; modify $ \s@(GS {..}) -> s { seed = seed + 1 };
                        io . command ctx $ Assert (Just i) c})
         cs
       deps <- V.fromList . map (symbol *** symbol) <$> gets deps
       io $ generateDepGraph "deps" deps
       return (ctx,vs,deps)

    go :: (Context, [Variable], V.Vector (Symbol,Symbol)) -> Gen [[String]]
    go (ctx,vs,deps) = do
       resp <- io $ command ctx CheckSat
       case resp of
         Error e -> io (cleanupContext ctx) >> error (T.unpack e)
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

generateDepGraph :: String -> V.Vector (Symbol,Symbol) -> IO ()
generateDepGraph name deps = writeFile (name <.> "dot") digraph
  where
    digraph = unlines $ ["digraph G {"] ++ edges ++ ["}"]
    edges   = [printf "\"%s\" -> \"%s\";" p c | (S p, S c) <- V.toList deps]


-- evalType :: Env -> RApp -> Expr -> Gen Bool
evalType :: M.HashMap String Expr -> SpecType -> Expr -> Gen Bool
evalType m t e@(EApp c xs)
  = do dcp <- (safeFromJust "evalType" . lookup (symbolString $ val $ c))
              <$> gets ctorEnv
       tyi <- gets tyconInfo
       vts <- freshen $ applyPreds (expandRApp M.empty tyi t) dcp
       liftM2 (&&) (evalReft m (toReft $ rt_reft t) e) (evalTypes m vts xs)
evalType m t e
  = evalReft m (toReft $ rt_reft t) e

freshen [] = return []
freshen ((v,t):vts)
  = do n <- gets seed
       modify $ \s@ (GS {..}) -> s { seed = seed + 1 }
       let v' = symbol . (++show n) . symbolString $ v
           su = mkSubst [(v,var v')]
           t' = subst su t
       vts' <- freshen $ subst su vts
       return ((v',t'):vts')

evalTypes m []         []     = return True
evalTypes m ((v,t):ts) (x:xs)
  = liftM2 (&&) (evalType m' t x) (evalTypes m' ts xs)
  where
    m' = M.insert (symbolString v) x m


evalReft :: M.HashMap String Expr -> Reft -> Expr -> Gen Bool
evalReft m r@(Reft (S v, rs)) x
  = and <$> sequence [ evalPred p (M.insert v x m) | RConc p <- rs ]

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
    ct = case symbolString $ val c of
      "GHC.Types.[]" -> "[]"
      "GHC.Types.:"  -> ":"
      c -> c
    eq = safeFromJust ("applyMeasure: " ++ ct)
       $ find ((==ct) . show . ctor) $ eqns m
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

evalBop Plus  (ECon (I x)) (ECon (I y)) = ECon . I $ x + y
evalBop Minus (ECon (I x)) (ECon (I y)) = ECon . I $ x - y
evalBop Times (ECon (I x)) (ECon (I y)) = ECon . I $ x * y
evalBop Div   (ECon (I x)) (ECon (I y)) = ECon . I $ x `div` y
evalBop Mod   (ECon (I x)) (ECon (I y)) = ECon . I $ x `mod` y
evalBop b     e1           e2           = error $ printf "evalBop(%s, %s, %s)" (show b) (show e1) (show e2)


--------------------------------------------------------------------------------
--- Constrainable Data
--------------------------------------------------------------------------------
class Show a => Constrain a where
  getType :: Proxy a -> String
  default getType :: (Generic a, GConstrain (Rep a))
                  => Proxy a -> String
  getType p = gtype (reproxyRep p)

  gen :: Proxy a -> Int -> SpecType -> Gen String
  default gen :: (Generic a, GConstrain (Rep a))
              => Proxy a -> Int -> SpecType -> Gen String
  gen p = ggen (reproxyRep p)


  stitch :: Int -> Gen a
  default stitch :: (Generic a, GConstrain (Rep a))
                 => Int -> Gen a
  stitch d = to <$> gstitch d

  toExpr :: a -> Expr
  default toExpr :: (Generic a, GConstrain (Rep a))
                 => a -> Expr
  toExpr = gtoExpr . from

reproxyElem :: proxy (f a) -> Proxy a
reproxyElem = reproxy

reproxyRep :: Proxy a -> Proxy (Rep a a)
reproxyRep = reproxy

--------------------------------------------------------------------------------
--- Sums of Products
--------------------------------------------------------------------------------
class GConstrain f where
  gtype        :: Proxy (f a) -> String
  ggen         :: Proxy (f a) -> Int    -> SpecType -> Gen String
  gstitch      :: Int -> Gen (f a)
  gtoExpr      :: f a -> Expr

reproxyGElem :: Proxy (M1 d c f a) -> Proxy (f a)
reproxyGElem = reproxy

instance (Datatype c, GConstrainSum f) => GConstrain (D1 c f) where
  gtype p = qualifiedDatatypeName (undefined :: D1 c f a)

  ggen p d t
    = inModule mod . making sort $ do
        xs <- ggenAlts (reproxyGElem p) d t
        x  <- freshChoose xs sort
        constrain $ ofReft x $ toReft $ rt_reft t
        return x
    where
      mod  = GHC.Generics.moduleName (undefined :: D1 c f a)
      sort = qualifiedSort (undefined :: D1 c f a)

  gstitch d = M1 <$> (pop >> making sort (fst <$> gstitchAlts d))
    where
      sort = qualifiedSort (undefined :: D1 c f a)

  gtoExpr c@(M1 x) = app (qualify c (symbolString $ val d)) xs
    where
      (EApp d xs) = gtoExprAlts x

instance (Constrain a) => GConstrain (K1 i a) where
  gtype p    = getType (reproxy p :: Proxy a)
  ggen p d t = gen (reproxy p :: Proxy a) d t
  gstitch d  = K1 <$> stitch d
  gtoExpr (K1 x) = toExpr x

qualify :: Datatype d => D1 d f a -> String -> String
qualify d x = GHC.Generics.moduleName d ++ "." ++ x

qualifiedDatatypeName :: Datatype d => D1 d f a -> String
qualifiedDatatypeName d = qualify d (datatypeName d)

qualifiedSort :: Datatype d => D1 d f a -> Sort
qualifiedSort d = FObj $ symbol $ qualifiedDatatypeName d

--------------------------------------------------------------------------------
--- Sums
--------------------------------------------------------------------------------
class GConstrainSum f where
  ggenAlts      :: Proxy (f a) -> Int -> SpecType -> Gen [(String,String)]
  gstitchAlts   :: Int -> Gen (f a, Bool)
  gtoExprAlts   :: f a -> Expr

reproxyLeft :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (f a)
reproxyLeft = reproxy

reproxyRight :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (g a)
reproxyRight = reproxy

instance (GConstrainSum f, GConstrainSum g) => GConstrainSum (f :+: g) where
  ggenAlts p d t
    = do xs <- ggenAlts (reproxyLeft p) d t
         ys <- ggenAlts (reproxyRight p) d t
         return $! xs++ys

  gstitchAlts d
    = do (g,cg) <- gstitchAlts d
         (f,cf) <- gstitchAlts d
         case (cf,cg) of
           (True,_) -> return $ (L1 f, True)
           (_,True) -> return $ (R1 g, True)
           _        -> return $ (error "gstitchAlts :+: CANNOT HAPPEN", False)

  gtoExprAlts (L1 x) = gtoExprAlts x
  gtoExprAlts (R1 x) = gtoExprAlts x

instance (Constructor c, GConstrainProd f) => GConstrainSum (C1 c f) where
  ggenAlts p 0 t
    = do ty <- gets makingTy
         if gisRecursive p ty
           then return []
           else ggenAlt p 0 t
  ggenAlts p d t = ggenAlt p d t

  gstitchAlts 0
    = do ty <- gets makingTy
         if gisRecursive (Proxy :: Proxy (C1 c f a)) ty
           then return $ (error "gstitchAlts C1 CANNOT HAPPEN", False)
           else gstitchAlt 0
  gstitchAlts d
    = gstitchAlt d

  gtoExprAlts c@(M1 x)  = app (symbol $ conName c) (gtoExprs x)

gisRecursive :: (Constructor c, GConstrainProd f)
             => Proxy (C1 c f a) -> Sort -> Bool
gisRecursive (p :: Proxy (C1 c f a)) t
  = any (==(zDecodeString $ T.unpack $ smt2 t)) (gconArgTys (reproxyGElem p))
  where cn = conName (undefined :: C1 c f a)

ggenAlt :: (Constructor c, GConstrainProd f)
        => Proxy (C1 c f a) -> Int -> SpecType -> Gen [(String,String)]
ggenAlt (p :: Proxy (C1 c f a)) d t
  = fmap (:[]) $ withFreshChoice $ do
      let cn = conName (undefined :: C1 c f a)
      mod <- gets modName
      dcp <- safeFromJust "ggenAlt" . lookup (mod++"."++cn) <$> gets ctorEnv
      tyi <- gets tyconInfo
      let ts = applyPreds (expandRApp (M.fromList []) tyi t) dcp
      xs  <- ggenArgs (reproxyGElem p) d ts
      make (mod++"."++cn) xs =<< gets makingTy

gstitchAlt :: GConstrainProd f => Int -> Gen (C1 c f a, Bool)
gstitchAlt d
  = do pop
       x <- gstitchArgs d
       c <- popChoice
       return (M1 x, c)

--------------------------------------------------------------------------------
--- Products
--------------------------------------------------------------------------------
class GConstrainProd f where
  gconArgTys  :: Proxy (f a) -> [String]
  ggenArgs    :: Proxy (f a) -> Int -> [(Symbol,SpecType)] -> Gen [String]
  gstitchArgs :: Int -> Gen (f a)
  gtoExprs    :: (f a) -> [Expr]

instance (GConstrainProd f, GConstrainProd g) => GConstrainProd (f :*: g) where
  gconArgTys p = gconArgTys (reproxyLeft p) ++ gconArgTys (reproxyRight p)

  ggenArgs p d ts
    = do xs <- ggenArgs (reproxyLeft p) d ts
         let su = mkSubst $ zipWith (\x t -> (fst t, var x)) xs ts
         let ts' = drop (length xs) ts
         ys <- ggenArgs (reproxyRight p) d (map (second (subst su)) ts')
         return $ xs ++ ys

  gstitchArgs d
    = do ys <- gstitchArgs d
         xs <- gstitchArgs d
         return $ xs :*: ys

  gtoExprs (f :*: g) = gtoExprs f ++ gtoExprs g

instance (GConstrain f) => GConstrainProd (S1 c f) where
  gconArgTys p        = [gtype (reproxyGElem p)]
  ggenArgs p d (t:ts) = sequence [ggen (reproxyGElem p) (d-1) (snd t)]
  gstitchArgs d       = M1 <$> gstitch (d-1)
  gtoExprs (M1 x)     = [gtoExpr x]

instance GConstrainProd U1 where
  gconArgTys p    = []
  ggenArgs p d [] = return []
  gstitchArgs d   = return U1
  gtoExprs _      = []

--------------------------------------------------------------------------------
--- Instances
--------------------------------------------------------------------------------
instance Constrain () where
  getType _ = "GHC.Types.()"
  gen _ _ _ = fresh [] (FObj (S "UNIT"))
  stitch _  = pop >> return ()
  toExpr _  = app (stringSymbol "()") []

instance Constrain Int where
  getType _ = "GHC.Types.Int"
  gen _ _ t = fresh [] FInt >>= \x ->
    do constrain $ ofReft x (toReft $ rt_reft t)
       -- use the unfolding depth to constrain the range of Ints, like QuickCheck
       d <- gets depth
       constrain $ var x `ge` fromIntegral (negate d)
       constrain $ var x `le` fromIntegral d
       return x
  stitch _ = read <$> pop
  toExpr i = ECon $ I $ fromIntegral i

instance Constrain Bool
instance Constrain a => Constrain [a]
instance (Constrain a, Constrain b) => Constrain (a,b)



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

-- applyPreds :: RApp -> SpecType -> [SpecType]
applyPreds sp dc = zip xs (map tx ts)
  where
    (as, ps, _, t) = bkUniv dc
    (xs, ts, rt)   = bkArrow . snd $ bkClass t
    -- args  = reverse tyArgs
    su    = [(tv, toRSort t, t) | tv <- as | t <- rt_args sp]
    sup   = [(p, r) | p <- ps | r <- rt_pargs sp]
    tx    = (\t -> replacePreds "applyPreds" t sup) . onRefs (monosToPoly sup) . subsTyVars_meet su

onRefs f t@(RVar _ _) = t
onRefs f t = t { rt_pargs = f <$> rt_pargs t }

monosToPoly su r = foldr monoToPoly r su

monoToPoly (p, r) (RMono _ (U _ (Pr [up]) _))
  | pname p == pname up
  = r
monoToPoly _ m = m


-- apply4 :: (Constrain a, Constrain b, Constrain c, Constrain d)
--        => (a -> b -> c -> d -> e) -> Int -> Gen e
apply4 c d
  = do pop
       v4 <- cons
       v3 <- cons
       v2 <- cons
       v1 <- cons
       return $ c v1 v2 v3 v4
  where
    cons :: Constrain a => Gen a
    cons = stitch (d-1)


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

testModule :: FilePath -> [Gen Result] -> IO ()
testModule mod ts
  = do sp <- getSpec mod
       forM_ ts $ \t -> do
         res <- runGen sp t
         case res of
           Passed n -> printf "OK. Passed %d tests\n\n" n
           Failed x -> printf "Found counter-example: %s\n\n" x

testFun :: Testable f => f -> String -> Int -> Gen Result
testFun f name d
  = do ty <- fromJust . lookup name <$> gets sigs
       io $ printf "Testing %s\n" name -- (showpp ty)
       modify $ \s -> s { depth = d }
       test f d ty

testOne :: Testable f => f -> String -> FilePath -> IO Result
testOne f name path
  = do sp <- getSpec path
       let ty = val $ safeFromJust "testOne" $ lookup name $ map (first showpp) $ tySigs sp
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


safeFromJust msg Nothing  = error $ "safeFromJust: " ++ msg
safeFromJust msg (Just x) = x
