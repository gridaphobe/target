{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ParallelListComp     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns         #-}
module Test.Target.Targetable where

import           Control.Applicative
import           Control.Arrow                    (second)
import qualified Control.Monad.Catch              as Ex
import           Control.Monad.State
import           Data.Char
import qualified Data.HashMap.Strict              as M
import           Data.IORef
import           Data.List
import           Data.Maybe
import           Data.Monoid
import           Data.Proxy
import           Data.Ratio
import qualified Data.Text                        as T
import qualified Data.Text.Lazy                   as LT
import           Data.Word (Word8)
import           GHC.Generics
import           System.IO.Unsafe
import           Text.Show.Functions

import qualified GHC

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types          hiding (prop, ofReft)
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Tidy     (tidySymbol)
import           Language.Haskell.Liquid.Types    hiding (var)

-- import           Test.Target.Driver
import           Test.Target.Expr
import           Test.Target.Eval
import           Test.Target.Gen
import           Test.Target.Types
import           Test.Target.Util

import Text.Printf

import Debug.Trace

--------------------------------------------------------------------------------
--- Constrainable Data
--------------------------------------------------------------------------------
class Show a => Targetable a where
  getType :: Proxy a -> Sort
  gen     :: Proxy a -> Int -> SpecType -> Gen Variable
  -- stitch  :: Symbol -> SpecType -> Gen a
  toExpr  :: a -> Expr

  decode  :: Symbol -> SpecType -> Gen a
  check   :: a -> SpecType -> Gen (Bool, Expr)

  encode  :: a -> SpecType -> Gen Variable

  default getType :: (Generic a, GTargetable (Rep a))
                  => Proxy a -> Sort
  getType p = gtype (reproxyRep p)

  default gen :: (Generic a, GTargetable (Rep a))
              => Proxy a -> Int -> SpecType -> Gen Variable
  gen p = ggen (reproxyRep p)

  -- default stitch :: (Generic a, GTargetable (Rep a))
  --                => Symbol -> SpecType -> Gen a
  -- stitch d t = to <$> gstitch d

  default toExpr :: (Generic a, GTargetable (Rep a))
                 => a -> Expr
  toExpr = gtoExpr . from

  default decode :: (Generic a, GDecode (Rep a))
                 => Symbol -> SpecType -> Gen a
  decode v t = do
    x <- whichOf v
    -- traceShowM x
    (c, fs) <- unapply x
    -- traceShowM (c,fs)
    to <$> gdecode c fs

  default check :: (Generic a, GCheck (Rep a))
                => a -> SpecType -> Gen (Bool, Expr)
  check v t = gcheck (from v) t

  default encode :: (Generic a, GEncode (Rep a))
                 => a -> SpecType -> Gen Variable
  encode v t = gencode (from v) t

reproxy :: proxy a -> Proxy b
reproxy _ = Proxy
{-# INLINE reproxy #-}

reproxyElem :: proxy (f a) -> Proxy a
reproxyElem = reproxy
{-# INLINE reproxyElem #-}



--------------------------------------------------------------------------------
--- Instances
--------------------------------------------------------------------------------
instance Targetable () where
  getType _ = FObj "GHC.Tuple.()"
  gen _ _ _ = fresh (FObj "GHC.Tuple.()")
  -- this is super fiddly, but seemingly required since GHC.exprType chokes on "GHC.Tuple.()"
  toExpr _   = app ("()" :: Symbol) []

  decode _ _ = return ()
  check v t = do
    let e = app ("()" :: Symbol) []
    b <- eval e $ toReft $ rt_reft t
    return (b,e)
  encode v t = fresh (FObj "GHC.Tuple.()")


instance Targetable Int where
  getType _ = FObj "GHC.Types.Int"
  gen _ d t = fresh FInt >>= \x ->
    do constrain $ ofReft x (toReft $ rt_reft t)
       -- use the unfolding depth to constrain the range of Ints, like QuickCheck
       constrain $ var x `ge` fromIntegral (negate d)
       constrain $ var x `le` fromIntegral d
       return x
  toExpr i = ECon $ I $ fromIntegral i

  decode v _ = read . T.unpack <$> getValue v

  check v t = do
    let e = fromIntegral v
    b <- eval e $ toReft $ rt_reft t
    return (b, e)

  encode i t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral i
       constrain $ ofReft v (toReft $ rt_reft t)
       return v


instance Targetable Integer where
  getType _ = FObj "GHC.Integer.Type.Integer"
  gen _ d t = gen (Proxy :: Proxy Int) d t
  toExpr  x = toExpr (fromIntegral x :: Int)

  decode v t = decode v t >>= \(x::Int) -> return . fromIntegral $ x
  check v t = do
    let e = fromIntegral v
    b <- eval e $ toReft $ rt_reft t
    return (b, e)

  encode i t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral i
       constrain $ ofReft v (toReft $ rt_reft t)
       return v


instance Targetable Char where
  getType _ = FObj "GHC.Types.Char"
  gen _ d t = fresh FInt >>= \x ->
    do constrain $ var x `ge` 0
       constrain $ var x `le` fromIntegral d
       constrain $ ofReft x (toReft $ rt_reft t)
       return x
  toExpr  c = ESym $ SL $ T.singleton c

  decode v t = decode v t >>= \(x::Int) -> return . chr $ x + ord 'a'
  check v t = do
    let e = ESym $ SL $ T.singleton v
    b <- eval e $ toReft $ rt_reft t
    return (b, e)
  encode c t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral (ord c - ord 'a')
       constrain $ ofReft v (toReft $ rt_reft t)
       return v
  

instance Targetable Word8 where
  getType _ = FObj "GHC.Word.Word8"
  gen _ d t = fresh FInt >>= \x ->
    do _ <- gets depth
       constrain $ var x `ge` 0
       constrain $ var x `le` fromIntegral d
       constrain $ ofReft x (toReft $ rt_reft t)
       return x
  toExpr i   = ECon $ I $ fromIntegral i

  decode v t = decode v t >>= \(x::Int) -> return $ fromIntegral x
  check v t = do
    let e = fromIntegral v
    b <- eval e $ toReft $ rt_reft t
    return (b, e)
  encode w t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral w
       constrain $ ofReft v (toReft $ rt_reft t)
       return v


instance Targetable Bool where
  getType _ = FObj "GHC.Types.Bool"
  gen _ d t = fresh boolsort >>= \x ->
    do constrain $ ofReft x (toReft $ rt_reft t)
       return x

  decode v _ = getValue v >>= \case
    "true"  -> return True
    "false" -> return False


instance Targetable a => Targetable [a]
instance Targetable a => Targetable (Maybe a)
instance (Targetable a, Targetable b) => Targetable (Either a b)
instance (Targetable a, Targetable b) => Targetable (a,b)
instance (Targetable a, Targetable b, Targetable c) => Targetable (a,b,c)

instance (Num a, Integral a, Targetable a) => Targetable (Ratio a) where
  getType _ = FObj "GHC.Real.Ratio"
  gen _ d t = gen (Proxy :: Proxy Int) d t
  decode v t= decode v t >>= \ (x::Int) -> return (fromIntegral x)
  -- gen _ d t = fresh (FObj "GHC.Real.Ratio") >>= \x ->
  --   do gen (Proxy :: Proxy Int) d t
  --      gen (Proxy :: Proxy Int) d t
  --      return x
  -- stitch d t = do x :: Int <- stitch d t
  --                 y' :: Int <- stitch d t
  --                 -- we should really modify `t' above to have Z3 generate non-zero denoms
  --                 let y = if y' == 0 then 1 else y'
  --                 let toA z = fromIntegral z :: a
  --                 return $ toA x % toA y
  toExpr x = EApp (dummyLoc "GHC.Real.:%") [toExpr (numerator x), toExpr (denominator x)]
  check = undefined
  encode = undefined


choose :: Variable -> [Variable] -> Gen ()
choose x cs
  = do cs <- forM cs $ \c -> do
               addDep x c
               return $ prop c
       constrain $ pOr cs
       constrain $ pAnd [ PNot $ pAnd [x, y]
                        | [x, y] <- filter ((==2) . length) $ subsequences cs ]

-- make :: TH.Name -> [String] -> Sort -> Gen String
-- make :: Symbol -> [Variable] -> Sort -> Gen Variable
-- make c vs s
--   = do x  <- fresh vs s
--        --t <- (safeFromJust "make" . lookup c) <$> gets ctorEnv
--        t <- lookupCtor c
--        let (xs, _, rt) = bkArrowDeep t
--            su          = mkSubst $ zip (map symbol xs) (map var vs)
--            ct          = FFunc 0 $ map snd vs ++ [s]
--        addConstructor (c, ct)
--        addConstraint $ var x `eq` app c (map var vs)
--        constrain $ ofReft x $ subst su $ toReft $ rt_reft rt
--        return x

make' :: Symbol -> Variable -> [Variable] -> Gen ()
make' c x vs
  = do Just ch <- gets chosen
       mapM_ (addDep ch) vs
       addConstraint $ prop (fst ch) `imp` (var (fst x) `eq` app c (map (var . fst) vs))
       --mt <- lookup c <$> gets ctorEnv
       --case mt of
       --  Nothing -> addConstructor (c, FFunc 0 $ map snd vs ++ [snd x])
       --  Just t  -> do
       t <- lookupCtor c
       let (xs, _, rt) = bkArrowDeep t
           su          = mkSubst $ zip (map symbol xs) (map var vs)
       addConstructor (c, rTypeSort mempty t)
       constrain $ ofReft x $ subst su $ toReft $ rt_reft rt

apply :: Symbol -> [Variable] -> Gen Variable
apply c vs = do 
  s <- gets makingTy
  x <- fresh s
  addConstraint $ var (fst x) `eq` app c (map (var . fst) vs)
  --mt <- lookup c <$> gets ctorEnv
  --case mt of
  --  Nothing -> addConstructor (c, FFunc 0 $ map snd vs ++ [snd x])
  --  Just t  -> do
  t <- lookupCtor c
  let (xs, _, rt) = bkArrowDeep t
      su          = mkSubst $ zip (map symbol xs) (map var vs)
  addConstructor (c, rTypeSort mempty t)
  constrain $ ofReft x $ subst su $ toReft $ rt_reft rt
  return x

unapply :: Symbol -> Gen (Symbol, [Symbol])
unapply c = do
  let [_,cn,_] = T.splitOn "-" $ symbolText c
  deps <- gets deps
  return (symbol cn, M.lookupDefault [] c deps)

constrain :: Pred -> Gen ()
constrain p
  = do mc <- gets chosen
       case mc of
         Nothing -> addConstraint p
         Just c  -> let p' = prop c `imp` p
                    in addConstraint p'

-- make2 :: forall a b. (Constrain a, Targetable b)
--       => TH.Name -> (Proxy a, Proxy b) -> SpecType -> Sort -> Int -> Gen String
-- make2 c (pa,pb) t s d
--   = do dcp <- lookupCtor c -- fromJust . lookup c <$> gets ctorEnv
--        tyi <- gets tyconInfo
--        emb <- gets embEnv
--        let [t1,t2] = applyPreds (addTyConInfo emb tyi t) dcp
--        x1 <- gen pa (d-1) (snd t1)
--        let su = mkSubst [(fst t1, var x1)]
--        x2 <- gen pb (d-1) (subst su $ snd t2)
--        make c [x1,x2] s

-- -- make3 :: forall a b c. (Targetable a, Targetable b, Targetable c)
-- --       => TH.Name -> (Proxy a, Proxy b, Proxy c) -> SpecType -> Sort -> Int -> Gen String
-- make3 c (pa,pb,pc) t s d
--   = do dcp <- lookupCtor c --fromJust . lookup c <$> gets ctorEnv
--        tyi <- gets tyconInfo
--        emb <- gets embEnv
--        let [t1,t2,t3] = applyPreds (addTyConInfo emb tyi t) dcp
--        x1 <- gen pa (d-1) (snd t1)
--        let su = mkSubst [(fst t1, var x1)]
--        x2 <- gen pb (d-1) (subst su $ snd t2)
--        let su = mkSubst [(fst t1, var x1),(fst t2, var x2)]
--        x3 <- gen pc (d-1) (subst su $ snd t3)
--        make c [x1,x2,x3] s

-- make4 c (p1,p2,p3,p4) t s d
--   = do dcp <- lookupCtor c --fromJust . lookup c <$> gets ctorEnv
--        tyi <- gets tyconInfo
--        emb <- gets embEnv
--        let [t1,t2,t3,t4] = applyPreds (addTyConInfo emb tyi t) dcp
--        x1 <- gen p1 (d-1) (snd t1)
--        let su = mkSubst [(fst t1, var x1)]
--        x2 <- gen p2 (d-1) (subst su $ snd t2)
--        let su = mkSubst [(fst t1, var x1),(fst t2, var x2)]
--        x3 <- gen p3 (d-1) (subst su $ snd t3)
--        let su = mkSubst [(fst t1, var x1),(fst t2, var x2),(fst t3, var x3)]
--        x4 <- gen p4 (d-1) (subst su $ snd t4)
--        make c [x1,x2,x3,x4] s

-- make5 c (p1,p2,p3,p4,p5) t s d
--   = do dcp <- lookupCtor c --fromJust . lookup c <$> gets ctorEnv
--        tyi <- gets tyconInfo
--        emb <- gets embEnv
--        let [t1,t2,t3,t4,t5] = applyPreds (addTyConInfo emb tyi t) dcp
--        x1 <- gen p1 (d-1) (snd t1)
--        let su = mkSubst [(fst t1, var x1)]
--        x2 <- gen p2 (d-1) (subst su $ snd t2)
--        let su = mkSubst [(fst t1, var x1),(fst t2, var x2)]
--        x3 <- gen p3 (d-1) (subst su $ snd t3)
--        let su = mkSubst [(fst t1, var x1),(fst t2, var x2),(fst t3, var x3)]
--        x4 <- gen p4 (d-1) (subst su $ snd t4)
--        let su = mkSubst [(fst t1, var x1),(fst t2, var x2),(fst t3, var x3),(fst t4, var x4)]
--        x5 <- gen p5 (d-1) (subst su $ snd t5)
--        make c [x1,x2,x3,x4,x5] s


-- apply4 :: (Targetable a, Targetable b, Targetable c, Targetable d)
--        => (a -> b -> c -> d -> e) -> Int -> Gen e
-- apply4 c d
--   = do
--        v4 <- cons
--        v3 <- cons
--        v2 <- cons
--        v1 <- cons
--        return $ c v1 v2 v3 v4
--   where
--     cons :: Targetable a => Gen a
--     cons = stitch (d-1)


ofReft :: Variable -> Reft -> Pred
ofReft (s,_) (Reft (v, rs))
  = let x = mkSubst [(v, var s)]
    in pAnd [subst x p | RConc p <- rs]


reproxyRep :: Proxy a -> Proxy (Rep a a)
reproxyRep = reproxy


--------------------------------------------------------------------------------
--- Sums of Products
--------------------------------------------------------------------------------
class GTargetable f where
  gtype        :: Proxy (f a) -> Sort
  ggen         :: Proxy (f a) -> Int    -> SpecType -> Gen Variable
  -- gstitch      :: Symbol -> Gen (f a)
  gtoExpr      :: f a -> Expr


class GDecode f where
  gdecode      :: Symbol -> [Symbol] -> Gen (f a)

class GCheck f where
  gcheck       :: f a -> SpecType -> Gen (Bool, Expr)

class GEncode f where
  gencode      :: f a -> SpecType -> Gen Variable


reproxyGElem :: Proxy (M1 d c f a) -> Proxy (f a)
reproxyGElem = reproxy

instance (Datatype c, GTargetableSum f) => GTargetable (D1 c f) where
  gtype p = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

  ggen p d t
    = inModule mod . making sort $ do
        x  <- fresh sort
        xs <- ggenAlts (reproxyGElem p) x d t
        choose x xs
        constrain $ ofReft x $ toReft $ rt_reft t
        return x
    where
      mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

  -- gstitch d = M1 <$> making sort (fst <$> gstitchAlts d)
  --   where
  --     sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

  gtoExpr c@(M1 x) = app (qualify c (symbolString $ val d)) xs
    where
      (EApp d xs) = gtoExprAlts x

instance (Datatype c, GDecode f) => GDecode (D1 c f) where
  gdecode c vs = M1 <$> making sort (gdecode c vs)
    where
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

instance (Datatype c, GCheck f) => GCheck (D1 c f) where
  gcheck (M1 x) t = inModule mod . making sort $ gcheck x t
    where
      mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)

instance (Datatype c, GEncode f) => GEncode (D1 c f) where
  gencode (M1 x) t = inModule mod . making sort $ gencode x t
    where
      mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)


instance (Targetable a) => GTargetable (K1 i a) where
  gtype p    = getType (reproxy p :: Proxy a)
  ggen p d t = do let p' = reproxy p :: Proxy a
                  ty <- gets makingTy
                  depth <- gets depth
                  sc <- gets scDepth
                  let d' = if getType p' == ty || sc
                              then d
                              else depth
                  gen p' d' t
  -- gstitch d  = do let p = Proxy :: Proxy a
  --                 ty <- gets makingTy
  --                 depth <- gets depth
  --                 sc <- gets scDepth
  --                 let d' = if getType p == ty || sc
  --                             then d
  --                             else depth
  --                 K1 <$> stitch d' undefined
  gtoExpr (K1 x) = toExpr x


instance Targetable a => GDecodeFields (K1 i a) where
  gdecodeFields (v:vs) = do
    x <- decode v undefined
    return (vs, K1 x)

instance Targetable a => GCheckFields (K1 i a) where
  gcheckFields (K1 x) ((f,t):ts) = do
    (b, v) <- check x t
    return (b, [v], subst (mkSubst [(f, v)]) ts)

instance Targetable a => GEncodeFields (K1 i a) where
  gencodeFields (K1 x) ((f,t):ts) = do
    v <- encode x t
    return ([v], subst (mkSubst [(f, var v)]) ts)


qualify :: Datatype d => D1 d f a -> String -> String
qualify d x = GHC.Generics.moduleName d ++ "." ++ x

qualifiedDatatypeName :: Datatype d => D1 d f a -> Symbol
qualifiedDatatypeName d = symbol $ qualify d (datatypeName d)


--------------------------------------------------------------------------------
--- Sums
--------------------------------------------------------------------------------
class GTargetableSum f where
  ggenAlts      :: Proxy (f a) -> Variable -> Int -> SpecType -> Gen [Variable]
  -- gstitchAlts   :: Symbol -> Gen (f a, Bool)
  gtoExprAlts   :: f a -> Expr

reproxyLeft :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (f a)
reproxyLeft = reproxy

reproxyRight :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (g a)
reproxyRight = reproxy

instance (GTargetableSum f, GTargetableSum g) => GTargetableSum (f :+: g) where
  ggenAlts p v d t
    = do xs <- ggenAlts (reproxyLeft p) v d t
         ys <- ggenAlts (reproxyRight p) v d t
         return $! xs++ys

  -- gstitchAlts d
  --   = do (g,cg) <- gstitchAlts d
  --        (f,cf) <- gstitchAlts d
  --        case (cf,cg) of
  --          (True,_) -> return (L1 f, True)
  --          (_,True) -> return (R1 g, True)
  --          _        -> return (error "gstitchAlts :+: CANNOT HAPPEN", False)

  gtoExprAlts (L1 x) = gtoExprAlts x
  gtoExprAlts (R1 x) = gtoExprAlts x

instance (GDecode f, GDecode g) => GDecode (f :+: g) where
  gdecode c vs =  L1 <$> gdecode c vs
              <|> R1 <$> gdecode c vs

instance (GCheck f, GCheck g) => GCheck (f :+: g) where
  gcheck (L1 x) t = gcheck x t
  gcheck (R1 x) t = gcheck x t

instance (GEncode f, GEncode g) => GEncode (f :+: g) where
  gencode (L1 x) t = gencode x t
  gencode (R1 x) t = gencode x t


instance (Constructor c, GTargetableProd f) => GTargetableSum (C1 c f) where
  ggenAlts p v d t | d <= 0
    = do ty <- gets makingTy
         if gisRecursive p ty
           then return []
           else pure <$> ggenAlt p v 0 t
  ggenAlts p v d t = pure <$> ggenAlt p v d t

  -- gstitchAlts d | d <= 0
  --   = do ty <- gets makingTy
  --        if gisRecursive (Proxy :: Proxy (C1 c f a)) ty
  --          then return (error "gstitchAlts C1 CANNOT HAPPEN", False)
  --          else gstitchAlt 0
  -- gstitchAlts d
  --   = gstitchAlt d

  gtoExprAlts c@(M1 x)  = app (symbol $ conName c) (gtoExprs x)

instance (Constructor c, GDecodeFields f) => GDecode (C1 c f) where
  gdecode c vs
    | c == symbol (conName (undefined :: C1 c f a))
    = M1 . snd <$> gdecodeFields vs
    | otherwise
    = empty

instance (Constructor c, GCheckFields f) => GCheck (C1 c f) where
  gcheck c@(M1 x) t = do
    mod <- symbolString <$> gets modName
    let cn = symbol $ mod ++ "." ++ conName (undefined :: C1 c f a)
    dcp <- lookupCtor cn
    -- traceShowM (cn, dcp)
    tyi <- gets tyconInfo
    emb <- gets embEnv
    let ts = applyPreds (addTyConInfo emb tyi t) dcp
    -- traceShowM ts
    (b, vs, _) <- gcheckFields x ts
    let v = app cn vs
    b'  <- eval v (toReft $ rt_reft t)
    return (b && b', v)
    -- v <- apply (symbol $ mod++"."++cn) vs
    -- let t' = subst (mkSubst [(f, var v) | (f,t) <- ts | v <- vs]) t
    -- constrain $ ofReft v $ toReft $ rt_reft t'
    -- return v

instance (Constructor c, GEncodeFields f) => GEncode (C1 c f) where
  gencode c@(M1 x) t = do
    let cn = conName (undefined :: C1 c f a)
    mod <- symbolString <$> gets modName
    dcp <- lookupCtor (symbol $ mod++"."++cn)
    tyi <- gets tyconInfo
    emb <- gets embEnv
    let ts = applyPreds (addTyConInfo emb tyi t) dcp
    (vs, _) <- gencodeFields x ts
    let t' = subst (mkSubst [(f, var v) | (f,t) <- ts | v <- vs]) t
    v <- apply (symbol $ mod++"."++cn) vs
    constrain $ ofReft v $ toReft $ rt_reft t'
    return v

gisRecursive :: (Constructor c, GTargetableProd f)
             => Proxy (C1 c f a) -> Sort -> Bool
gisRecursive (p :: Proxy (C1 c f a)) t
  = t `elem` gconArgTys (reproxyGElem p)

ggenAlt :: (Constructor c, GTargetableProd f)
        => Proxy (C1 c f a) -> Variable -> Int -> SpecType -> Gen Variable
ggenAlt (p :: Proxy (C1 c f a)) x d t
  = withFreshChoice cn $ \ch -> do
     mod <- symbolString <$> gets modName
     dcp <- lookupCtor (symbol $ mod++"."++cn)
     tyi <- gets tyconInfo
     emb <- gets embEnv
     let ts = applyPreds (addTyConInfo emb tyi t) dcp
     xs  <- ggenArgs (reproxyGElem p) d ts
     make' (symbol $ mod++"."++cn) x xs
  where
    cn = conName (undefined :: C1 c f a)

-- gstitchAlt :: GTargetableProd f => Symbol -> Gen (C1 c f a, Bool)
-- gstitchAlt v
--   = do x <- gstitchArgs v
--        c <- getValue v
--        return (M1 x, c)

--------------------------------------------------------------------------------
--- Products
--------------------------------------------------------------------------------
class GTargetableProd f where
  gconArgTys  :: Proxy (f a) -> [Sort]
  ggenArgs    :: Proxy (f a) -> Int -> [(Symbol,SpecType)] -> Gen [Variable]
  -- gstitchArgs :: Int -> Gen (f a)
  gtoExprs    :: f a -> [Expr]

class GDecodeFields f where
  gdecodeFields :: [Symbol] -> Gen ([Symbol], f a)

class GCheckFields f where
  gcheckFields :: f a -> [(Symbol, SpecType)]
               -> Gen (Bool, [Expr], [(Symbol, SpecType)])

class GEncodeFields f where
  gencodeFields :: f a -> [(Symbol,SpecType)] -> Gen ([Variable], [(Symbol,SpecType)])


instance (GTargetableProd f, GTargetableProd g) => GTargetableProd (f :*: g) where
  gconArgTys p = gconArgTys (reproxyLeft p) ++ gconArgTys (reproxyRight p)

  ggenArgs p d ts
    = do xs <- ggenArgs (reproxyLeft p) d ts
         let su = mkSubst $ zipWith (\x t -> (fst t, var x)) xs ts
         let ts' = drop (length xs) ts
         ys <- ggenArgs (reproxyRight p) d (map (second (subst su)) ts')
         return $ xs ++ ys

  -- gstitchArgs d
  --   = do ys <- gstitchArgs d
  --        xs <- gstitchArgs d
  --        return $ xs :*: ys

  gtoExprs (f :*: g) = gtoExprs f ++ gtoExprs g

instance (GDecodeFields f, GDecodeFields g) => GDecodeFields (f :*: g) where
  gdecodeFields vs = do
    (vs', ls)  <- gdecodeFields vs
    (vs'', rs) <- gdecodeFields vs'
    return (vs'', ls :*: rs)

instance (GCheckFields f, GCheckFields g) => GCheckFields (f :*: g) where
  gcheckFields (f :*: g) ts = do
    (bl,fs,ts')  <- gcheckFields f ts
    (br,gs,ts'') <- gcheckFields g ts'
    return (bl && br, fs ++ gs, ts'')

instance (GEncodeFields f, GEncodeFields g) => GEncodeFields (f :*: g) where
  gencodeFields (f :*: g) ts = do
    (fs,ts')  <- gencodeFields f ts
    (gs,ts'') <- gencodeFields g ts'
    return (fs ++ gs, ts'')


instance (GTargetable f) => GTargetableProd (S1 c f) where
  gconArgTys p        = [gtype (reproxyGElem p)]
  ggenArgs p d (t:ts) = sequence [ggen (reproxyGElem p) (d-1) (snd t)]
  -- gstitchArgs d       = M1 <$> gstitch (d-1)
  gtoExprs (M1 x)     = [gtoExpr x]

instance GDecodeFields f => GDecodeFields (S1 c f) where
  gdecodeFields vs = do
    (vs, x) <- gdecodeFields vs
    return (vs, M1 x)

instance (GCheckFields f) => GCheckFields (S1 c f) where
  gcheckFields (M1 x) ts = gcheckFields x ts

instance (GEncodeFields f) => GEncodeFields (S1 c f) where
  gencodeFields (M1 x) ts = gencodeFields x ts

instance GTargetableProd U1 where
  gconArgTys p    = []
  ggenArgs p d _  = return []
  -- gstitchArgs d   = return U1
  gtoExprs _      = []

instance GDecodeFields U1 where
  gdecodeFields vs = return (vs, U1)

instance GCheckFields U1 where
  gcheckFields _ ts = return (True, [], ts)

instance GEncodeFields U1 where
  gencodeFields _ ts = return ([], ts)
