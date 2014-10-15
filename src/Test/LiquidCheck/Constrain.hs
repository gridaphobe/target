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
module Test.LiquidCheck.Constrain where

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

-- import           Test.LiquidCheck.Driver
import           Test.LiquidCheck.Expr
import           Test.LiquidCheck.Eval
import           Test.LiquidCheck.Gen
import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util

import Text.Printf

import Debug.Trace

--------------------------------------------------------------------------------
--- Constrainable Data
--------------------------------------------------------------------------------
class Show a => Constrain a where
  getType :: Proxy a -> Sort
  gen     :: Proxy a -> Int -> SpecType -> Gen Variable
  -- stitch  :: Symbol -> SpecType -> Gen a
  toExpr  :: a -> Expr

  decode  :: Symbol -> SpecType -> Gen a
  encode  :: a -> SpecType -> Gen Variable

  default getType :: (Generic a, GConstrain (Rep a))
                  => Proxy a -> Sort
  getType p = gtype (reproxyRep p)

  default gen :: (Generic a, GConstrain (Rep a))
              => Proxy a -> Int -> SpecType -> Gen Variable
  gen p = ggen (reproxyRep p)

  -- default stitch :: (Generic a, GConstrain (Rep a))
  --                => Symbol -> SpecType -> Gen a
  -- stitch d t = to <$> gstitch d

  default toExpr :: (Generic a, GConstrain (Rep a))
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
instance Constrain () where
  getType _ = FObj "GHC.Tuple.()"
  gen _ _ _ = fresh (FObj "GHC.Tuple.()")
  -- this is super fiddly, but seemingly required since GHC.exprType chokes on "GHC.Tuple.()"
  toExpr _   = app ("()" :: Symbol) []

  decode _ _ = return ()
  encode v t = fresh (FObj "GHC.Tuple.()")


instance Constrain Int where
  getType _ = FObj "GHC.Types.Int"
  gen _ d t = fresh FInt >>= \x ->
    do constrain $ ofReft x (toReft $ rt_reft t)
       -- use the unfolding depth to constrain the range of Ints, like QuickCheck
       constrain $ var x `ge` fromIntegral (negate d)
       constrain $ var x `le` fromIntegral d
       return x
  toExpr i = ECon $ I $ fromIntegral i

  decode v _ = read . T.unpack <$> getValue v
  encode i t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral i
       constrain $ ofReft v (toReft $ rt_reft t)
       return v


instance Constrain Integer where
  getType _ = FObj "GHC.Integer.Type.Integer"
  gen _ d t = gen (Proxy :: Proxy Int) d t
  toExpr  x = toExpr (fromIntegral x :: Int)

  decode v t = decode v t >>= \(x::Int) -> return . fromIntegral $ x
  encode i t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral i
       constrain $ ofReft v (toReft $ rt_reft t)
       return v


instance Constrain Char where
  getType _ = FObj "GHC.Types.Char"
  gen _ d t = fresh FInt >>= \x ->
    do constrain $ var x `ge` 0
       constrain $ var x `le` fromIntegral d
       constrain $ ofReft x (toReft $ rt_reft t)
       return x
  toExpr  c = ESym $ SL $ T.singleton c

  decode v t = decode v t >>= \(x::Int) -> return . chr $ x + ord 'a'
  encode c t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral (ord c - ord 'a')
       constrain $ ofReft v (toReft $ rt_reft t)
       return v
  

instance Constrain Word8 where
  getType _ = FObj "GHC.Word.Word8"
  gen _ d t = fresh FInt >>= \x ->
    do _ <- gets depth
       constrain $ var x `ge` 0
       constrain $ var x `le` fromIntegral d
       constrain $ ofReft x (toReft $ rt_reft t)
       return x
  toExpr i   = ECon $ I $ fromIntegral i

  decode v t = decode v t >>= \(x::Int) -> return $ fromIntegral x
  encode w t =
    do v <- fresh FInt
       constrain $ var v `eq` fromIntegral w
       constrain $ ofReft v (toReft $ rt_reft t)
       return v


instance Constrain Bool where
  getType _ = FObj "GHC.Types.Bool"
  gen _ d t = fresh boolsort >>= \x ->
    do constrain $ ofReft x (toReft $ rt_reft t)
       return x

  decode v _ = getValue v >>= \case
    "true"  -> return True
    "false" -> return False


instance Constrain a => Constrain [a]
instance Constrain a => Constrain (Maybe a)
instance (Constrain a, Constrain b) => Constrain (Either a b)
instance (Constrain a, Constrain b) => Constrain (a,b)
instance (Constrain a, Constrain b, Constrain c) => Constrain (a,b,c)

-- instance (Num a, Integral a, Constrain a) => Constrain (Ratio a) where
--   getType _ = FObj "GHC.Real.Ratio"
--   gen _ d t = fresh (FObj "GHC.Real.Ratio") >>= \x ->
--     do gen (Proxy :: Proxy Int) d t
--        gen (Proxy :: Proxy Int) d t
--        return x
--   stitch d t = do x :: Int <- stitch d t
--                   y' :: Int <- stitch d t
--                   -- we should really modify `t' above to have Z3 generate non-zero denoms
--                   let y = if y' == 0 then 1 else y'
--                   let toA z = fromIntegral z :: a
--                   return $ toA x % toA y
--   toExpr x = EApp (dummyLoc "GHC.Real.:%") [toExpr (numerator x), toExpr (denominator x)]


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

-- make2 :: forall a b. (Constrain a, Constrain b)
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

-- -- make3 :: forall a b c. (Constrain a, Constrain b, Constrain c)
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


-- apply4 :: (Constrain a, Constrain b, Constrain c, Constrain d)
--        => (a -> b -> c -> d -> e) -> Int -> Gen e
-- apply4 c d
--   = do
--        v4 <- cons
--        v3 <- cons
--        v2 <- cons
--        v1 <- cons
--        return $ c v1 v2 v3 v4
--   where
--     cons :: Constrain a => Gen a
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
class GConstrain f where
  gtype        :: Proxy (f a) -> Sort
  ggen         :: Proxy (f a) -> Int    -> SpecType -> Gen Variable
  -- gstitch      :: Symbol -> Gen (f a)
  gtoExpr      :: f a -> Expr


class GDecode f where
  gdecode      :: Symbol -> [Symbol] -> Gen (f a)

class GEncode f where
  gencode      :: f a -> SpecType -> Gen Variable


reproxyGElem :: Proxy (M1 d c f a) -> Proxy (f a)
reproxyGElem = reproxy

instance (Datatype c, GConstrainSum f) => GConstrain (D1 c f) where
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

instance (Datatype c, GEncode f) => GEncode (D1 c f) where
  gencode (M1 x) t = inModule mod . making sort $ gencode x t
    where
      mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
      sort = FObj $ qualifiedDatatypeName (undefined :: D1 c f a)


instance (Constrain a) => GConstrain (K1 i a) where
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


instance Constrain a => GDecodeFields (K1 i a) where
  gdecodeFields (v:vs) = do
    x <- decode v undefined
    return (vs, K1 x)

instance Constrain a => GEncodeFields (K1 i a) where
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
class GConstrainSum f where
  ggenAlts      :: Proxy (f a) -> Variable -> Int -> SpecType -> Gen [Variable]
  -- gstitchAlts   :: Symbol -> Gen (f a, Bool)
  gtoExprAlts   :: f a -> Expr

reproxyLeft :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (f a)
reproxyLeft = reproxy

reproxyRight :: Proxy ((c (f :: * -> *) (g :: * -> *)) a) -> Proxy (g a)
reproxyRight = reproxy

instance (GConstrainSum f, GConstrainSum g) => GConstrainSum (f :+: g) where
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

instance (GEncode f, GEncode g) => GEncode (f :+: g) where
  gencode (L1 x) t = gencode x t
  gencode (R1 x) t = gencode x t


instance (Constructor c, GConstrainProd f) => GConstrainSum (C1 c f) where
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
    -- | trace (show (c, symbol (conName (undefined :: C1 c f a)))) False = undefined
    | c == symbol (conName (undefined :: C1 c f a))
    = M1 . snd <$> gdecodeFields vs
    | otherwise
    = empty

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

gisRecursive :: (Constructor c, GConstrainProd f)
             => Proxy (C1 c f a) -> Sort -> Bool
gisRecursive (p :: Proxy (C1 c f a)) t
  = t `elem` gconArgTys (reproxyGElem p)

ggenAlt :: (Constructor c, GConstrainProd f)
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

-- gstitchAlt :: GConstrainProd f => Symbol -> Gen (C1 c f a, Bool)
-- gstitchAlt v
--   = do x <- gstitchArgs v
--        c <- getValue v
--        return (M1 x, c)

--------------------------------------------------------------------------------
--- Products
--------------------------------------------------------------------------------
class GConstrainProd f where
  gconArgTys  :: Proxy (f a) -> [Sort]
  ggenArgs    :: Proxy (f a) -> Int -> [(Symbol,SpecType)] -> Gen [Variable]
  -- gstitchArgs :: Int -> Gen (f a)
  gtoExprs    :: f a -> [Expr]

class GDecodeFields f where
  gdecodeFields :: [Symbol] -> Gen ([Symbol], f a)

class GEncodeFields f where
  gencodeFields :: f a -> [(Symbol,SpecType)] -> Gen ([Variable], [(Symbol,SpecType)])


instance (GConstrainProd f, GConstrainProd g) => GConstrainProd (f :*: g) where
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

instance (GEncodeFields f, GEncodeFields g) => GEncodeFields (f :*: g) where
  gencodeFields (f :*: g) ts = do
    (fs,ts')  <- gencodeFields f ts
    (gs,ts'') <- gencodeFields g ts'
    return (fs ++ gs, ts'')


instance (GConstrain f) => GConstrainProd (S1 c f) where
  gconArgTys p        = [gtype (reproxyGElem p)]
  ggenArgs p d (t:ts) = sequence [ggen (reproxyGElem p) (d-1) (snd t)]
  -- gstitchArgs d       = M1 <$> gstitch (d-1)
  gtoExprs (M1 x)     = [gtoExpr x]

instance GDecodeFields f => GDecodeFields (S1 c f) where
  gdecodeFields vs = do
    (vs, x) <- gdecodeFields vs
    return (vs, M1 x)

instance (GEncodeFields f) => GEncodeFields (S1 c f) where
  gencodeFields (M1 x) ts = gencodeFields x ts

instance GConstrainProd U1 where
  gconArgTys p    = []
  ggenArgs p d _  = return []
  -- gstitchArgs d   = return U1
  gtoExprs _      = []

instance GDecodeFields U1 where
  gdecodeFields vs = return (vs, U1)

instance GEncodeFields U1 where
  gencodeFields _ ts = return ([], ts)
