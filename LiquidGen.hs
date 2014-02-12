{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import           Control.Applicative
import           Control.Arrow (second)
import           Control.Exception.Base
import "mtl"     Control.Monad.Reader
import           Data.Data
import           Data.Dynamic
import           Data.Function
import           Data.List
import qualified Data.Map as M
import           Data.Maybe
import           Data.Tuple
import           Data.Typeable
import           Test.QuickCheck hiding ((==>))
import           Text.Printf

import           Data.SBV
import           Data.SBV.Internals
import           Language.Fixpoint.Parse
import           Language.Fixpoint.Types hiding (Symbolic)
import qualified Language.Haskell.Interpreter as Hint
import           Language.Haskell.Liquid.Parse ()
import           Language.Haskell.Liquid.Types

import           Debug.Trace

{-

NOTES
-----

QuickCheck actually has special cases for some values that are
difficult to generate, e.g. sorted lists. The approach is to generate
arbitrary values and then apply the predicate to them:

    sort <$> vector 10 :: Gen [Int]

This is of course orders of magnitude faster than contraining the
generator to produce pre-sorted lists

    vector 10 `suchThat` isSorted :: Gen [Int]

Are there cases where we can't rely on post-processing to ensure a
property holds? Sure

    arbitrary `suchThat` \(x,y,z) -> y == f x && z == g y

For some sufficiently complex `f` and `g`.

-}


convert = flip runReaderT M.empty

test s = runReaderT (genT (rr s :: BareType)) M.empty

test' spec func
  = do let (cs, r) = genPrePost $ rr spec
       sats <- take 20 . extractModels <$> allSat (runReaderT cs M.empty)
       f    <- eval func
       -- FIXME: this is specializing to function of single arg, must generalize
       forM_ sats $ \x -> do
         v <- evaluate (show $ f x) `catch` \(_ :: SomeException) -> return "CRASH"
         b <- evaluate (evalReft (M.fromList [("x",x)]) r (f x))
              `catch` \(_ :: SomeException) -> return False
         let k = if b
                 then "SAFE"
                 else "UNSAFE"
         printf "%s:\tx = %d, f x = %s\n" k x v

allSat' :: Provable a => a -> IO AllSatResult
allSat' = allSatWith defaultSMTCfg{ timeOut = Just 10, Data.SBV.verbose = True }

sat' :: Provable a => a -> IO SatResult
sat' = satWith defaultSMTCfg{ timeOut = Just 10, Data.SBV.verbose = True }

eval :: Typeable a => String -> IO a
eval s = do r <- Hint.runInterpreter $ do Hint.setImportsQ [("Prelude", Nothing)]
                                          Hint.interpret s Hint.infer
            case r of
              Left err -> error $ show err
              Right v  -> return v

genPrePost :: BareType -> (Convert SBool, Reft)
genPrePost t = (genT t', r)
  where
    (xs, ts, rt) = bkArrow t
    t' = mkArrow [] [] (zip (init xs) (init ts)) (last ts)
    r  = toReft $ rt_reft rt

foo :: BareType
foo = rr "{v:[a] | (len v) = 5}"


main = print =<< (allSat' $ convert $ genList 5 foo)

deSat (SatResult s) = s

-- shape :: SMTResult -> [[(String,CW)]]
-- shape (Satisfiable _ m) = groupBy ((==) `on` snd) $ modelAssocs m
shape (Satisfiable _ m) = M.fromListWith (++) $ map (second (:[]) . swap)
                        $ modelAssocs m


boo :: Symbolic SBool
boo = do x :: SInteger <- free "x"
         y :: SInteger <- free "x"
         return $ x .== y



data L a = N | C a (L a) deriving (Eq, Ord, Read, Show, Data, Typeable)

instance (Data a, HasKind a) => HasKind [a] where
  kindOf _ = KUninterpreted $ "list" -- ++ showType (undefined :: a)
instance (Data a, Ord a, HasKind a) => SymWord [a]

instance (Data a, HasKind a) => HasKind (L a) where
instance (Data a, Ord a, HasKind a) => SymWord (L a)

type SList a = SBV (L a)

-- len :: (Data a, SymWord a) => SList a -> SInteger
len :: SInteger -> SInteger
len = uninterpret "len"

genList :: Int -> BareType -> Convert SBool
genList n (RApp _ [a] _ r)
  = do nil :: SInteger <- lift $ free "nil"
       lift $ constrain $ len nil .== 0
       ls <- foldrM foo [nil] =<< replicateM n (lift free_)
       l <- lift $ free "l"
       lift $ constrain $ bOr [l .== l' | l' <- nil:ls]
       local (M.insert "len" (toDyn (\[x::SInteger] -> len x)) . M.insert "v" (toDyn l)) $ gen $ toReft r
  where
    -- foo :: SList Integer -> [SList Integer] -> Convert [SList Integer]
    foo l (l':ls) = do lift $ constrain $ len l .== len l' + 1

                       return $ l:l':ls

foldrM :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
foldrM f z []     = return z
foldrM f z (x:xs) = do xs' <- foldrM f z xs
                       f x xs'

unfold f z
  = case f z of
      Nothing -> []
      Just z' -> z' : unfold f z'


-- unfoldM :: (Functor m, Monad m) => (b -> m (Maybe (a, b))) -> b -> m [a]
unfoldM f b
  = do mx <- f b
       case mx of
         Nothing     -> return []
         Just (a,b') -> traceShow a $ (a:) <$> unfoldM f b'

genT :: BareType -> Convert SBool
genT (RApp c as ps r)
  = gen $ toReft r
genT (RFun (S x) i o r)
  = do x' <- lift $ sInteger x
       local (M.insert x (toDyn x')) $ do
         lift . constrain =<< genT i
         genT o

-- blah = sat $ do x <- sInteger "x"
--                 solve [x .== 100]
--                 v <- sInteger "v"
--                 return $ v .== x + 1

gen :: Reft -> Convert SBool
gen (Reft (S v, rs))
  = do mv <- asks (M.lookup v)
       case mv of
         Nothing -> do
           v' <- lift $ sInteger v
           local (M.insert v (toDyn v')) go
         Just _ -> go
  where
    go = bAnd <$> mapM (ofPred . toPred) rs

toPred (RConc p) = p

-- type Convert = ReaderT (M.Map String SInteger) Symbolic
type Convert = ReaderT (M.Map String Dynamic) Symbolic

ofPred :: Pred -> Convert SBool
ofPred PTrue           = return true
ofPred PFalse          = return false
ofPred (PAnd ps)       = bAnd <$> mapM ofPred ps --foldr (\x y -> ofPred x &&& y) true ps
ofPred (POr ps)        = bOr  <$> mapM ofPred ps --foldr (\x y -> ofPred x ||| y) false ps
ofPred (PNot p)        = bnot <$> ofPred p
ofPred (PImp p q)      = (==>) <$> ofPred p <*> ofPred q
ofPred (PIff p q)      = (<=>) <$> ofPred p <*> ofPred q
ofPred (PBexp e)       = undefined -- ofExpr e
ofPred (PAtom b e1 e2) = ofBrel b <$> ofExpr e1 <*> ofExpr e2
ofPred (PAll ss p)     = undefined
ofPred PTop            = undefined

ofBrel Eq = (.==)
ofBrel Ne = (./=)
ofBrel Gt = (.>)
ofBrel Ge = (.>=)
ofBrel Lt = (.<)
ofBrel Le = (.<=)

ofExpr :: (Typeable a, OrdSymbolic a) => Expr -> Convert a
ofExpr (EVar (S s))   = fromD <$> asks (M.! s)
ofExpr (EBin b e1 e2) = ofBop b <$> ofExpr e1 <*> ofExpr e2
ofExpr (ECon (I i))   = return $ literal i
ofExpr (EApp f es)    = asks (M.! (show $ val f)) >>= \f ->
  (fromD f ) <$> (mapM ofExpr es)

-- ofBop :: Bop -> SInteger -> SInteger -> SInteger
ofBop Plus  = (+)
ofBop Minus = (-)
ofBop Times = (*)
ofBop Div   = sDiv
ofBop Mod   = sMod


evalReft :: M.Map String Integer -> Reft -> Integer -> Bool
evalReft m (Reft (S v, rs)) x = and [ fromPred p (M.insert v x m)
                                    | r <- rs, let p = toPred r
                                    ]

fromPred :: Pred -> M.Map String Integer -> Bool
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

--------------------------------------------------------------------------------
--- STUPID Functor -> Applicative -> Monad NONSENSE
--------------------------------------------------------------------------------

instance Applicative Symbolic where
  pure  = return
  f <*> x = do f <- f
               x <- x
               return $ f x

deriving instance Typeable1 SBV

fromD :: (Typeable a) => Dynamic -> a
fromD d = fromDyn d (error $ "fromDyn: WRONG TYPE!!! " ++ show d)
