{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LiquidGen where

import           Control.Applicative
import           Control.Exception.Base
import "mtl"     Control.Monad.Reader
import qualified Data.Map as M
import           Data.Typeable
import           Test.QuickCheck hiding ((==>))
import           Text.Printf

import           Data.SBV
import           Language.Fixpoint.Parse
import           Language.Fixpoint.Types hiding (Symbolic)
import qualified Language.Haskell.Interpreter as Hint
import           Language.Haskell.Liquid.Parse ()
import           Language.Haskell.Liquid.Types


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




genT :: BareType -> Convert SBool
genT (RApp c as ps r)
  = gen $ toReft r
genT (RFun (S x) i o r)
  = do x' <- lift $ sInteger x
       local (M.insert x x') $ do
         lift . constrain =<< genT i
         genT o

-- blah = sat $ do x <- sInteger "x"
--                 solve [x .== 100]
--                 v <- sInteger "v"
--                 return $ v .== x + 1

gen :: Reft -> Convert SBool
gen (Reft (S v, rs))
  = do mv <- asks $ M.lookup v
       case mv of
         Nothing -> do
           v' <- lift $ sInteger v
           local (M.insert v v') go
         Just _ -> go
  where
    go = bAnd <$> mapM (ofPred . toPred) rs

toPred (RConc p) = p

type Convert = ReaderT (M.Map String SInteger) Symbolic

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

ofExpr :: Expr -> Convert SInteger
ofExpr (EVar (S s))   = asks (M.! s)
ofExpr (EBin b e1 e2) = ofBop b <$> ofExpr e1 <*> ofExpr e2
ofExpr (ECon (I i))   = return $ literal i

ofBop :: Bop -> SInteger -> SInteger -> SInteger
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
