{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LiquidSMT where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad.State
import           Data.List
import           Data.Maybe
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


driver :: Constrain a => Int -> BareType -> a -> IO a
driver d t v
  = do let (cs, vs) = runGen $ constrain d v t
           cts      = ctors v
           consts   = filter (notFun . snd) cts
           notFun (FFunc _ _) = False
           notFun _           = True
       ctx <- makeContext Z3
       mapM_ (\ (x,t)  -> command ctx $ makeDecl x t) cts
       mapM_ (\ x      -> command ctx $ Declare (symbol x) [] FInt) vs
       command ctx $ Declare (stringSymbol "len") [FInt] FInt
       smtWrite ctx "(assert (forall ((x Int)) (=> (= x nil) (= (len x) 0))))"
       mapM_ (command ctx .  Assert) cs
       print =<< command ctx CheckSat
       Values vals <- command ctx (GetValue $ map symbol vs ++ map fst consts)
       print vals
       let x = runCons (map (first symbolString) vals) $ construct d
       cleanupContext ctx
       return x

makeDecl x (FFunc _ ts) = Declare x (init ts) (last ts)
makeDecl x t            = Declare x []        FInt

type Constraint = [Pred]
type Value      = String

instance SMTLIB2 Constraint where
  smt2 = smt2 . PAnd

class Constrain a where
  constrain :: Int -> a -> BareType -> Gen (Constraint, [String])
  construct :: Int -> Cons a
  ctors     :: a -> [(Symbol, Sort)]

type Gen  = State Int
type Cons = State [(String,Value)]

fresh :: Gen Int
fresh = do i <- get
           modify (+1)
           return i

runGen :: Gen a -> a
runGen x = evalState x 0

pop :: Cons (String,Value)
pop = do (sv:svs) <- get
         put svs
         return sv

runCons :: [(String,Value)] -> Cons a -> a
runCons svs act = evalState act svs

instance Constrain Int where
  constrain _ _ (RApp _ [] _ r) = do x <- freshen "v"
                                     return $ (ofReft x $ toReft r, [x])
  construct _ = do (_,v) <- pop
                   return $ read v
  ctors _ = []

instance Constrain a => Constrain [a] where
  constrain d _ (RApp _ [a] _ r) = act -- (concat cs, concat vs)
    where
      act = do (cs,xs) <- (concat *** concat) . unzip <$> unfoldrNM d build nil
               l <- freshen "list"
               let ls = filter ("list" `isPrefixOf`) xs
                   c  = pOr $ map (var l `eq`) (nil : map var ls)
                   cr = ofReft l $ toReft r
               return (cr ++ c:cs, l:xs)
      build l = do l' <- var <$> freshen "list"
                   (cs, v:vs) <- constrain d (undefined :: a) a
                   let c = l' `eq` cons (var v) l
                   return ((c:cs, showpp l':v:vs), l')
      -- build l = let l'     = freshen "list"
      --               (cs,v:vs)  = constrain d (undefined :: a) a
      --               c = l' `eq` cons (var v) l
      --           in Just ((c:cs, showpp l':v:vs), l')
  -- construct d svs = (ls,rest)
  --   where
  --     (lvs,rest)              = first toQuads $ splitAt (d*2) svs
  --     toQuads []              = []
  --     toQuads ((x,y):(z,w):r) = (x,y,z,w) : toQuads r
  --     ls                      = scanl build ("nil",[]) lvs
  --     build (_,l) (_,x,_,v)   = (x,v:l)
  construct d = do (_,x) <- pop
                   ls    <- unfoldrNM d build []
                   n     <- fromJust . lookup "nil" <$> get
                   return $ fromJust $ lookup (traceShow x x) ((n, []):ls)
    where
      build l = do (_,v) <- pop
                   x::a  <- construct d
                   return ((v,x:l),x:l)
  ctors _ = [(stringSymbol "nil", FInt), (stringSymbol "cons", FFunc 2 [FInt, FInt, FInt])]

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

freshen :: String -> Gen String
freshen x = fresh >>= return . (x++) . show

-- var :: String -> SMT.Expr
-- var = flip SMT.app [] . fromString

var :: String -> Expr
var = EVar . symbol

len :: SMT.Expr -> SMT.Expr
len x = SMT.app "len" [x]

-- nil :: SMT.Expr
-- nil = var "nil"

nil :: Expr
nil = EVar $ stringSymbol "nil"

-- cons :: SMT.Expr -> SMT.Expr -> SMT.Expr
-- cons x xs = SMT.app "cons" [x,xs]

cons :: Expr -> Expr -> Expr
cons x xs = EApp (dummyLoc $ stringSymbol "cons") [x,xs]


--------------------------------------------------------------------------------
--- test data
--------------------------------------------------------------------------------

t :: BareType
t = rr "{v:[{v0:Int | v0 >= 0}] | (len v) > 0}"


list :: [Int]
list = []
