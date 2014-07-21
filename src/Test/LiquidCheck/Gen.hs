{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE OverloadedStrings          #-}
module Test.LiquidCheck.Gen where

import           Control.Applicative
import           Control.Arrow
import           Control.Exception
import           Control.Monad
import           Control.Monad.State
import           Data.Default
import qualified Data.HashMap.Strict              as M
import qualified Data.HashSet                     as S
import           Data.List
import           Data.Monoid
import qualified Data.Text.Lazy                   as T

import           Language.Fixpoint.Config  (SMTSolver(..))
import           Language.Fixpoint.SmtLib2 hiding (verbose)
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types

import qualified GHC

import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util


newtype Gen a = Gen (StateT GenState IO a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadState GenState)

runGen :: GhcSpec -> FilePath -> Gen a -> IO a
runGen e f (Gen x) = bracket (makeContext Z3) cleanupContext
                             (evalStateT x . initGS f e)
  -- = do ctx <- makeContext Z3
  --      a <- evalStateT act (initGS e ctx)
  --      cleanupContext ctx
  --      return a

evalGen :: GenState -> Gen a -> IO a
evalGen s (Gen x) = evalStateT x s

-- execGen :: GhcSpec -> Gen a -> IO GenState
-- execGen e (Gen x) = execStateT x (initGS e)

data GenState
  = GS { seed         :: !Int
       , variables    :: ![Variable]
       , choices      :: ![Variable]
       , constraints  :: !Constraint
       , values       :: ![Value]
       , deps         :: ![(Symbol, Symbol)]
       , dconEnv      :: ![(Symbol, DataConP)]
       , ctorEnv      :: !DataConEnv
       , measEnv      :: !MeasureEnv
       , tyconInfo    :: !(M.HashMap GHC.TyCon RTyCon)
       , freesyms     :: ![(Symbol,Symbol)]
       , constructors :: ![Variable] -- (S.HashSet Variable)  --[(String, String)]
       , sigs         :: ![(Symbol, SpecType)]
       , depth        :: !Int
       , chosen       :: !(Maybe Variable)
       , sorts        :: !(S.HashSet T.Text)
       , modName      :: !Symbol
       , filePath     :: !Symbol
       , makingTy     :: !Symbol
       , verbose      :: !Bool
       , logging      :: !Bool
       , smtContext   :: !(Context)
       } -- deriving (Show)

initGS fp sp ctx = GS def def def def def def dcons cts (measures sp) tyi free [] sigs def Nothing S.empty "" (symbol fp) "" False False ctx
  where
    dcons = map (symbol *** id) (dconsP sp)
    cts   = map (symbol *** val) (ctors sp)
    tyi   = makeTyConInfo (tconsP sp)
    free  = map (second symbol) $ freeSyms sp
    sigs  = map (symbol *** val) $ tySigs sp

whenVerbose x
  = do v <- gets verbose
       when v x

setValues vs = modify $ \s@(GS {..}) -> s { values = vs }

addDep from to = modify $ \s@(GS {..}) -> s { deps = (fst from, fst to):deps }

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

lookupCtor :: Symbol -> Gen SpecType
lookupCtor c
  = do mt <- lookup c <$> gets ctorEnv
       m  <- gets filePath
       case mt of
         Just t -> return t
         Nothing -> do
           t <- io $ runGhc $ do
                  loadModule (show m)
                  ofType <$> GHC.exprType (show c)
           modify $ \s@(GS {..}) -> s { ctorEnv = (c,t) : ctorEnv }
           return t

withFreshChoice :: (Variable -> Gen ()) -> Gen Variable
withFreshChoice act
  = do c  <- freshChoice []
       mc <- gets chosen
       modify $ \s -> s { chosen = Just c }
       act c
       modify $ \s -> s { chosen = mc }
       return c

-- | `fresh` generates a fresh variable and encodes the reachability
-- relation between variables, e.g. `fresh xs sort` will return a new
-- variable `x`, from which everything in `xs` is reachable.
fresh :: [Variable] -> Sort -> Gen Variable
fresh xs sort
  = do n <- gets seed
       modify $ \s@(GS {..}) -> s { seed = seed + 1 }
       modify $ \s@(GS {..}) -> s { sorts = S.insert (smt2 sort) sorts }
       let x = (symbol $ T.unpack (smt2 sort) ++ show n, sort)
       modify $ \s@(GS {..}) -> s { variables = x : variables }
       mapM_ (addDep x) xs
       return x

freshChoice :: [Variable] -> Gen Variable
freshChoice xs
  = do c <- fresh xs choicesort
       modify $ \s@(GS {..}) -> s { choices = c : choices }
       return c



pop :: Gen Value
pop = do (v:vs) <- gets values
         modify $ \s@(GS {..}) -> s { values = vs }
         return v

popN :: Int -> Gen [Value]
popN d = replicateM d pop

popChoice :: Gen Bool
popChoice = read <$> pop
  where
    read "true"  = True
    read "false" = False
    read e       = error $ "popChoice: " ++ show e

popChoices :: Int -> Gen [Bool]
popChoices n = fmap read <$> popN n
  where
    read "true"  = True
    read "false" = False
    read e       = error $ "popChoices: " ++ show e
