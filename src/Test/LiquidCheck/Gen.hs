{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
module Test.LiquidCheck.Gen where

import           Control.Applicative
import           Control.Arrow
import qualified Control.Exception                as Ex
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.State
import           Data.Default
import           Data.Generics                    (Data, Typeable, everywhere,
                                                   mkT)
import qualified Data.HashMap.Strict              as M
import qualified Data.HashSet                     as S
import           Data.List                        hiding (sort)
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text.Lazy                   as T
import           System.Process                   (terminateProcess)
import           Text.Printf

import           Language.Fixpoint.Config         (SMTSolver (..))
import           Language.Fixpoint.Names          ()
import           Language.Fixpoint.SmtLib2        hiding (verbose)
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Tidy
import           Language.Haskell.Liquid.Types

import qualified GHC

import           Test.LiquidCheck.Types
import           Test.LiquidCheck.Util


instance Symbolic T.Text where
  symbol = symbol . T.toStrict

newtype Gen a = Gen (StateT GenState IO a)
  deriving (Functor, Applicative, Monad, MonadIO, Alternative
           ,MonadState GenState, MonadCatch)
instance MonadThrow Gen where
  throwM = Ex.throw

runGen :: GhcSpec -> FilePath -> Gen a -> IO a
runGen e f (Gen x)
  = do ctx <- makeContext Z3
       evalStateT x (initGS f e ctx) `finally` (killContext ctx)
  where
    mkContext = {-if logging then makeContext else-} makeContextNoLog
    killContext ctx = terminateProcess (pId ctx) >> cleanupContext ctx

evalGen :: GenState -> Gen a -> IO a
evalGen s (Gen x) = evalStateT x s

-- execGen :: GhcSpec -> Gen a -> IO GenState
-- execGen e (Gen x) = execStateT x (initGS e)

data GenState
  = GS { seed         :: !Int
       , variables    :: ![Variable]
       , choices      :: ![Variable]
       , constraints  :: !Constraint
       , deps         :: !(M.HashMap Symbol [Symbol])
       , realized     :: ![(Symbol, Value)]
       , dconEnv      :: ![(Symbol, DataConP)]
       , ctorEnv      :: !DataConEnv
       , measEnv      :: !MeasureEnv
       , embEnv       :: !(TCEmb GHC.TyCon)
       , tyconInfo    :: !(M.HashMap GHC.TyCon RTyCon)
       , freesyms     :: ![(Symbol,Symbol)]
       , constructors :: ![Variable] -- (S.HashSet Variable)  --[(String, String)]
       , sigs         :: ![(Symbol, SpecType)]
       , depth        :: !Int
       , chosen       :: !(Maybe Variable)
       , sorts        :: !(S.HashSet Sort)
       , modName      :: !Symbol
       , filePath     :: !FilePath
       , makingTy     :: !Sort
       , verbose      :: !Bool
       , logging      :: !Bool
       , keepGoing    :: !Bool -- ^ whether to keep going after finding a
                               --   counter-example, useful for checking
                               --   coverage
       , maxSuccess   :: !(Maybe Int)
       , scDepth      :: !Bool -- ^ whether to use SmallCheck's notion of depth
       , smtContext   :: !Context
       }

initGS fp sp ctx
  = GS { seed         = 0
       , variables    = []
       , choices      = []
       , constraints  = []
       , deps         = mempty
       , realized     = []
       , dconEnv      = dcons
       , ctorEnv      = cts
       , measEnv      = meas
       , embEnv       = tcEmbeds sp
       , tyconInfo    = tyi
       , freesyms     = free
       , constructors = []
       , sigs         = sigs
       , depth        = 0
       , chosen       = Nothing
       , sorts        = S.empty
       , modName      = ""
       , filePath     = fp
       , makingTy     = FObj ""
       , verbose      = False
       , logging      = False
       , keepGoing    = False
       , maxSuccess   = Nothing
       , scDepth      = False
       , smtContext   = ctx
       }
  where
    dcons = tidy $ map (symbol *** id) (dconsP sp)
    cts   = tidy $ map (symbol *** val) (ctors sp)
    tyi   = tidy $ makeTyConInfo (tconsP sp)
    free  = tidy $ map (symbol *** symbol) $ freeSyms sp
    sigs  = tidy $ map (symbol *** val) $ tySigs sp
    meas  = tidy $ measures sp
    tidy :: forall a. Data a => a -> a
    tidy  = everywhere (mkT tidySymbol)

whenVerbose x
  = do v <- gets verbose
       when v x

noteUsed (v,x) = modify $ \s@(GS {..}) -> s { realized = (v,x) : realized }

setMaxSuccess m = modify $ \s@(GS {..}) -> s { maxSuccess = Just m }

addDep from to = modify $ \s@(GS {..}) ->
  s { deps = M.insertWith (flip (++)) (fst from) [fst to] deps }

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
                  loadModule m
                  ofType <$> GHC.exprType (printf "(%s)" (symbolString c))
           modify $ \s@(GS {..}) -> s { ctorEnv = (c,t) : ctorEnv }
           return t

withFreshChoice :: String -> (Variable -> Gen ()) -> Gen Variable
withFreshChoice cn act
  = do c  <- freshChoice cn []
       mc <- gets chosen
       modify $ \s -> s { chosen = Just c }
       act c
       modify $ \s -> s { chosen = mc }
       return c

-- | `fresh` generates a fresh variable and encodes the reachability
-- relation between variables, e.g. `fresh xs sort` will return a new
-- variable `x`, from which everything in `xs` is reachable.
fresh :: Sort -> Gen Variable
fresh sort
  = do n <- gets seed
       modify $ \s@(GS {..}) -> s { seed = seed + 1 }
       let sorts' = sortTys sort
       -- io $ print sorts'
       modify $ \s@(GS {..}) -> s { sorts = S.union (S.fromList (arrowize sort : sorts')) sorts }
       let x = (symbol $ T.unpack (T.intercalate "->" $ map (T.fromStrict.symbolText.unObj) sorts') ++ show n, sort)
       -- io $ print x
       modify $ \s@(GS {..}) -> s { variables = x : variables }
       -- mapM_ (addDep x) xs
       return x

sortTys :: Sort -> [Sort]
sortTys (FFunc _ ts) = concatMap sortTys ts
sortTys t            = [t]

arrowize :: Sort -> Sort
arrowize = FObj . symbol . T.intercalate "->" . map (T.fromStrict . symbolText . unObj) . sortTys

unObj FInt     = "Int"
unObj (FObj s) = s
unObj s        = error $ "unObj: " ++ show s

freshChoice :: String -> [Variable] -> Gen Variable
freshChoice cn xs
  = do n <- gets seed
       modify $ \s@(GS {..}) -> s { seed = seed + 1 }
       modify $ \s@(GS {..}) -> s { sorts = S.insert choicesort sorts }
       let x = (symbol $ T.unpack (smt2 choicesort) ++ "-" ++ cn ++ "-" ++ show n, choicesort)
       -- io $ print x
       modify $ \s@(GS {..}) -> s { variables = x : variables }
       -- mapM_ (addDep x) xs
       return x


getValue :: Symbol -> Gen Value
getValue v = do
  ctx <- gets smtContext
  Values [x] <- io $ ensureValues $ command ctx (GetValue [v])
  noteUsed x
  return (snd x)

whichOf :: Symbol -> Gen Symbol
whichOf v = do
  deps <- gets deps
  -- io $ print deps
  -- io $ print v
  let Just cs = M.lookup v deps
  [c]  <- catMaybes <$> forM cs (\c -> do
    val <- getValue c
    if val == "true"
      then return (Just c)
      else return Nothing)
  return c
  -- return $ head $ deps M.! c


-- pop :: Gen Value
-- pop = do (v:vs) <- gets values
--          modify $ \s@(GS {..}) -> s { values = vs }
--          return v

-- popN :: Int -> Gen [Value]
-- popN d = replicateM d pop

-- popChoice :: Gen Bool
-- popChoice = read <$> pop
--   where
--     read "true"  = True
--     read "false" = False
--     read e       = error $ "popChoice: " ++ show e

-- popChoices :: Int -> Gen [Bool]
-- popChoices n = fmap read <$> popN n
--   where
--     read "true"  = True
--     read "false" = False
--     read e       = error $ "popChoices: " ++ show e
