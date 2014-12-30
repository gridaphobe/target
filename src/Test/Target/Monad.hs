{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
module Test.Target.Monad where

import           Control.Applicative
import           Control.Arrow
import qualified Control.Exception                as Ex
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Generics                    (Data, everywhere, mkT)
import qualified Data.HashMap.Strict              as M
import qualified Data.HashSet                     as S
import           Data.IORef
import           Data.List                        hiding (sort)
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text.Lazy                   as T
import           System.IO.Unsafe
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

import           Test.Target.Types
import           Test.Target.Util

-- import           Debug.Trace


instance Symbolic T.Text where
  symbol = symbol . T.toStrict

newtype Gen a = Gen (StateT GenState (ReaderT TargetOpts IO) a)
  deriving ( Functor, Applicative, Monad, MonadIO, Alternative
           , MonadState GenState, MonadCatch, MonadReader TargetOpts )
instance MonadThrow Gen where
  throwM = Ex.throw

runGen :: TargetOpts -> GhcSpec -> FilePath -> Gen a -> IO a
runGen opts sp f (Gen x)
  = do ctx <- mkContext Z3
       runReaderT (evalStateT x (initGS f sp ctx)) opts
         `finally` killContext ctx
  where
    mkContext = if logging opts then makeContext else makeContextNoLog
    killContext ctx = terminateProcess (pId ctx) >> cleanupContext ctx

evalGen :: TargetOpts -> GenState -> Gen a -> IO a
evalGen o s (Gen x) = runReaderT (evalStateT x s) o

-- execGen :: GhcSpec -> Gen a -> IO GenState
-- execGen e (Gen x) = execStateT x (initGS e)

seed :: IORef Int
seed = unsafePerformIO $ newIORef 0
{-# NOINLINE seed #-}

freshInt :: Gen Int
freshInt = liftIO $ do
  n <- readIORef seed
  modifyIORef' seed (+1)
  return n

data TargetOpts = TargetOpts
  { depth      :: !Int
  , solver     :: !SMTSolver
  , verbose    :: !Bool
  , logging    :: !Bool
  , keepGoing  :: !Bool
    -- ^ whether to keep going after finding a counter-example, useful for
    -- checking coverage
  , maxSuccess :: !(Maybe Int)
  , scDepth    :: !Bool
    -- ^ whether to use SmallCheck's notion of depth
  }

defaultOpts :: TargetOpts
defaultOpts = TargetOpts
  { depth = 5
  , solver = Z3
  , verbose = False
  , logging = True
  , keepGoing = False
  , maxSuccess = Nothing
  , scDepth = False
  }

data GenState
  = GS { variables    :: ![Variable]
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
       , chosen       :: !(Maybe Symbol)
       , sorts        :: !(S.HashSet Sort)
       , modName      :: !Symbol
       , filePath     :: !FilePath
       , makingTy     :: !Sort
       , smtContext   :: !Context
       }

initGS :: FilePath -> GhcSpec -> Context -> GenState
initGS fp sp ctx
  = GS { variables    = []
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
       , chosen       = Nothing
       , sorts        = S.empty
       , modName      = ""
       , filePath     = fp
       , makingTy     = FObj ""
       , smtContext   = ctx
       }
  where
    dcons = tidy $ map (first symbol) (dconsP sp)
    cts   = tidy $ map (symbol *** val) (ctors sp)
    tyi   = tidy $ makeTyConInfo (tconsP sp)
    free  = tidy $ map (symbol *** symbol) $ freeSyms sp
    sigs  = tidy $ map (symbol *** val) $ tySigs sp
    meas  = tidy $ measures sp
    tidy :: forall a. Data a => a -> a
    tidy  = everywhere (mkT tidySymbol)

whenVerbose :: Gen () -> Gen ()
whenVerbose x
  = do v <- asks verbose
       when v x

noteUsed :: (Symbol, Value) -> Gen ()
noteUsed (v,x) = modify $ \s@(GS {..}) -> s { realized = (v,x) : realized }

-- TODO: does this type make sense? should it be Symbol -> Symbol -> Gen ()?
addDep :: Symbol -> Expr -> Gen ()
addDep from (EVar to) = modify $ \s@(GS {..}) ->
  s { deps = M.insertWith (flip (++)) from [to] deps }
addDep _ _ = return ()

addConstraint :: Pred -> Gen ()
addConstraint p = modify $ \s@(GS {..}) -> s { constraints = p:constraints }

addConstructor :: Variable -> Gen ()
addConstructor c
  = do -- modify $ \s@(GS {..}) -> s { constructors = S.insert c constructors }
       modify $ \s@(GS {..}) -> s { constructors = nub $ c:constructors }

inModule :: Symbol -> Gen a -> Gen a
inModule m act
  = do m' <- gets modName
       modify $ \s -> s { modName = m }
       r <- act
       modify $ \s -> s { modName = m' }
       return r

making :: Sort -> Gen a -> Gen a
making ty act
  = do ty' <- gets makingTy
       modify $ \s -> s { makingTy = ty }
       r <- act
       modify $ \s -> s { makingTy = ty' }
       return r

-- | Find the refined type of a data constructor.
lookupCtor :: Symbol -> Gen SpecType
lookupCtor c
  = do mt <- lookup c <$> gets ctorEnv
       m  <- gets filePath
       case mt of
         Just t -> return t
         Nothing -> do
           t <- io $ runGhc $ do
                  loadModule m
                  t <- GHC.exprType (printf "(%s)" (symbolString c))
                  return (ofType t)
           modify $ \s@(GS {..}) -> s { ctorEnv = (c,t) : ctorEnv }
           return t

-- | Given a data constuctor @d@ and a refined type for @d@s output,
-- return a list of 'Variable's representing suitable arguments for @d@.
unfold :: Symbol -> SpecType -> Gen [(Symbol, SpecType)]
unfold cn t = do
  dcp <- lookupCtor cn
  tyi <- gets tyconInfo
  emb <- gets embEnv
  let ts = applyPreds (addTyConInfo emb tyi t) dcp
  return ts


-- | Given a data constructor @d@ and an action, create a new choice variable
-- @c@ and execute the action while guarding any generated constraints with
-- @c@. Returns @(action-result, c)@.
guarded :: String -> Gen Expr -> Gen (Expr, Expr)
guarded cn act
  = do c  <- freshChoice cn
       mc <- gets chosen
       modify $ \s -> s { chosen = Just c }
       x <- act
       modify $ \s -> s { chosen = mc }
       return (x, EVar c)

-- | Generate a fresh variable of the given 'Sort'.
fresh :: Sort -> Gen Symbol
fresh sort
  = do n <- freshInt
       let sorts' = sortTys sort
       modify $ \s@(GS {..}) -> s { sorts = S.union (S.fromList (arrowize sort : sorts')) sorts }
       let x = symbol $ T.unpack (T.intercalate "->" $ map (T.fromStrict.symbolText.unObj) sorts') ++ show n
       modify $ \s@(GS {..}) -> s { variables = (x,sort) : variables }
       return x

sortTys :: Sort -> [Sort]
sortTys (FFunc _ ts) = concatMap sortTys ts
sortTys t            = [t]

arrowize :: Sort -> Sort
arrowize = FObj . symbol . T.intercalate "->" . map (T.fromStrict . symbolText . unObj) . sortTys

unObj :: Sort -> Symbol
unObj FInt     = "Int"
unObj (FObj s) = s
unObj s        = error $ "unObj: " ++ show s

-- | Given a data constructor @d@, create a new choice variable corresponding to
-- @d@.
freshChoice :: String -> Gen Symbol
freshChoice cn
  = do n <- freshInt
       modify $ \s@(GS {..}) -> s { sorts = S.insert choicesort sorts }
       let x = symbol $ T.unpack (smt2 choicesort) ++ "-" ++ cn ++ "-" ++ show n
       modify $ \s@(GS {..}) -> s { variables = (x,choicesort) : variables }
       return x

-- | Ask the SMT solver for the 'Value' of the given variable.
getValue :: Symbol -> Gen Value
getValue v = do
  ctx <- gets smtContext
  Values [x] <- io $ ensureValues $ command ctx (GetValue [v])
  noteUsed x
  return (snd x)

-- | Given a symbolic variable @x@, figure out which of @x@s choice varaibles
-- was picked and return it.
whichOf :: Symbol -> Gen Symbol
whichOf v = do
  deps <- gets deps
  let Just cs = M.lookup v deps
  [c]  <- catMaybes <$> forM cs (\c -> do
    val <- getValue c
    if val == "true"
      then return (Just c)
      else return Nothing)
  return c
