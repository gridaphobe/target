{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE BangPatterns #-}
module Test.LiquidCheck.Util where

import           Control.Applicative
import           Control.Exception
import           Control.Monad.IO.Class
import           Data.List
import           Data.Maybe
import           Data.Monoid
import           Data.Generics                    (everywhere, mkT)
import           Debug.Trace
import           GHC.IO.Handle
import           System.IO

import qualified DynFlags as GHC
import qualified GHC
import qualified GHC.Paths
import qualified HscTypes as GHC

import           Language.Fixpoint.Types          hiding (prop)
import           Language.Haskell.Liquid.CmdLine
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types    hiding (var)

io ::  MonadIO m => IO a -> m a
io = liftIO

myTrace :: Show a => String -> a -> a
myTrace s x = trace (s ++ ": " ++ show x) x

type family Args a where
  Args (a -> b -> c -> d -> e) = (a,b,c,d)
  Args (a -> b -> c -> d) = (a,b,c)
  Args (a -> b -> c) = (a,b)
  Args (a -> b) = a

type family Res a where
  Res (a -> b -> c -> d -> e) = e
  Res (a -> b -> c -> d) = d
  Res (a -> b -> c) = c
  Res (a -> b) = b

safeFromJust :: String -> Maybe a -> a
safeFromJust msg Nothing  = error $ "safeFromJust: " ++ msg
safeFromJust _   (Just x) = x

applyPreds :: SpecType -> SpecType -> [(Symbol,SpecType)]
applyPreds sp' dc = zip xs (map tx ts)
  where
    sp = removePreds <$> sp'
    removePreds (U r _ _) = (U r mempty mempty)
    (as, ps, _, t) = bkUniv dc
    (xs, ts, rt)   = bkArrow . snd $ bkClass t
    -- args  = reverse tyArgs
    su    = [(tv, toRSort t, t) | tv <- as | t <- rt_args sp]
    sup   = [(p, r) | p <- ps | r <- rt_pargs sp]
    tx    = (\t -> replacePreds "applyPreds" t sup) . everywhere (mkT $ monosToPoly sup) . subsTyVars_meet su

-- deriving instance (Show a, Show b, Show c) => Show (Ref a b c)

-- onRefs f t@(RVar _ _) = t
-- onRefs f t = t { rt_pargs = f <$> rt_pargs t }

monosToPoly su r = foldr monoToPoly r su

monoToPoly (p, r) (RMono _ (U _ (Pr [up]) _))
  | pname p == pname up
  = r
monoToPoly _ m = m


stripQuals = snd . bkClass . fourth4 . bkUniv

fourth4 (_,_,_,d) = d

getSpec :: FilePath -> IO GhcSpec
getSpec target
  = do cfg  <- mkOpts mempty
       info <- getGhcInfo cfg target
       case info of
         Left err -> error $ show err
         Right i  -> return $ spec i

runGhc x = GHC.runGhc (Just GHC.Paths.libdir) $ do
             df <- GHC.getSessionDynFlags
             let df' = df { GHC.ghcMode   = GHC.CompManager
                          , GHC.ghcLink   = GHC.NoLink --GHC.LinkInMemory
                          , GHC.hscTarget = GHC.HscNothing --GHC.HscInterpreted
                          , GHC.optLevel  = 0 --2
                          } `GHC.gopt_set` GHC.Opt_ImplicitImportQualified
                            `GHC.xopt_set` GHC.Opt_MagicHash
             GHC.setSessionDynFlags df'
             x

loadModule f = do target <- GHC.guessTarget f Nothing
                  --lcheck <- GHC.guessTarget "src/Test/LiquidCheck.hs" Nothing
                  GHC.setTargets [target] -- [target,lcheck]
                  GHC.load GHC.LoadAllTargets
                  modGraph <- GHC.getModuleGraph
                  let m = fromJust $ find ((==f) . GHC.msHsFilePath) modGraph
                  GHC.setContext [ GHC.IIModule (GHC.ms_mod_name m)
                                 --, GHC.IIDecl $ GHC.simpleImportDecl
                                 --             $ GHC.mkModuleName "Test.LiquidCheck"
                                 ]
                  return m
