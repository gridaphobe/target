{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.Target.Util where

import           Control.Applicative
import           Control.Monad.IO.Class
import           Data.List
import           Data.Maybe
import           Data.Monoid
import           Data.Generics                    (everywhere, mkT)
import           Data.Text.Format                hiding (print)
import qualified Data.Text.Lazy                  as LT
import           Debug.Trace

import qualified DynFlags as GHC
import qualified GhcMonad as GHC
import qualified GHC
import qualified GHC.Exts as GHC
import qualified GHC.Paths
import qualified HscTypes as GHC

import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Types          hiding (prop)
import           Language.Haskell.Liquid.CmdLine
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.PredType
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Types    hiding (var)

type Depth = Int

io ::  MonadIO m => IO a -> m a
io = liftIO

myTrace :: Show a => String -> a -> a
myTrace s x = trace (s ++ ": " ++ show x) x

reft :: SpecType -> Reft
reft = toReft . rt_reft

data HList (a :: [*]) where
  Nil   :: HList '[]
  (:::) :: a -> HList bs -> HList (a ': bs)

instance AllHave Show as => Show (HList as) where
  show Nil         = "()"
  show (x ::: Nil) = show x
  show (x ::: xs)  = show x ++ ", " ++ show xs

type family Map (f :: a -> b) (xs :: [a]) :: [b] where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

type family Constraints (cs :: [GHC.Constraint]) :: GHC.Constraint
type instance Constraints '[]       = ()
type instance Constraints (c ': cs) = (c, Constraints cs)

type AllHave (c :: k -> GHC.Constraint) (xs :: [k]) = Constraints (Map c xs)

type family Args a where
  Args (a -> b) = a ': Args b
  Args a        = '[]

type family Res a where
  Res (a -> b) = Res b
  Res a        = a

-- liquid-fixpoint started encoding `FObj s` as `Int` in 0.3.0.0, but we
-- want to preserve the type aliases for easier debugging.. so here's a
-- copy of the SMTLIB2 Sort instance..
smt2Sort :: Sort -> LT.Text
smt2Sort FInt        = "Int"
smt2Sort (FApp t []) | t == intFTyCon = "Int"
smt2Sort (FApp t []) | t == boolFTyCon = "Bool"
smt2Sort (FApp t [FApp ts _,_]) | t == appFTyCon  && fTyconSymbol ts == "Set_Set" = "Set"
smt2Sort (FObj s)    = smt2 s
smt2Sort s@(FFunc _ _) = error $ "smt2 FFunc: " ++ show s
smt2Sort _           = "Int"

makeDecl :: Symbol -> Sort -> LT.Text
-- FIXME: hack..
makeDecl x (FFunc _ ts)
  = format "(declare-fun {} ({}) {})"
           (smt2 x, LT.unwords (map smt2Sort (init ts)), smt2Sort (last ts))
makeDecl x t
  = format "(declare-const {} {})" (smt2 x, smt2Sort t)

safeFromJust :: String -> Maybe a -> a
safeFromJust msg Nothing  = error $ "safeFromJust: " ++ msg
safeFromJust _   (Just x) = x

applyPreds :: SpecType -> SpecType -> [(Symbol,SpecType)]
applyPreds sp' dc = zip xs (map tx ts)
  where
    sp = removePreds <$> sp'
    removePreds (U r _ _) = U r mempty mempty
    (as, ps, _, t) = bkUniv dc
    (xs, ts, _, _) = bkArrow . snd $ bkClass t
    -- args  = reverse tyArgs
    su    = [(tv, toRSort t, t) | tv <- as | t <- rt_args sp]
    sup   = [(p, r) | p <- ps | r <- rt_pargs sp]
    tx    = (\t -> replacePreds "applyPreds" t sup) . everywhere (mkT $ propPsToProp sup) . subsTyVars_meet su

propPsToProp
  :: [(PVar t3, Ref t (UReft t2) t1)]
     -> Ref t (UReft t2) t1 -> Ref t (UReft t2) t1
propPsToProp su r = foldr propPToProp r su

propPToProp
  :: (PVar t3, Ref t (UReft t2) t1)
     -> Ref t (UReft t2) t1 -> Ref t (UReft t2) t1
propPToProp (p, r) (RPropP _ (U _ (Pr [up]) _))
  | pname p == pname up
  = r
propPToProp _ m = m


stripQuals :: SpecType -> SpecType
stripQuals = snd . bkClass . fourth4 . bkUniv

fourth4 :: (t, t1, t2, t3) -> t3
fourth4 (_,_,_,d) = d

getSpec :: [String] -> FilePath -> IO GhcSpec
getSpec opts target
  = do cfg  <- mkOpts mempty
       info <- getGhcInfo (cfg {ghcOptions = opts}) target
       case info of
         Left err -> error $ show err
         Right i  -> return $ spec i

runGhc :: [String] -> GHC.Ghc a -> IO a
runGhc o x = GHC.runGhc (Just GHC.Paths.libdir) $ do
               df <- GHC.getSessionDynFlags
               let df' = df { GHC.ghcMode   = GHC.CompManager
                            , GHC.ghcLink   = GHC.NoLink --GHC.LinkInMemory
                            , GHC.hscTarget = GHC.HscNothing --GHC.HscInterpreted
                            -- , GHC.optLevel  = 0 --2
                            , GHC.log_action = \_ _ _ _ _ -> return ()
                            } `GHC.gopt_set` GHC.Opt_ImplicitImportQualified
                              `GHC.xopt_set` GHC.Opt_MagicHash
               (df'',_,_) <- GHC.parseDynamicFlags df' (map GHC.noLoc o)
               _ <- GHC.setSessionDynFlags df''
               x

loadModule :: FilePath -> GHC.Ghc GHC.ModSummary
loadModule f = do target <- GHC.guessTarget f Nothing
                  --lcheck <- GHC.guessTarget "src/Test/Target.hs" Nothing
                  GHC.setTargets [target] -- [target,lcheck]
                  _ <- GHC.load GHC.LoadAllTargets
                  modGraph <- GHC.getModuleGraph
                  let m = fromJust $ find ((==f) . GHC.msHsFilePath) modGraph
                  GHC.setContext [ GHC.IIModule (GHC.ms_mod_name m)
                                 --, GHC.IIDecl $ GHC.simpleImportDecl
                                 --             $ GHC.mkModuleName "Test.Target"
                                 ]
                  return m
