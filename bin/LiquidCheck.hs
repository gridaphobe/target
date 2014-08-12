{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module Main where

import           Control.Applicative
import           Control.Concurrent.Timeout
import           Control.Monad
import           Data.Char
import           Data.List
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text                  as T
import qualified Data.Text.IO               as T
import           Data.Time.Clock.POSIX
import           Data.Timeout               (TimeoutUnit (Minute), ( # ))
import           System.Directory
import           System.Environment
import           System.FilePath
import           System.IO
import           System.Process
import           Text.Printf

import qualified DynFlags                   as GHC
import qualified GHC
import qualified GHC.Exts
import qualified GHC.Paths
import qualified GhcMonad                   as GHC
import qualified HscTypes                   as GHC
import qualified Outputable                 as GHC
import qualified Type                       as GHC
import qualified TypeRep                    as GHC

import           Language.Fixpoint.Misc     (stripParens)
import           Test.LiquidCheck

findFuns :: T.Text -> [T.Text]
findFuns hs = specs `intersect` decls
  where
    specs = [spec | s <- T.lines hs
                  , "{-@" `T.isPrefixOf` s
                  , let spec = T.words s !! 1
                  , spec `notElem` ["import", "include", "data", "measure", "type", "predicate", "class"]]
    decls = [decl | d <- T.lines hs
                  , not (T.null d)
                  , not (isSpace $ T.head d)
                  , let decl = head (T.words d)]

findModule :: T.Text -> T.Text
findModule hs = case [m | "module":m:_ <- T.words <$> T.lines hs] of
                  [] -> "Main"
                  m:_ -> m

main = do
  f:time:monos <- getArgs
  hs  <- T.readFile f
  tpl <- T.readFile "bin/CheckFun.template.hs"
  (m,fs) <- findModuleFuns f (pairs monos)
  createDirectoryIfMissing True "_results"
  let funs     = T.intercalate "\n       ," $
                  map (\(f,t) ->
                        "(T (" <> f <> " :: " <> t <> "), \"" <> stripParens f <> "\")")
                  fs
      contents = subst tpl [ ("$module$", m), ("$file$", T.pack f)
                           , ("$timeout$", T.pack time)
                           , ("$funs$", funs)
                           ]
      path     = (reverse . drop 3 . reverse $ f) ++ "Coverage.hs"
  T.writeFile path contents

pairs :: [String] -> [(String,String)]
pairs [] = []
pairs (x:y:zs) = (x,y) : pairs zs

findModuleFuns :: FilePath -> [(String,String)] -> IO (T.Text, [(T.Text,T.Text)])
findModuleFuns file monos = runGhc $ do
  m     <- loadModule file
  let modName = T.pack $ GHC.moduleNameString $ GHC.ms_mod_name m
  names <- GHC.modInfoExports . fromJust <$> GHC.getModuleInfo (GHC.ms_mod m)
  hs    <- GHC.liftIO (T.readFile file)
  let specs = [ stripParens spec
              | s <- T.lines hs
              , "{-@" `T.isPrefixOf` s
              , let ws = T.words s
              , length ws > 1
              , let spec = ws !! 1
              ]
  df  <- GHC.getSessionDynFlags
  let funs = [ f | f <- T.pack . showInModule df GHC.neverQualify <$> names, f `elem` specs]
  int <- GHC.exprType "1 :: Int"
  monos' <- forM monos $ \(v,t) -> (v,) <$> GHC.exprType ("undefined :: " ++ t)
  funTys <- forM funs $ \f -> do
    let f' = ("(" <> modName <> "." <> f <> ")")
    t    <- monomorphic df int monos' <$> GHC.exprType (T.unpack f')
    return (f', T.pack $ concat $ lines $ showInModule df (\_ _ -> GHC.NameQual $ GHC.ms_mod_name m, const False) t)
  return (modName, funTys)

showInModule df m = GHC.showSDocForUser df m . GHC.ppr

subst :: T.Text -> [(T.Text, T.Text)] -> T.Text
subst = foldr (\(x,y) t -> T.replace x y t)

mkPath f fun = dropExtensions f <.> T.unpack fun <.> ".hs"

--monomorphize :: FilePath -> T.Text -> IO T.Text
--monomorphize file fun = runGhc $ do
--  loadModule file
--  df  <- GHC.getSessionDynFlags
--  int <- GHC.exprType "1 :: Int"
--  t   <- monomorphic df int <$> GHC.exprType (T.unpack fun)
--  let showInModule = GHC.showSDocForUser df GHC.neverQualify . GHC.ppr
--  return $ T.pack (showInModule t)

monomorphic :: GHC.DynFlags -> GHC.Type -> [(String,GHC.Type)] -> GHC.Type -> GHC.Type
monomorphic df int monos (GHC.TyVarTy v)
  | Just t <- lookup (GHC.showPpr df v) monos = t
  | otherwise                                 = int
monomorphic df int monos (GHC.AppTy x y)
  = GHC.AppTy (monomorphic df int monos x) (monomorphic df int monos y)
monomorphic df int monos (GHC.TyConApp t ts)
  = GHC.TyConApp t $ map (monomorphic df int monos) ts
monomorphic df int monos (GHC.FunTy i o)
  | GHC.isClassPred i = monomorphic df int monos o
  | otherwise         = GHC.FunTy (monomorphic df int monos i) (monomorphic df int monos o)
monomorphic df int monos (GHC.ForAllTy a t)
  = monomorphic df int monos t
monomorphic df int monos t
  = error $ "Don't know how to monomorphize " ++ GHC.showPpr df t

mkLiquidCheck d path m fun ty
  = printf "Test.LiquidCheck.testOne %d (%s :: %s) \"%s\" \"%s\""
           d fun ty (m++"."++fun) path

data Outcome = Completed Result
             | TimedOut
             deriving (Show)

checkMany :: FilePath -> String -> String -> String -> IO [(Int, Double, Outcome)]
checkMany path mod fun ty = go 2
  where
    go 11     = return []
    go n      = checkAt n >>= \case
                  (d,Nothing) -> return [(n,d,TimedOut)]
                  (d,Just r)  -> ((n,d,Completed r):) <$> go (n+1)
    checkAt :: Int -> IO (Double, Maybe Result)
    checkAt n = do (test :: IO Result) <- runGhc $ do
                     loadModule path
                     let liquidCheck = mkLiquidCheck n path mod fun ty
                     GHC.liftIO $ print liquidCheck
                     GHC.Exts.unsafeCoerce# <$> GHC.compileExpr liquidCheck
                   putStrNow (printf "%d " n)
                   timed $ timeout timeLimit test

timeLimit = 5 # Minute

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

putStrNow s = putStr s >> hFlush stdout

runGhc x = GHC.runGhc (Just GHC.Paths.libdir) $ do
             df <- GHC.getSessionDynFlags
             let df' = df { GHC.ghcMode   = GHC.CompManager
                          , GHC.ghcLink   = GHC.NoLink
                          , GHC.hscTarget = GHC.HscNothing
                          -- , GHC.optLevel  = 2
                          , GHC.importPaths = ["examples", "src"]
                          -- , GHC.verbosity = 3
                          -- , GHC.includePaths  = ["src"]
                          } `GHC.gopt_set` GHC.Opt_ImplicitImportQualified
             GHC.setSessionDynFlags df'
             x

loadModule f = do target <- GHC.guessTarget f Nothing
                  --lcheck <- GHC.guessTarget "src/Test/LiquidCheck.hs" Nothing
                  GHC.setTargets [target] -- [target,lcheck]
                  GHC.load GHC.LoadAllTargets
                  modGraph <- GHC.getModuleGraph
                  let m = fromJust $ find ((==f) . GHC.msHsFilePath) modGraph
                  GHC.setContext [ GHC.IIModule (GHC.ms_mod_name m)
                                 -- , GHC.IIDecl $ GHC.simpleImportDecl
                                 --              $ GHC.mkModuleName "Test.LiquidCheck"
                                 ]
                  return m
