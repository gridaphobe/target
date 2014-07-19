{-# LANGUAGE MagicHash #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import           Control.Applicative
import           Control.Monad
import           Data.Char
import           Data.List
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Time.Clock.POSIX
import           System.Environment
import           System.FilePath
import           System.IO
import           System.Process
import           System.Timeout
import           Text.Printf

import qualified DynFlags as GHC
import qualified GHC
import qualified GHC.Exts
import qualified GHC.Paths
import qualified HscTypes as GHC

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
  [f] <- getArgs
  hs  <- T.readFile f
  tpl <- T.readFile "bin/CheckFun.template.hs"
  let m  = findModule hs
      fs = findFuns hs
  forM_ fs $ \fun -> do
    let contents = subst tpl [ ("$module$", m), ("$file$", T.pack f), ("$fun$", m<>"."<>fun)]
        path     = mkPath f fun
    T.writeFile path contents
    system $ printf "ghc --make -O2 %s -i%s" path (takeDirectory path)
    system $ printf "cabal exec %s" $ dropExtension path
  -- print m
  -- print fs
  -- forM_ fs $ \fun -> do
  --   putStrNow (fun ++ ": ")
  --   rs <- checkMany f m fun
  --   putStrLn "done"
  --   forM_ rs $ \(d,t,r) -> printf "%d\t%.2f\t%s\n" d t (show r)
  --   putStrLn ""
  -- tests :: [IO Result] <- runGhc $ do
  --   loadModule f
  --   forM fs $ \fun -> do
  --     hv <- GHC.compileExpr $ mkLiquidCheck f m fun
  --     return $ GHC.Exts.unsafeCoerce# hv
  -- mapM_ print =<< sequence tests

subst :: T.Text -> [(T.Text, T.Text)] -> T.Text
subst = foldr (\(x,y) t -> T.replace x y t)

mkPath f fun = dropExtensions f <.> T.unpack fun <.> ".hs"

mkLiquidCheck d path m fun
  = printf "Test.LiquidCheck.testOne %d %s \"%s\" \"%s\""
           d fun (m++"."++fun) path

data Outcome = Completed Result
             | TimedOut
             deriving (Show)

checkMany :: FilePath -> String -> String -> IO [(Int, Double, Outcome)]
checkMany path mod fun = go 2
  where
    go n      = checkAt n >>= \case
                  (d,Nothing) -> return [(n,d,TimedOut)]
                  (d,Just r)  -> ((n,d,Completed r):) <$> go (n+1)
    checkAt n = do test <- runGhc $ do
                     loadModule path
                     GHC.Exts.unsafeCoerce# <$> GHC.compileExpr (mkLiquidCheck n path mod fun)
                   putStrNow (printf "%d " n)
                   timed $ timeout tenMinutes test

tenMinutes = 2 * 60 * 1000000

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
                          , GHC.ghcLink   = GHC.LinkInMemory
                          , GHC.hscTarget = GHC.HscInterpreted
                          , GHC.optLevel  = 2
                          } `GHC.dopt_set` GHC.Opt_ImplicitImportQualified
             GHC.setSessionDynFlags df'
             x

loadModule f = do target <- GHC.guessTarget f Nothing
                  -- lcheck <- GHC.guessTarget "Test.LiquidCheck" Nothing
                  GHC.setTargets [target]
                  GHC.load GHC.LoadAllTargets
                  modGraph <- GHC.getModuleGraph
                  let m = fromJust $ find ((==f) . GHC.msHsFilePath) modGraph
                  GHC.setContext [ GHC.IIModule (GHC.ms_mod_name m)
                                 , GHC.IIDecl $ GHC.simpleImportDecl
                                              $ GHC.mkModuleName "Test.LiquidCheck"
                                 ]
