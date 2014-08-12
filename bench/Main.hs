{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}
module Main where

import           Test.LiquidCheck
import           Test.LiquidCheck.Types
import qualified Test.QuickCheck            as QC
import qualified Test.SmallCheck            as SC
import qualified Test.SmallCheck.Drivers    as SC

import           Control.Applicative
import           Control.Concurrent.Timeout
import           Data.IORef
import           Data.Time.Clock.POSIX
import           Data.Timeout
import           System.IO
import           Text.Printf

import qualified Expr
import qualified List
import qualified MapBench                   as Map
import qualified RBTree
import qualified XMonad.Properties          as XMonad

data Outcome = TimeOut
             | Complete !Int
             | GaveUp !Int
             deriving (Read, Show)

data TestResult
  = TestResult { liquid :: ![(Int,Double,Outcome)]
               , small  :: ![(Int,Double,Outcome)]
               , quick  :: !(Double,Outcome)
               } deriving (Read, Show)

main :: IO ()
main = do
  print =<< listInsertTests
  print =<< rbTreeAddTests
  print =<< exprSubstTests
  print =<< mapDeleteTests
  print =<< mapDifferenceTests
  print =<< xmonadFocusLeftTests

listInsertTests = do
  l <- checkLiquid List.insert         "List.insert" "examples/List.hs"
  s <- checkSmall  List.prop_insert_sc "List.insert"
  q <- checkQuick  List.prop_insert_qc "List.insert"
  return $ TestResult l s q

rbTreeAddTests = do
  l <- checkLiquid RBTree.prop_add_lc "RBTree.add" "examples/RBTree.hs"
  s <- checkSmall  RBTree.prop_add_sc "RBTree.add"
  q <- checkQuick  RBTree.prop_add_qc "RBTree.add"
  return $ TestResult l s q

exprSubstTests = do
  l <- checkLiquid Expr.subst         "Expr.subst" "examples/Expr.hs"
  s <- checkSmall  Expr.prop_subst_sc "Expr.subst"
  q <- checkQuick  Expr.prop_subst_qc "Expr.subst"
  return $ TestResult l s q

mapDeleteTests = do
  l <- checkLiquid Map.prop_delete_lc "Map.delete" "examples/Map.hs"
  s <- checkSmall  Map.prop_delete_sc "Map.delete"
  q <- checkQuick  Map.prop_delete_qc "Map.delete"
  return $ TestResult l s q

mapDifferenceTests = do
  l <- checkLiquid Map.prop_difference_lc "Map.difference" "examples/Map.hs"
  s <- checkSmall  Map.prop_difference_sc "Map.difference"
  q <- checkQuick  Map.prop_difference_qc "Map.difference"
  return $ TestResult l s q

xmonadFocusLeftTests = do
  l <- checkLiquid XMonad.prop_focus_left_master_lc "XMonad.Properties.prop_focus_left_master_lc"
                                                    "examples/XMonad/Properties.hs"
  s <- checkSmall  XMonad.prop_focus_left_master_sc "XMonad.Properties.prop_focus_left_master"
  q <- checkQuick  XMonad.prop_focus_left_master_qc "XMonad.Properties.prop_focus_left_master"
  return $ TestResult l s q


myTimeout :: IO a -> IO (Maybe a)
myTimeout = timeout (1 # Minute)

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

checkLiquid :: CanTest f => f -> String -> FilePath -> IO [(Int,Double,Outcome)]
checkLiquid f n m = checkMany (n++"/LiquidCheck")
                              (\d -> resultPassed <$> testOne f n d m)

checkSmall p n = checkMany (n++"/SmallCheck")
                           (\d -> fromIntegral.fst.fst <$> runTestWithStats d p)

checkQuick p n = timed $ do
  putStrNow $ printf "Testing %s/QuickCheck.. " n
  r <- QC.quickCheckWithResult (QC.stdArgs {QC.chatty = False}) p
  putStrNow "done!\n"
  return $ case r of
             QC.Success {..} -> Complete numTests
             QC.GaveUp {..}  -> GaveUp numTests

checkMany :: String -> (Int -> IO Int) -> IO [(Int, Double, Outcome)]
checkMany name bench = do
  putStrNow $ printf "Testing %s.. " name
  r <- go 2
  putStrNow "done!\n"
  return r
  where
    go 11 = return []
    go n  = putStrNow (printf "%d " n) >> timed (myTimeout (bench n)) >>= \case
              (d,Nothing) -> return [(n,d,TimeOut)]
              (d,Just i)  -> ((n,d, Complete i):) <$> go (n+1)


putStrNow s = putStr s >> hFlush stdout

runTestWithStats :: SC.Testable IO a => SC.Depth -> a
                 -> IO ((Integer,Integer), Maybe SC.PropertyFailure)
runTestWithStats d prop = do
  good <- newIORef 0
  bad <- newIORef 0

  let
    hook SC.GoodTest = modifyIORef' good (+1)
    hook SC.BadTest  = modifyIORef' bad  (+1)

  r <- SC.smallCheckWithHook d hook prop

  goodN <- readIORef good
  badN  <- readIORef bad

  return ((goodN, badN), r)
