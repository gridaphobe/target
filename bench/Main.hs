{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Main where

import           Test.LiquidCheck
import           Test.LiquidCheck.Types
import qualified Test.QuickCheck            as QC
import qualified Test.SmallCheck            as SC
import qualified Test.SmallCheck.Drivers    as SC

import           Control.Applicative
import           Control.Concurrent.Timeout
import           Control.Exception
import           Control.Monad
import qualified Data.ByteString            as B
import qualified Data.ByteString.Char8      as B8
import qualified Data.ByteString.Lazy       as LB
import           Data.Csv
import qualified Data.List                  as L
import           Data.IORef
import           Data.Monoid
import           Data.Time.Clock.POSIX
import           Data.Timeout
import qualified Data.Vector                as V
import           System.IO
import           Text.Printf

import qualified Expr
import qualified ExprBench                  as Expr
import qualified List
import qualified ListBench                  as List
import qualified MapBench                   as Map
import qualified RBTree
import qualified RBTreeBench                as RBTree
import qualified XMonad.Properties          as XMonad

import qualified LazySmallCheck             as LSC

data Outcome = TimeOut
             | Complete !Int
             | GaveUp !Int
             deriving (Read, Show)

data TestResult
  = TestResult { testName :: !String
               , liquid :: ![(Int,Double,Outcome)]
               , small  :: ![(Int,Double,Outcome)]
               , lazysmall  :: ![(Int,Double,Outcome)]
               , lazysmall_slow :: !(Maybe [(Int,Double,Outcome)])
               , quick  :: !(Double,Outcome)
               } deriving (Read, Show)

testResultRecords :: TestResult -> [NamedRecord]
testResultRecords (TestResult name l s ls lss _)
  = [ namedRecord $ [ "Benchmark" .= B8.pack name
                    , "Tool"      .= B8.pack "Target" ]
                 ++ [ bshow d .= toResult t o | d <- [2..10], let (t,o) = lookup3 d l ]
    , namedRecord $ [ "Benchmark" .= B8.pack name
                    , "Tool"      .= B8.pack "SmallCheck" ]
                 ++ [ bshow d .= toResult t o | d <- [2..10], let (t,o) = lookup3 d s ]
    , namedRecord $ [ "Benchmark" .= B8.pack name
                    , "Tool"      .= B8.pack "Lazy-SmallCheck" ]
                 ++ [ bshow d .= toResult t o | d <- [2..10], let (t,o) = lookup3 d ls ]
    ]
   ++ maybe [] (\ss ->
    [ namedRecord $ [ "Benchmark" .= B8.pack name
                    , "Tool"      .= B8.pack "Lazy-SmallCheck-slow" ]
                 ++ [ bshow d .= toResult t o | d <- [2..10], let (t,o) = lookup3 d ss ]
    ]) lss

bshow :: Show a => a -> B.ByteString
bshow = B8.pack . show

lookup3 :: Int -> [(Int,Double,Outcome)] -> (Double,Outcome)
lookup3 x xs = case L.find (\(a,b,c) -> a == x) xs of
                 Nothing -> (0, TimeOut)
                 Just (i,d,o) -> (d,o)

toResult :: Double -> Outcome -> B.ByteString
toResult d TimeOut      = "X"
toResult d (Complete i) = bshow d

header :: V.Vector B.ByteString
header = V.fromList $ ["Benchmark", "Tool"] ++ [bshow d | d <- [2..10]]

logCsv f r = withFile f WriteMode $ \h -> do
  LB.hPutStr h $ encodeByName header $ testResultRecords r
  return r

main :: IO ()
main = do
  print =<< logCsv "bench/List.insert.csv"       =<< listInsertTests
  print =<< logCsv "bench/RBTree.add.csv"        =<< rbTreeAddTests
  print =<< logCsv "bench/Expr.subst.csv"        =<< exprSubstTests
  print =<< logCsv "bench/Map.delete.csv"        =<< mapDeleteTests
  print =<< logCsv "bench/Map.difference.csv"    =<< mapDifferenceTests
  print =<< logCsv "bench/XMonad.focus_left.csv" =<< xmonadFocusLeftTests

listInsertTests = do
  l <- checkLiquid List.insert         "List.insert" "examples/List.hs"
  s <- checkSmall  List.prop_insert_sc "List.insert"
  ls <- checkLazySmall  List.prop_insert_lsc "List.insert"
  q <- checkQuick  List.prop_insert_qc "List.insert"
  return $ TestResult "List.insert" l s ls Nothing q

rbTreeAddTests = do
  l <- checkLiquid RBTree.prop_add_lc "RBTree.add" "examples/RBTree.hs"
  s <- checkSmall  RBTree.prop_add_sc "RBTree.add"
  ls <- checkLazySmall  RBTree.prop_add_lsc "RBTree.add"
  lss <- checkLazySmall  RBTree.prop_add_lsc_slow "RBTree.add"
  q <- checkQuick  RBTree.prop_add_qc "RBTree.add"
  return $ TestResult "RBTree.add" l s ls (Just lss) q

exprSubstTests = do
  l <- checkLiquid Expr.subst         "Expr.subst" "examples/Expr.hs"
  s <- checkSmall  Expr.prop_subst_sc "Expr.subst"
  ls <- checkLazySmall  Expr.prop_subst_lsc "Expr.subst"
  q <- checkQuick  Expr.prop_subst_qc "Expr.subst"
  return $ TestResult "Expr.subst" l s ls Nothing q

mapDeleteTests = do
  l <- checkLiquid Map.prop_delete_lc "Map.delete" "examples/Map.hs"
  s <- checkSmall  Map.prop_delete_sc "Map.delete"
  ls <- checkLazySmall  Map.prop_delete_lsc "Map.delete"
  lss <- checkLazySmall  Map.prop_delete_lsc_slow "Map.delete"
  q <- checkQuick  Map.prop_delete_qc "Map.delete"
  return $ TestResult "Map.delete" l s ls (Just lss) q

mapDifferenceTests = do
  l <- checkLiquid Map.prop_difference_lc "Map.difference" "examples/Map.hs"
  s <- checkSmall  Map.prop_difference_sc "Map.difference"
  ls <- checkLazySmall  Map.prop_difference_lsc "Map.difference"
  lss <- checkLazySmall  Map.prop_difference_lsc_slow "Map.difference"
  q <- checkQuick  Map.prop_difference_qc "Map.difference"
  return $ TestResult "Map.difference" l s ls (Just lss) q

xmonadFocusLeftTests = do
  l <- checkLiquid XMonad.prop_focus_left_master_lc "XMonad.Properties.prop_focus_left_master_lc"
                                                    "examples/XMonad/Properties.hs"
  s <- checkSmall  XMonad.prop_focus_left_master_sc "XMonad.Properties.prop_focus_left_master"
  ls <- checkLazySmall  XMonad.prop_focus_left_master_lsc "XMonad.Properties.prop_focus_left_master"
  q <- checkQuick  XMonad.prop_focus_left_master_qc "XMonad.Properties.prop_focus_left_master"
  return $ TestResult "XMonad.focus_left_master" l s ls Nothing q


myTimeout :: IO a -> IO (Maybe a)
myTimeout = timeout (5 # Minute)

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

-- checkLiquid :: CanTest f => f -> String -> FilePath -> IO [(Int,Double,Outcome)]
checkLiquid f n m = checkMany (n++"/LiquidCheck")
                              (\d max -> resultPassed <$> testOneMax f n d max m)

checkSmall p n = checkMany (n++"/SmallCheck")
                           (\d n -> fromIntegral.fst.fst <$> runTestWithStats d n p)

checkLazySmall p n = checkMany (n++"/LazySmallCheck")
                               (\d n -> LSC.depthCheckResult d n (p d))

checkQuick :: QC.Testable f => f -> String -> IO (Double,Outcome)
checkQuick p n = timed $ do
  putStrNow $ printf "Testing %s/QuickCheck.. " n
  r <- QC.quickCheckWithResult (QC.stdArgs {QC.chatty = False}) p
  putStrNow "done!\n"
  return $ case r of
             QC.Success {..} -> Complete numTests
             QC.GaveUp {..}  -> GaveUp numTests

checkMany :: String -> (Int -> Int -> IO Int) -> IO [(Int, Double, Outcome)]
checkMany name bench = do
  putStrNow $ printf "Testing %s.. " name
  r <- go 2
  putStrNow "done!\n"
  return r
  where
    go n  
      | n > 20
      = return []
      | otherwise
      = putStrNow (printf "%d " n) >> timed (myTimeout (bench n 2000)) >>= \case
              (d,Nothing) -> return [(n,d,TimeOut)]
              (d,Just i)  -> ((n,d,Complete i):) <$> go (n+1)


putStrNow s = putStr s >> hFlush stdout

runTestWithStats :: SC.Testable IO a => SC.Depth -> Int -> a
                 -> IO ((Integer,Integer), Maybe SC.PropertyFailure)
runTestWithStats d n prop = do
  good <- newIORef 0
  bad <- newIORef 0

  let
    hook SC.GoodTest = do modifyIORef' good (+1)
                          n' <- readIORef good
                          when (n' == fromIntegral n) $ throw ()
    hook SC.BadTest  = modifyIORef' bad (+1)

  r <- SC.smallCheckWithHook d hook prop `catch` \() -> return Nothing

  goodN <- readIORef good
  badN  <- readIORef bad

  return ((goodN, badN), r)

-- instance Exception ()
