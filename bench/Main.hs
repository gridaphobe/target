{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Main where

import           Test.Target
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

-- import qualified Expr
-- import qualified ExprBench                  as Expr
import qualified List
import qualified ListBench                  as List
import qualified Map                        as Map
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
  = [ namedRecord [ "Depth" .= bshow d
                  , "Target" .= uncurry toResult (lookup3 d l)
                  , "SmallCheck" .= uncurry toResult (lookup3 d s)
                  , "Lazy-SmallCheck" .= uncurry toResult (lookup3 d ls)
                  ]
      <> maybe (namedRecord []) (\ss ->
          namedRecord [ "Lazy-SmallCheck-slow" .= uncurry toResult (lookup3 d ss)])
         lss
    | d <- [2..20]
    ]
  -- = [ namedRecord $ [ "Tool"      .= B8.pack "Target" ]
  --                ++ [ bshow d .= toResult t o | d <- [2..20], let (t,o) = lookup3 d l ]
  --   , namedRecord $ [ "Tool"      .= B8.pack "SmallCheck" ]
  --                ++ [ bshow d .= toResult t o | d <- [2..20], let (t,o) = lookup3 d s ]
  --   , namedRecord $ [ "Tool"      .= B8.pack "Lazy-SmallCheck" ]
  --                ++ [ bshow d .= toResult t o | d <- [2..20], let (t,o) = lookup3 d ls ]
  --   ]
  --  ++ maybe [] (\ss ->
  --   [ namedRecord $ [ "Tool"      .= B8.pack "Lazy-SmallCheck-slow" ]
  --                ++ [ bshow d .= toResult t o | d <- [2..20], let (t,o) = lookup3 d ss ]
  --   ]) lss

bshow :: Show a => a -> B.ByteString
bshow = B8.pack . show

lookup3 :: Int -> [(Int,Double,Outcome)] -> (Double,Outcome)
lookup3 x xs = case L.find (\(a,b,c) -> a == x) xs of
                 Nothing -> (0, TimeOut)
                 Just (i,d,o) -> (d,o)

toResult :: Double -> Outcome -> B.ByteString
toResult d TimeOut      = "nan"
toResult d (Complete i) = bshow d

-- header :: V.Vector B.ByteString
-- header = V.fromList $ ["Tool"] ++ [bshow d | d <- [2..20]]
header (TestResult name l s ls lss _)
  = V.fromList $ [ "Depth", "Target", "SmallCheck", "Lazy-SmallCheck"]
              ++ maybe [] (const ["Lazy-SmallCheck-slow"]) lss

logCsv f r = withFile f WriteMode $ \h -> do
  LB.hPutStr h $ encodeByName (header r) $ testResultRecords r
  return r

main :: IO ()
main = do
  print =<< logCsv "bench/List.insert.csv"       =<< listInsertTests
  print =<< logCsv "bench/RBTree.add.csv"        =<< rbTreeAddTests
  -- print =<< logCsv "bench/Expr.subst.csv"        =<< exprSubstTests
  print =<< logCsv "bench/Map.delete.csv"        =<< mapDeleteTests
  print =<< logCsv "bench/Map.difference.csv"    =<< mapDifferenceTests
  print =<< logCsv "bench/XMonad.focus_left.csv" =<< xmonadFocusLeftTests

listInsertTests = do
  let n = 'List.insert
  l <- checkTarget List.insert         n "examples/List.hs"
  s <- checkSmall  List.prop_insert_sc n
  ls <- checkLazySmall  List.prop_insert_lsc n
  q <- checkQuick  List.prop_insert_qc n
  return $ TestResult (show n) l s ls Nothing q

rbTreeAddTests = do
  let n = 'RBTree.add
  l <- checkTarget RBTree.prop_add_lc n "examples/RBTree.hs"
  s <- checkSmall  RBTree.prop_add_sc n
  ls <- checkLazySmall  RBTree.prop_add_lsc n
  lss <- checkLazySmall  RBTree.prop_add_lsc_slow n
  q <- checkQuick  RBTree.prop_add_qc n
  return $ TestResult (show n) l s ls (Just lss) q

-- exprSubstTests = do
--   l <- checkTarget Expr.subst         "Expr.subst" "examples/Expr.hs"
--   s <- checkSmall  Expr.prop_subst_sc "Expr.subst"
--   ls <- checkLazySmall  Expr.prop_subst_lsc "Expr.subst"
--   q <- checkQuick  Expr.prop_subst_qc "Expr.subst"
--   return $ TestResult "Expr.subst" l s ls Nothing q

mapDeleteTests = do
  let n = 'Map.delete
  l <- checkTarget Map.prop_delete_lc n "examples/Map.hs"
  s <- checkSmall  Map.prop_delete_sc n
  ls <- checkLazySmall  Map.prop_delete_lsc n
  lss <- checkLazySmall  Map.prop_delete_lsc_slow n
  q <- checkQuick  Map.prop_delete_qc n
  return $ TestResult (show n) l s ls (Just lss) q

mapDifferenceTests = do
  let n = 'Map.difference
  l <- checkTarget Map.prop_difference_lc n "examples/Map.hs"
  s <- checkSmall  Map.prop_difference_sc n
  ls <- checkLazySmall  Map.prop_difference_lsc n
  lss <- checkLazySmall  Map.prop_difference_lsc_slow n
  q <- checkQuick  Map.prop_difference_qc n
  return $ TestResult (show n) l s ls (Just lss) q

xmonadFocusLeftTests = do
  let n = 'XMonad.prop_focus_left_master_lc
  l <- checkTarget XMonad.prop_focus_left_master_lc n "examples/XMonad/Properties.hs"
  s <- checkSmall  XMonad.prop_focus_left_master_sc n
  ls <- checkLazySmall  XMonad.prop_focus_left_master_lsc n
  q <- checkQuick  XMonad.prop_focus_left_master_qc n
  return $ TestResult (show n) l s ls Nothing q


myTimeout :: IO a -> IO (Maybe a)
myTimeout = timeout (60 # Minute)

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

resultPassed (Passed i) = i

-- checkTarget :: CanTest f => f -> String -> FilePath -> IO [(Int,Double,Outcome)]
checkTarget f n m = checkMany (show n++"/Target")
                              (\d max -> resultPassed <$>
                                         targetResultWith f (show n) m (mkOpts d max))
  where mkOpts d max = defaultOpts { logging = False, depth = d, maxSuccess = Just max, scDepth = True }

checkSmall p n = checkMany (show n++"/SmallCheck")
                           (\d n -> fromIntegral.fst.fst <$> runTestWithStats d n (p d))

checkLazySmall p n = checkMany (show n++"/LazySmallCheck")
                               (\d n -> LSC.depthCheckResult d n (p d))

-- checkQuick :: QC.Testable f => f -> String -> IO (Double,Outcome)
checkQuick p n = timed $ do
  putStrNow $ printf "Testing %s/QuickCheck.. " (show n)
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
      = putStrNow (printf "%d " n) >> timed (myTimeout (bench n 1000)) >>= \case
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
