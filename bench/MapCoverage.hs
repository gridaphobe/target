{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import qualified Map

import           Control.Applicative
import           Control.Concurrent.Async
import           Control.Concurrent.MSem
import           Control.Concurrent.Timeout
import           Control.Monad.Catch
import           Control.Monad
import           Data.Time.Clock.POSIX
import           Data.Timeout
import           System.Environment
import           System.IO
import           Text.Printf

import           Language.Haskell.Liquid.Types (GhcSpec)
import           Test.Target
import           Test.Target.Monad

instance Show (a -> b) where
  show _ = "<function>"

main :: IO ()
main = do
  [t]  <- getArgs
  withFile ("_results/Map-" ++ t ++ ".tsv") WriteMode $ \h -> do
    hPutStrLn h "Function\tDepth\tTime(s)\tResult"
    mapPool 12 (checkMany h (read t # Minute)) funs
  putStrLn "done"
  putStrLn ""

mapPool max f xs = do
  sem <- new max
  mapConcurrently (with sem . f) xs


checkMany :: Handle -> Timeout -> (Test, String) -> IO [(Int, Double, Outcome)]
checkMany h time (f,sp) = putStrNow (printf "Testing %s..\n" sp) >> go 2
  where
    go 21     = return []
    go n      = checkAt f sp n time >>= \case
                  (d,Nothing) -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show TimeOut)
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    return [(n,d,TimeOut)]
                  --NOTE: timeout is a bit unreliable..
                  (d,_) | round d >= time #> Second -> do
                    let s = printf "%s\t%d\t%.2f\t%s" sp n d (show TimeOut)
                    putStrLn s >> hFlush stdout
                    hPutStrLn h s >> hFlush h
                    putStrLn "WARNING: timeout seems to have been ignored..."
                    return [(n,d,TimeOut)]
                  --NOTE: sometimes the timeout causes an error instead of a timeout exn
                  (d,Just (Errored s)) -> return [(n,d,Complete (Errored s))]
                  --NOTE: ignore counter-examples for the sake of exploring coverage
                  --(d,Just (Failed s)) -> return [(n,d,Complete (Failed s))]
                  (d,Just r)  -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show (Complete r))
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    ((n,d,Complete r):) <$> go (n+1)

checkAt :: Test -> String -> Int -> Timeout -> IO (Double, Maybe Result)
checkAt (T f) sp n time = timed $ do
  r <- try $ timeout time $ targetResultWithStr f sp "bench/Map.hs" (defaultOpts {logging=False, keepGoing = True, depth = n})
  case r of
    Left (e :: SomeException) -> return $ Just $ Errored $ show e
    Right r                   -> return r

-- time = 5 # Minute

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

putStrNow s = putStr s >> hFlush stdout

data Outcome = Complete Result
             | TimeOut
             deriving (Show)

funs :: [(Test,String)]
funs = [(T ((Map.!) :: Map.Map Map.Char () -> Map.Char -> ()), "Map.!")
       ,(T ((Map.\\) :: Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.\\\\")
       ,(T ((Map.null) :: Map.Map Map.Char () -> Map.Bool), "Map.null")
       ,(T ((Map.lookup) :: Map.Char -> Map.Map Map.Char () -> Map.Maybe ()), "Map.lookup")
       ,(T ((Map.member) :: Map.Char -> Map.Map Map.Char () -> Map.Bool), "Map.member")
       ,(T ((Map.notMember) :: Map.Char -> Map.Map Map.Char () -> Map.Bool), "Map.notMember")
       ,(T ((Map.findWithDefault) :: () -> Map.Char -> Map.Map Map.Char () -> ()), "Map.findWithDefault")
       ,(T ((Map.lookupLT) :: Map.Char -> Map.Map Map.Char () -> Map.Maybe (Map.Char, ())), "Map.lookupLT")
       ,(T ((Map.lookupGT) :: Map.Char -> Map.Map Map.Char () -> Map.Maybe (Map.Char, ())), "Map.lookupGT")
       ,(T ((Map.lookupLE) :: Map.Char -> Map.Map Map.Char () -> Map.Maybe (Map.Char, ())), "Map.lookupLE")
       ,(T ((Map.lookupGE) :: Map.Char -> Map.Map Map.Char () -> Map.Maybe (Map.Char, ())), "Map.lookupGE")
       ,(T ((Map.singleton) :: Map.Char -> () -> Map.Map Map.Char ()), "Map.singleton")
       ,(T ((Map.insert) :: Map.Char -> () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.insert")
       ,(T ((Map.insertWith) :: (() -> () -> ())-> Map.Char -> () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.insertWith")
       ,(T ((Map.insertWithKey) :: (Map.Char -> () -> () -> ())-> Map.Char -> () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.insertWithKey")
       ,(T ((Map.insertLookupWithKey) :: (Map.Char -> () -> () -> ())-> Map.Char-> ()-> Map.Map Map.Char ()-> (Map.Maybe (), Map.Map Map.Char ())), "Map.insertLookupWithKey")
       ,(T ((Map.delete) :: Map.Char -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.delete")
       ,(T ((Map.adjust) :: (() -> ())-> Map.Char -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.adjust")
       ,(T ((Map.adjustWithKey) :: (Map.Char -> () -> ())-> Map.Char -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.adjustWithKey")
       ,(T ((Map.update) :: (() -> Map.Maybe ())-> Map.Char -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.update")
       ,(T ((Map.updateWithKey) :: (Map.Char -> () -> Map.Maybe ())-> Map.Char -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.updateWithKey")
       ,(T ((Map.updateLookupWithKey) :: (Map.Char -> () -> Map.Maybe ())-> Map.Char-> Map.Map Map.Char ()-> (Map.Maybe (), Map.Map Map.Char ())), "Map.updateLookupWithKey")
       ,(T ((Map.alter) :: (Map.Maybe () -> Map.Maybe ())-> Map.Char -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.alter")
       ,(T ((Map.findIndex) :: Map.Char -> Map.Map Map.Char () -> Map.Int), "Map.findIndex")
       ,(T ((Map.lookupIndex) :: Map.Char -> Map.Map Map.Char () -> Map.Maybe Map.Int), "Map.lookupIndex")
       ,(T ((Map.elemAt) :: Map.Int -> Map.Map Map.Char () -> (Map.Char, ())), "Map.elemAt")
       ,(T ((Map.updateAt) :: (Map.Char -> () -> Map.Maybe ())-> Map.Int -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.updateAt")
       ,(T ((Map.deleteAt) :: Map.Int -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.deleteAt")
       ,(T ((Map.findMin) :: Map.Map Map.Char () -> (Map.Char, ())), "Map.findMin")
       ,(T ((Map.findMax) :: Map.Map Map.Char () -> (Map.Char, ())), "Map.findMax")
       ,(T ((Map.deleteMin) :: Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.deleteMin")
       ,(T ((Map.deleteMax) :: Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.deleteMax")
       ,(T ((Map.updateMin) :: (() -> Map.Maybe ()) -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.updateMin")
       ,(T ((Map.updateMax) :: (() -> Map.Maybe ()) -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.updateMax")
       ,(T ((Map.updateMinWithKey) :: (Map.Char -> () -> Map.Maybe ())-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.updateMinWithKey")
       ,(T ((Map.updateMaxWithKey) :: (Map.Char -> () -> Map.Maybe ())-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.updateMaxWithKey")
       ,(T ((Map.minViewWithKey) :: Map.Map Map.Char ()-> Map.Maybe (Map.Char, (), Map.Map Map.Char ())), "Map.minViewWithKey")
       ,(T ((Map.maxViewWithKey) :: Map.Map Map.Char ()-> Map.Maybe (Map.Char, (), Map.Map Map.Char ())), "Map.maxViewWithKey")
       ,(T ((Map.minView) :: Map.Map Map.Char () -> Map.Maybe ((), Map.Map Map.Char ())), "Map.minView")
       ,(T ((Map.maxView) :: Map.Map Map.Char () -> Map.Maybe ((), Map.Map Map.Char ())), "Map.maxView")
       ,(T ((Map.unions) :: [Map.Map Map.Char ()] -> Map.Map Map.Char ()), "Map.unions")
       ,(T ((Map.unionsWith) :: (() -> () -> ()) -> [Map.Map Map.Char ()] -> Map.Map Map.Char ()), "Map.unionsWith")
       ,(T ((Map.union) :: Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.union")
       ,(T ((Map.unionWith) :: (() -> () -> ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.unionWith")
       ,(T ((Map.unionWithKey) :: (Map.Char -> () -> () -> ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.unionWithKey")
       ,(T ((Map.difference) :: Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.difference")
       ,(T ((Map.differenceWith) :: (() -> () -> Map.Maybe ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.differenceWith")
       ,(T ((Map.differenceWithKey) :: (Map.Char -> () -> () -> Map.Maybe ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.differenceWithKey")
       ,(T ((Map.intersection) :: Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.intersection")
       ,(T ((Map.intersectionWith) :: (() -> () -> ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.intersectionWith")
       ,(T ((Map.intersectionWithKey) :: (Map.Char -> () -> () -> ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.intersectionWithKey")
       ,(T ((Map.mergeWithKey) :: (Map.Char -> () -> () -> Map.Maybe ())-> (Map.MaybeS Map.Char    -> Map.MaybeS Map.Char    -> Map.Map Map.Char ()    -> Map.Map Map.Char ())-> (Map.MaybeS Map.Char    -> Map.MaybeS Map.Char    -> Map.Map Map.Char ()    -> Map.Map Map.Char ())-> Map.Map Map.Char ()-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.mergeWithKey")
       ,(T ((Map.isSubmapOf) :: Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Bool), "Map.isSubmapOf")
       ,(T ((Map.isSubmapOfBy) :: (() -> () -> Map.Bool)-> Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Bool), "Map.isSubmapOfBy")
       ,(T ((Map.isProperSubmapOf) :: Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Bool), "Map.isProperSubmapOf")
       ,(T ((Map.isProperSubmapOfBy) :: (() -> () -> Map.Bool)-> Map.Map Map.Char () -> Map.Map Map.Char () -> Map.Bool), "Map.isProperSubmapOfBy")
       ,(T ((Map.filter) :: (() -> Map.Bool) -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.filter")
       ,(T ((Map.filterWithKey) :: (Map.Char -> () -> Map.Bool)-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.filterWithKey")
       ,(T ((Map.partition) :: (() -> Map.Bool)-> Map.Map Map.Char ()-> (Map.Map Map.Char (), Map.Map Map.Char ())), "Map.partition")
       ,(T ((Map.partitionWithKey) :: (Map.Char -> () -> Map.Bool)-> Map.Map Map.Char ()-> (Map.Map Map.Char (), Map.Map Map.Char ())), "Map.partitionWithKey")
       ,(T ((Map.mapMaybe) :: (() -> Map.Maybe ()) -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.mapMaybe")
       ,(T ((Map.mapMaybeWithKey) :: (Map.Char -> () -> Map.Maybe ())-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.mapMaybeWithKey")
       ,(T ((Map.mapEither) :: (() -> Map.Either () ())-> Map.Map Map.Char ()-> (Map.Map Map.Char (), Map.Map Map.Char ())), "Map.mapEither")
       ,(T ((Map.mapEitherWithKey) :: (Map.Char -> () -> Map.Either () ())-> Map.Map Map.Char ()-> (Map.Map Map.Char (), Map.Map Map.Char ())), "Map.mapEitherWithKey")
       ,(T ((Map.map) :: (() -> ()) -> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.map")
       ,(T ((Map.mapWithKey) :: (Map.Char -> () -> ())-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.mapWithKey")
       ,(T ((Map.mapAccum) :: (() -> () -> ((), ()))-> () -> Map.Map Map.Char () -> ((), Map.Map Map.Char ())), "Map.mapAccum")
       ,(T ((Map.mapAccumWithKey) :: (() -> Map.Char -> () -> ((), ()))-> () -> Map.Map Map.Char () -> ((), Map.Map Map.Char ())), "Map.mapAccumWithKey")
       ,(T ((Map.mapAccumRWithKey) :: (() -> Map.Char -> () -> ((), ()))-> () -> Map.Map Map.Char () -> ((), Map.Map Map.Char ())), "Map.mapAccumRWithKey")
       ,(T ((Map.mapKeys) :: (Map.Char -> Map.Char)-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.mapKeys")
       ,(T ((Map.mapKeysWith) :: (() -> () -> ())-> (Map.Char -> Map.Char)-> Map.Map Map.Char ()-> Map.Map Map.Char ()), "Map.mapKeysWith")
       ,(T ((Map.mapKeysMonotonic) :: (Map.Char -> Map.Char)-> Map.Map Map.Char () -> Map.Map Map.Char ()), "Map.mapKeysMonotonic")
       ,(T ((Map.foldr) :: (() -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldr")
       ,(T ((Map.foldr') :: (() -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldr'")
       ,(T ((Map.foldl) :: (() -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldl")
       ,(T ((Map.foldl') :: (() -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldl'")
       ,(T ((Map.foldrWithKey) :: (Map.Char -> () -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldrWithKey")
       ,(T ((Map.foldrWithKey') :: (Map.Char -> () -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldrWithKey'")
       ,(T ((Map.foldlWithKey) :: (() -> Map.Char -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldlWithKey")
       ,(T ((Map.foldlWithKey') :: (() -> Map.Char -> () -> ()) -> () -> Map.Map Map.Char () -> ()), "Map.foldlWithKey'")
       ,(T ((Map.elems) :: Map.Map Map.Char () -> [()]), "Map.elems")
       ,(T ((Map.keys) :: Map.Map Map.Char () -> [Map.Char]), "Map.keys")
       ,(T ((Map.assocs) :: Map.Map Map.Char () -> [(Map.Char, ())]), "Map.assocs")
       ,(T ((Map.fromList) :: [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromList")
       ,(T ((Map.fromListWith) :: (() -> () -> ()) -> [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromListWith")
       ,(T ((Map.fromListWithKey) :: (Map.Char -> () -> () -> ())-> [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromListWithKey")
       ,(T ((Map.toList) :: Map.Map Map.Char () -> [(Map.Char, ())]), "Map.toList")
       ,(T ((Map.toAscList) :: Map.Map Map.Char () -> [(Map.Char, ())]), "Map.toAscList")
       ,(T ((Map.toDescList) :: Map.Map Map.Char () -> [(Map.Char, ())]), "Map.toDescList")
       ,(T ((Map.fromAscList) :: [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromAscList")
       ,(T ((Map.fromAscListWith) :: (() -> () -> ()) -> [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromAscListWith")
       ,(T ((Map.fromAscListWithKey) :: (Map.Char -> () -> () -> ())-> [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromAscListWithKey")
       ,(T ((Map.fromDistinctAscList) :: [(Map.Char, ())] -> Map.Map Map.Char ()), "Map.fromDistinctAscList")
       ,(T ((Map.split) :: Map.Char-> Map.Map Map.Char ()-> (Map.Map Map.Char (), Map.Map Map.Char ())), "Map.split")
       ,(T ((Map.splitLookup) :: Map.Char-> Map.Map Map.Char ()-> (Map.Map Map.Char (), Map.Maybe (), Map.Map Map.Char ())), "Map.splitLookup")
       --,(T ((Map.deleteFindMin) :: Map.Map Map.Char () -> (Map.Char, (), Map.Map Map.Char ())), "Map.deleteFindMin")
       --,(T ((Map.deleteFindMax) :: Map.Map Map.Char () -> (Map.Char, (), Map.Map Map.Char ())), "Map.deleteFindMax")
       ]
