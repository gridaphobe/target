{-# LANGUAGE LambdaCase #-}
module Main where

import qualified RBTree

import Control.Applicative
import Control.Monad
import           Control.Concurrent.Async
import           Control.Concurrent.MSem
import Control.Concurrent.Timeout
import Data.Time.Clock.POSIX
import Data.Timeout
import System.Environment
import System.IO
import Text.Printf

import Language.Haskell.Liquid.Types (GhcSpec)
import Test.Target
import Test.Target.Monad

main :: IO ()
main = do
  [t]  <- getArgs
  spec <- getSpec "bench/RBTree.hs"
  withFile ("_results/RBTree"++t++".tsv") WriteMode $ \h -> do
    hPutStrLn h "Function\tDepth\tTime(s)\tResult"
    mapPool 4 (checkMany spec h (read t # Minute)) funs
  putStrLn "done"
  putStrLn ""

mapPool max f xs = do
  sem <- new max
  mapConcurrently (with sem . f) xs

-- checkMany :: GhcSpec -> Handle -> IO [(Int, Double, Outcome)]
checkMany spec h time (T f,sp) = putStrNow (printf "Testing %s..\n" sp) >> go 2
  where
    go 21     = return []
    go n      = checkAt n >>= \case
                  (d,Nothing) -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show TimeOut)
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    return [(n,d,TimeOut)]
                  --NOTE: ignore counter-examples for the sake of exploring coverage
                  --(d,Just (Failed s)) -> return [(n,d,Completed (Failed s))]
                  (d,Just r)  -> do let s = printf "%s\t%d\t%.2f\t%s" sp n d (show (Complete r))
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    ((n,d,Complete r):) <$> go (n+1)
    checkAt n = timed $ timeout time $ runGen spec "bench/RBTree.hs" $ testFunIgnoringFailure f sp n

--time = 5 # Minute

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

funs = [(T ((RBTree.add) :: RBTree.Char-> RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.add")
       ,(T ((RBTree.ins) :: RBTree.Char-> RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.ins")
       ,(T ((RBTree.remove) :: RBTree.Char-> RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.remove")
       ,(T ((RBTree.del) :: RBTree.Char-> RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.del")
       ,(T ((RBTree.append) :: RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char), "RBTree.append")
       ,(T ((RBTree.deleteMin) :: RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.deleteMin")
       ,(T ((RBTree.lbalS) :: RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char), "RBTree.lbalS")
       ,(T ((RBTree.rbalS) :: RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char), "RBTree.rbalS")
       ,(T ((RBTree.lbal) :: RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char), "RBTree.lbal")
       ,(T ((RBTree.rbal) :: RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char-> RBTree.RBTree RBTree.Char), "RBTree.rbal")
       ,(T ((RBTree.makeRed) :: RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.makeRed")
       ,(T ((RBTree.makeBlack) :: RBTree.RBTree RBTree.Char -> RBTree.RBTree RBTree.Char), "RBTree.makeBlack")]
