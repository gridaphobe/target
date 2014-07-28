{-# LANGUAGE LambdaCase #-}
module Main where

import qualified $module$

import Control.Applicative
import Control.Monad
import Data.Time.Clock.POSIX
import System.IO
import System.Timeout
import Text.Printf

import Language.Haskell.Liquid.Types (GhcSpec)
import Test.LiquidCheck
import Test.LiquidCheck.Gen
import Test.LiquidCheck.Util

main :: IO ()
main = do
  spec <- getSpec "$file$"
  putStrLn ("$fun$" ++ ": ")
  withFile "_results/$fun$.tsv" WriteMode $ \h -> do
    hPutStrLn h "Depth\tTime(s)\tResult"
    checkMany spec h
  putStrLn "done"
  putStrLn ""

checkMany :: GhcSpec -> Handle -> IO [(Int, Double, Outcome)]
checkMany spec h = go 2
  where
    go 10     = return []
    go n      = checkAt n >>= \case
                  (d,Nothing) -> do let s = printf "%d\t%.2f\t%s" n d (show TimedOut)
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    return [(n,d,TimedOut)]
                  --NOTE: ignore counter-examples for the sake of exploring coverage
                  --(d,Just (Failed s)) -> return [(n,d,Completed (Failed s))]
                  (d,Just r)  -> do let s = printf "%d\t%.2f\t%s" n d (show (Completed r))
                                    putStrLn s >> hFlush stdout
                                    hPutStrLn h s >> hFlush h
                                    ((n,d,Completed r):) <$> go (n+1)
    checkAt n = timed $ timeout time $ runGen spec "$file$" $ testFun ($fun$ :: $type$) "$fun$" n

time = $timeout$ * 60 * 1000000

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

timed x = do start <- getTime
             v     <- x
             end   <- getTime
             return (end-start, v)

putStrNow s = putStr s >> hFlush stdout

data Outcome = Completed Result
             | TimedOut
             deriving (Show)
