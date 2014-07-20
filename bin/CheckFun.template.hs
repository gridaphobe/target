{-# LANGUAGE LambdaCase #-}
module Main where

import $module$

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
  putStr ("$fun$" ++ ": ")
  rs <- checkMany spec
  putStrLn "done"
  withFile "_results/$fun$.tsv" WriteMode $ \h -> do
    hPutStrLn h "Depth\tTime(s)\tResult"
    forM_ rs $ \(d,t,r) -> do 
      let s = printf "%d\t%.2f\t%s\n" d t (show r)
      putStrLn s
      hPutStrLn h s
  putStrLn ""

checkMany :: GhcSpec -> IO [(Int, Double, Outcome)]
checkMany spec = go 2
  where
    go n      = checkAt n >>= \case
                  (d,Nothing) -> return [(n,d,TimedOut)]
                  (20,Just r) -> return [(n,20,Completed r)]
                  (d,Just (Failed s)) -> return [(n,d,Completed (Failed s))]
                  (d,Just r)  -> ((n,d,Completed r):) <$> go (n+1)
    checkAt n = do putStrNow (printf "%d " n)
                   timed $ timeout twentyMinutes $ runGen spec $ testFun ($fun$ :: $type$) "$fun$" n

twentyMinutes = 20 * 60 * 1000000

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
